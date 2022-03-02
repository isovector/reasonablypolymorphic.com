---
layout: post
title: Porting to Polysemy
date: 2021-10-02 22:46
comments: true
tags: polysemy, refactoring
---

Many years ago, when I first started using free monads in anger, I was tasked
with porting our giant codebase to something that used an effect system. While
it was a noble goal, my efforts slowly imploded upon their own weight. I didn't
know how to go about doing such a dramatic refactoring on a live codebase, and
unwisely tried to do the whole thing in a single PR. A month later, as you might
expect, it became overwhelming obvious that we were never going to merge the
thing, and it died there.

Several years older (and wiser), I've recently been contracted to port another
codebase to Polysemy. Today we hit our first big milestone, and the experience
has gone swimmingly. I wanted to spend some time today discussing how to
actually go about Polysemizing a codebase. It's not too onerous if you proceed
cautiously. The trick is to do several passes over the codebase, each time
introducing a few more effects, but at no point ever actually changing any code
paths.

## Getting Your Foot in the Door

The first step is to introduce Polysemy into your codebase. Your program is
almost certainly structured around a main application monad, and that's the
right place to start. As a first step, we will swap out `IO` for `Sem`. For
example, if your main monad were:

```haskell
newtype App a = App
  { unApp :: ReaderT Env (ExceptT AppError IO) a
  }
```

we will change it to:

```haskell
newtype App r a = App
  { unApp :: Member (Final IO) r => ReaderT Env (ExceptT AppError (Sem r)) a
  }
```

This change exposes the effect row (the `r` type variable,) and asserts that we
always have a `Final IO` member in that row. Exposing `r` means we can gradually
introduce `Member` constraints in application code as we begin teasing apart
effects, and `Final IO` gives us a way to implement `MonadIO` for `App`. Let's
start with that:

```haskell
instance MonadIO (App r) where
  liftIO a = App $ lift $ lift $ embedFinal a
```

Due to some quirks of how Haskell deals with impredicativity, this function
can't be written point-free.

This change of `App` to `App r` isn't the end-goal; it's *just* enough that we
can get Polysemy into the project without it being a huge change. In the medium
term, our goal is to eliminate the `App` newtype altogether, leaving a bare
`Sem` in its place. But one step at a time.

You'll need to rewrite any instances on `App` that you were previously newtype
deriving. This sucks, but the answer is always just to `lift`. You might find
that some instances used to be derived via `IO`, and thus now cannot be
implemented via `lift`. In these cases, don't be afraid to give an orphan
instance for `Sem r`; orphans are bad, but we'll be cleaning this all up very
soon.

Take some time to get everything compiling. It's a lot of drudgery, but all you
need to do is to add the `r` type variable to every type signature in your
codebase that mentions `App`.

You will also need an introduction function, to lift Polysemy actions into
`App`:

```haskell
liftSem :: Sem r a -> App r a
liftSem a = App $ lift $ lift a
```

as well as an elimination function which will evolve as you add effects. At some
point in your (existing) program, you will need to actually run `App` down to
`IO`. It probably looks something like this:

```haskell
runApp :: Env -> App a -> IO (Either AppError a)
runApp env = runExceptT . flip runReaderT env . unApp
```

instead we are going to create the *canonical* interpretation down to `IO`:

```haskell
type CanonicalEffects =
  '[ Final IO
   ]

canonicalAppToIO :: Env -> App CanonicalEffects a -> IO (Either AppError a)
canonicalAppToIO env
  = runFinal
  . runExceptT
  . flip runReaderT env
  . unApp
```

As we pull effects out of the program, we will add them to `CanonicalEffects`,
and their interpreters to `canonicalAppToIO`. But for now, this function is very
boring.

Once everything is up and compiling, all of the old tests should still pass. We
haven't changed anything, just installed some new machinery. But importantly,
all of code paths are still exactly the same. Remember, this is a refactoring
task! The goal is to do lots of little refactors, each one pulling out some
effect machinery, but not changing any code paths. The entire porting project
should be a series of no-op PRs that slowly carve your codebase into one with
explicitly described effects.


## First Effects

Your medium term goal is to eliminate the `Final IO` constraint inside of `App`,
which exists only to provide a `MonadIO` instance. So, our *real* goal is to
systematically eliminate raw `IO` from `App`.

The usual culprits here are database access, HTTP requests, and logging. If your
team has been disciplined, database access and HTTP requests should already be
relatively isolated from the rest of the codebase. Isolated here means "database
calls are in their own functions," rather than being inlined directly in the
application code whenever it wants to talk to the database. If your database
accesses are not isolated, take some time to uninline them before continuing.

Our next step is to identify CRUD groups on the database. We generously
interpret the "read" in CRUD to be any queries that exist against the logical
datastructure that you're serializing in the database. These CRUD groups might
be organized by table, but they don't necessarily need to be; by table is good
enough for now if it corresponds to how the queries exist today.

For each CRUD group, we want to make a new Polysemy effect, and thread it
through the application, replacing each direct call to the database with a call
to the effect action. Finish working on each effect before starting on the next;
each group makes for a good PR.

For example, maybe we've identified the following database accesses for table
`users`:

```haskell
insertUser       :: MonadDB m => UserName -> User -> m ()
lookupUser       :: MonadDB m => UserName -> m (Maybe User)
getUsersByRegion :: MonadDB m => Region -> m [User]
setUserLapsed    :: MonadDB m => UserName -> m ()
unsetUserLapsed  :: MonadDB m => UserName -> m ()
purgeUser        :: MonadDB m => UserNamr -> m ()
```

This CRUD group corresponds to an effect:

```haskell
module App.Sem.UserStore where

data UserStore m a where
  Insert      :: UserName -> User -> UserStore m ()
  Lookup      :: UserName -> UserStore m (Maybe User)
  GetByRegion :: Region -> UserStore m [User]
  SetLapsed   :: UserName -> UserStore m ()
  UnsetLapsed :: UserName -> UserStore m ()
  Purge       :: UserName -> UserStore m ()

makeSem ''UserStore
```

We can now replace all calls across the codebase to `insertUser a b` with
`liftSem $ UserStore.insert a b`. Doing so will require you to propagate a
`Member UserStore r` constraint throughout the callstack. I really like this
process. It's a bit annoying to push constraints upwards, but it really gives
you a good sense for the hidden complexity in your program. As it turns out,
`MonadIO` is hiding a metric ton of spaghetti code!

All of this replacing and constraint propagating has given you dependency
injection. But remember, at this step we'd like all of our changes to be no-ops,
so we still need to inject the old codepath. For this we will make an
interpreter of the `UserStore` effect:

```haskell
module App.Sem.UserStore.IO where

import qualified TheDatabase as DB
import App.Sem.UserStore

userStoreToDB
    :: forall m r a
     . (Member (Embed m) r, MonadDB m)
    => Sem (UserStore ': r) a
    -> Sem r a
userStoreToDB = interpret $ embed @m . \case
  Insert un u    -> DB.insertUser un u
  Lookup un      -> DB.lookupUser un
  GetByRegion r  -> DB.getUsersByRegion r
  SetLapsed un   -> DB.setUserLapsed un
  UnsetLapsed un -> DB.unsetUserLapsed un
  Purge un       -> DB.purgeUser un
```

Make sure to add `UserStore` (and its dependency, `Embed DB`) to the head of
`CanonicalEffects`:

```haskell
type CanonicalEffects =
  '[ UserStore
   , Embed DB  -- dependency of UserStore
   , Embed IO  -- dependency of Embed DB
   , Final IO
   ]
```

and then we can update the canonical interpreter:

```haskell
canonicalAppToIO :: Env -> App CanonicalEffects a -> IO (Either AppError a)
canonicalAppToIO env
  = runFinal
  . embedToFinal
  . runEmbedded @DB @IO (however you run the DB in IO)
  . userStoreToDB @DB
  . runExceptT
  . flip runReaderT env
  . unApp
```

The general principle here is that you add the new effect somewhere near the top
of the `CanonicalEffects` stack, making sure to add any effects that your
intended interpreter requires lower in the stack. Then, add the new interpreter
to `canonicalAppToIO`, in the same order (but perhaps presented "backwards",
since function application is right to left.) Make sure to add interpreters for
the depended-upon effects too!

As you pull more and more effects out, you'll find that often you'll already
have the depended-upon effects in `CanonicalEffects`. This is a good thing ---
we will probably have several effects that can all be interpreted via `Embed
DB`.

The benefit here is that we have now separated our *application code* from the
particular choice of database implementation. While we want to use
`userStoreToDB` in production, it might make less sense to use in local testing
environments, where we don't want to spin up a database. Instead, we could just
write a little interpreter that emulates the `UserStore` interface purely in
memory! Once you've fully exorcised `IO` from your codebase, this approach gets
extremely powerful.


## Choosing Effects

Carving out your effects is probably the hardest thing to do here. What's
difficult is that you need to forget your instincts! Things that would make a
good MTL-style typeclass are often *terrible* choices for effects.

Why's that? There's this extremely common pattern in the Haskell ecosystem for
libraries that want to expose themselves to arbitrary applications' monad
stacks. To continue with the `MonadDB` example, it's likely something like:

```haskell
class (MonadIO m, MonadThrow m) => MonadDB m where
  liftDB :: DB a -> m a
```

While this works fine for a single underlying implementation, it's an awful
effect for the same reason: there's only one interpretation! Any meaningful
interpreter for `MonadDB` is equivalent to writing your own implementation of
the database! It's the same reason we don't like `IO` --- `IO` is so big that
every possible interpretation of it would necessarily need to be able to talk to
the file system, to the network, to threads, and *everything else* that we can
do in `IO`.

Instead, when you're looking for effects to pull out, you need to *forget
entirely about the implementation,* and just look at the abstract interface.
Don't use an HTTP effect to talk to a REST API --- it's too big, and would
require you to implement an entire HTTP protocol. Instead, just define an effect
that talks to exactly the pieces of the API that you need to talk to. Forget
that it's REST entirely! That's an implementation detail, and implementation
details are the domain of the interpreter, not the effect.

Furthermore, if you're just using the standard `Polysemy` effects, pick the
smallest effect that you can get away with. You'll probably reach for `Reader`
more often than you should. You don't need to use `Reader` unless you need
`local` --- otherwise, prefer `Input`.


## Summing Up

That's all I have for today, but I have a few more posts in mind for this
series. One on how to actually go about testing all of this stuff, and another
on how to follow up the refactoring of your new Polysemy codebase now that all
of the `IO` has been removed.

