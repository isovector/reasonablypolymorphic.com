---
layout: post
title: review2
date: 2026-08-24 23:26
comments: true
tags: foo, bar
---

Last time, we took a stroll down memory lane to review some ancient code I
wrote, and see what/how I'd do things differently now. That was fun, and I have
a new banger for us today.

Today's example comes from the same place --- a little vim-like text editor I
was working on. Vim has this "repeat" operator which just does the same thing
you did last time. It's nice. Delete a word. Running repeat deletes another
word. Kinda dinky in this example, but it can also rerun "increment every number
in the next four paragraphs."

Anyway, so that's the feature I was trying to duplicate. But the action I was
running might have done some IO, and I didn't want to repeat the IO (because
maybe the IO was to gather some input from the user, and repeating shouldn't ask
again.)

I was still [high on my own supply of writing
monads](https://sandymaguire.me/blog/jurisdiction-of-heaven/), so I approached
this problem with a custom monad. The gist of the API was:

```haskell
-- | A monad transformer adding the ability to record the results of IO actions
-- and later replay them.
data Again m a
instance Monad m => Monad (Again m)
instance MonadIO m => MonadIO (Again m)
instance MonadTrans Again

-- | Runs an action and records all of its sampled IO. Returns a action which
-- when invoked will use the recorded IO.
runAgain
    :: Monad m
    => Again m a
    -> m (m a)

-- | Marks an IO action to be memoized after its first invocation.
again
    :: ( MonadIO m
       , Typeable r
       )
    => IO r
    -> Again m r
```

I'm actually pretty impressed with past-me on this one. That's a clean API, and
the implementation was pretty cute.

```haskell
newtype Again m a = Again
  { runAgain' :: RWST () [Dynamic] [Dynamic] m a
  }

once
    :: forall m r
     . ( MonadIO m
       , Typeable r
)
    => IO r
    -> Again m r
once action = do
    a <- dequeue >>= \case
        Just x  -> return . fromJust $ fromDynamic x
        Nothing -> liftIO action
    tell [toDyn a]
    return a
  where
    dequeue :: MonadState [r] m => m (Maybe r)
    dequeue = do
        get >>= \case
            []     -> return Nothing
            (x:xs) -> do
                put xs
                return $ Just x
```

The trick here is to keep `MonadState [Dynamic]` and a `MonadWriter [Dynamic]`
instances around. This code uses the `MonadState` to pop off IO actions it's
already run, and the `MonadWriter` to keep track of new IO actions it needs to
cache. The "magic" happens in `runAgain`, which runs it through once with an
empty state, and then returns a new action with the MonadWriter results moved
into the state for the next time around:

```haskell
runAgain
    :: Monad m
    => Again m a
    -> m (m a)
runAgain action = do
    (a, w) <- evalRWST (runAgain' action) () []
    return $ do
        evalRWST (runAgain' action) () w
        return a
```

Simple. Clean. Elegant. Too bad it doesn't actually work.

The following program crashes with an error coming from the unsafe use of
`fromJust` in `once`:

```haskell
oops :: Again (StateT Bool IO) ()
oops =
  -- Branch on the StateT
  lift get >>= \case
    -- The first time around...
    False -> do
      -- Cache a unit value
      once $ print ()
      -- Change the state value
      lift $ put True

    -- Since the state changed at the end of the first branch, we will take this
    -- branch the second time around...
    True -> do
      -- Calling 'once' the second time around gets its value from the cache,
      -- which has type @()@. But at this callsite, it ought to have type
      -- @Bool -> Bool@. Uh oh!
      f <- once $ pure not
      lift $ print ("uh oh!", f True)


ohNo :: IO ((), Bool)
ohNo = flip runStateT False $ do
  m <- runAgain oops
  m
```

The attack here comes from the fact that we can force the `Again` program down a
different code path its second time around. And that second time, it encounters
a call to `once` which has a different type than the one it cached. Thus,
trying to reuse the cache leads to what is effectively a type error at runtime.

What actually went wrong here? The problem is that
[monads are too powerful](https://chrispenner.ca/posts/expressiveness-spectrum).
Since the only way to compose monads is via bind (`m a -> (a -> m b) -> m b`),
we are forced to extend a monadic value of type `m a` by a *function* of type
`a -> m b`. Which is to say that the "next thing to do" in a monadic computation
is always going to be a function. And functions are completely opaque. So, once
we're given a monad, there's simply no way to know what it's going to do without
actually running the continuation.

The problem arises from the fact that that continuation can invisibly branch.
My `Again` monad was attempting to *statically analyze* the monadic computation,
and cache the IO results in a queue. But as `oops` shows, it's trivial to break
this sort of static analysis. Because the branch is hidden inside of a function,
and there's no way to determine which branches a function *didn't take.*

But I didn't know that eleven years ago, so I give myself a pass on this one.
Nevertheless, let's tackle this problem with the wisdom of ages.


## No More Monads

So if the problem with my previous implementation of `Again` is that it's a
monad, what options do we have? As it happens, there are two very nice options
available to us here: *arrows* and *selective applicative functors.* We'll
discuss arrows for now, and come back to selectives.

Long time readers might remember a
[series on arrows from a few years back.](/tags/yampa.html) But if you don't,
that's OK; you're still welcome here. A quick recap:

Arrows are a generalization of functions. Like functions, they take two type
parameters (an input and an output). Like functions, they come with an identity
arrow. They compose "end to end" just like functions do. These three properties
are expressed as a `Category` superclass, which we usually call `c` and write
infix:

```haskell
class Category (c :: Type -> Type -> Type) where
  id  :: x `c` x
  (.) :: (y `c` z) -> (x `c` y) -> (x `c` z)
```

In addition to being categories, arrows also come with a means of transforming
regular functions into arrows, and of mapping arrows over pairs:

```haskell
class Category c => Arrow c where
  arr :: (x -> y) -> (x `c` y)
  (***) :: (x `c` x') -> (y `c` y') -> ((x, y) `c` (x', y'))
```

What's neat about arrows is that their values are function-like things, rather
than being *actually functions.* That means when we compose arrows, we compose
values whose internals we get to choose. Which in turn, means that static
analysis is possible again!

Attentive readers will notice that there isn't actually any way for
arrows-as-such to be able to branch. To gain that capability, they require an
additional `ArrowChoice`, which equips them with the ability to lift arrows
over `Either`:

```haskell
class Arrow c => ArrowChoice c where
  (+++) :: (x `c` x') -> (y `c` y') -> (Either x y `c` Either x' y')
```

To wet our whistle, let's write a little helper `Arrow` that shows that the
composition of an applicative functor with an arrow is itself an arrow:

```haskell
newtype Static m c x y = Static
  { unStatic :: m (c x y)
  }
```

The arrow instances for `(Applicative m, Arrow c) => Static m c` are the usual
trick of using applicative functions to lift operations into the right place.
For example, identity is just `pure id, and composition is `liftA2` of
composition:

```haskell
instance (Category c, Applicative m) => Category (Static m c) where
  id = Static $ pure id
  Static g . Static f = Static $ liftA2 (.) g f
```

We can do the same trick for `arr` and `(***)`:

```haskell
instance (Arrow c, Applicative m) => Arrow (Static m c) where
  arr = Static . pure . arr
  Static f *** Static g = Static $ liftA2 (***) f g
```

as well as for `(+++)`:

```haskell
instance (ArrowChoice c, Applicative m) => ArrowChoice (Static m c) where
  Static f +++ Static g = Static $ liftA2 (+++) f g
```

What's nice about this `Static` construct we've built is that it gives us two
degrees of freedom. We're free to choose an arrow whose structure we're going to
reuse, and an underlying applicative functor (which can give us "static" effects
as we're *building* the underlying arrow.)

The idea here is that we can put the cache-*building* machinery inside of the
applicative functor, but the cache-*reading* machinery inside of the underlying
arrow.


### Constructing Again, Again

It's worth knowing about the Kleisli arrow:

```haskell
newtype Kleisli m a b = Kleisli
  { runKleisli :: a -> m b
  }

instance Monad m => Category (Kleisli m)
instance Monad m => Arrow (Kleisli m)
instance Monad m => ArrowChoice (Kleisli m)
```

which says that any monadic bind function is itself an arrow. Implementing the
instances yourself is a fun exercise if you're new to this stuff. We can reuse
`Kleisli` as our underlying arrow, which when you expand everything out, we get:

```haskell
newtype Again m a b = Again
  { unAgain :: Static m (Kleisli m) a b
  }
  deriving newtype (Category, Arrow, ArrowChoice)

runAgain :: Monad m => Again m a b -> m (a -> m b)
runAgain = fmap runKleisli . unStatic . unAgain
```

What I think is particularly cool about this is that `runAgain` is just the
composition of the newtype unwrappers, and yet its type is extremely reminiscent
of my ten-year-ago implementation:

```haskell
runAgain  -- the original
    :: Monad m
    => Again m a
    -> m (m a)
```

This is an instance of a more general principle, which is that the final
"observation" you want to make of your type is always a good *representation* of
that type. It's not the only representation, but it's always a reasonable
choice. Appropriately enough, this is known as a *final encoding.*

Anyway. How can we implement `once`? By way of `onceF`:

```haskell
onceF :: (MonadIO m, Ord a) => (a -> IO b) -> Again m a b
onceF m = Again $ Static $ do
  cache <- liftIO $ newIORef mempty
  pure $ Kleisli $ \a -> liftIO $ do
    cacheMap <- readIORef cache
    case M.lookup a cacheMap of
      Just b -> pure b
      Nothing -> do
        b <- m a
        modifyIORef' cache $ M.insert a b
        pure b

once :: MonadIO m => IO b -> Again m a b
once m = arr (const ()) >>> onceF (const m)
```

`onceF` works by constructing a `cache :: IORef (Map a b)` at the `Static`
level. Each call to `onceF` gets a unique cache. Then we drop into the
implementation of the `Kleisli` arrow (which recall happens at *runtime*.)
Inside the `Kleisli`, we check to see if the map has a value at the requested
`a`, and if so, return the cached `b`. If not, we run our function and cache it.

Since there's no `Dynamic` tomfoolery here that is existentializing away our
types, we don't need to worry about the `oops` attack; Haskell's type system
guarantees we can't construct such a thing.

Because `Again` isn't a `Monad`, it can't be a `MonadIO` either. But it's nice
to be able to provide the equivalent of `liftIO`:

```haskell
againF :: MonadIO m => (a -> IO b) -> Again m a b
againF = Again . Static . pure . Kleisli . fmap liftIO

again :: MonadIO m => IO a -> Again m x a
again m = arr (const ()) >>> againF (const m)
```

So that completes our arrow-based implementation of `Again`. But there's still
something left undone.


### Circling Back to Selectives

I said earlier that selective applicative functors would be an alternative
approach to implementing `Again`. Selectives rightfully sit between
`Applicative` and `Monad` in the functor hierarchy, but were
[discovered too late](https://dl.acm.org/doi/10.1145/3341694), and everyone was
still kind of annoyed about having had just stuck `Applicative` into the
hierarchy.

What, precisely is a selective functor? It's a different solution to the problem
of "monads are too powerful" which gives us a branching primitive to play with.
Behold:

```haskell
class Applicative f => Selective f where
  select :: f (Either a b) -> f (a -> b) -> f b
```

`select` says that you might have an `a`, in which case you must run the
provided `f (a -> b)`. But maybe you have a `b`, in which case you *may* run the
effects of the `f (a -> b)`. But nobody's forcing you to.

Since there are still no raw function continuations to be seen here, we can use
`select` to provide branching to our programs. But all of the branches can be
identified statically, since we're only operating on `f` values, again, whose
internals we can control.

In fact, by aggressively nesting `select` calls, you can get back a version of
monadic bind --- so long as you have a finite number of select calls you'd need
to make:

```haskell
bindS
    :: (Selective f, Enum a, Bounded a, Eq a)
    => f a
    -> (a -> f b)
    -> f b
```

(the implementation of which is fun if you're looking for a challenge)

Anyway, all of this is to say that we could have equally structured our `Again`
as a selective functor rather than as an arrow! But `ArrowChoice` is at least as
powerful as `Selective`, so given all of our hard work already, we can pull out
a `Selective` instance for free.

What do I mean when I say "at least as powerful?" It means we can derive it for
free, given an `ArrowChoice` instance. Behold, the `GenericArrow` newtype, which
exists only for us to have something to attach some instances to.

```haskell
newtype GenericArrow c x a = GenericArrow
  { unGenericArrow :: c x a
  }
  deriving newtype (Category, Arrow, ArrowChoice)
```

Here we use newtype deriving to say that if `c` is a category/arrow/arrowchoice,
then `GenericArrow c` is too. But now we can show that having `Arrow` is enough
to get `Functor` and `Applicative` instance:

```haskell
instance Arrow c => Functor (GenericArrow c x) where
  fmap f c = arr f . c

instance Arrow c => Applicative (GenericArrow c x) where
  pure = arr . const
  liftA2 f x y = (x &&& y) >>> arr (uncurry f)
```

Then, given an `ArrowChoice`, we can get an implementation of `select`:

```haskell
instance ArrowChoice c => Selective (GenericArrow c x) where
  select te tk = proc b -> do
    e <- te -< b
    case e of
      Left x -> do
        k <- tk -< b
        returnA -< k x
      Right y -> returnA -< y
```

Here we don't have the option of choosing to invoke `tk` in the `Right` case.
But that's OK, because in `Again`, doing so would correspond to creating caches
for branches that don't need it.

Given all of this, we can now derive `Functor` up to `Selective` for `Again`:

```haskell
newtype Again m a b = Again
  { unAgain :: Static m (Kleisli m) a b
  }
  deriving newtype (Category, Arrow, ArrowChoice)
  deriving (Functor, Applicative, Selective) via GenericArrow (Again m) a
```

which means that users can now choose between the arrow hierarchy and the
functor hierarchy for how they'd like to think about building `Again` actions.
And to nudge them even a little further, we can introduce something that looks
like a monad transformer, removing the input parameter:

```haskell
type AgainT m = Again m ()

runAgainT :: Monad m => AgainT m a -> m (m a)
runAgainT = fmap ($ ()) . runAgain
```

Clean. Tidy. Actually works this time around.

