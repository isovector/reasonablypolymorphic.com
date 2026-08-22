---
layout: post
title: Code-Reviewing My First Monad Implementation
date: 2026-08-21 23:50
comments: true
tags: code-review, haskell, monad
---

I've been wanting to get back into the habit of blogging, and thought a fun
project would be to go back through my old code and review it as the programmer
I am now. So let's do that.


Eleven years ago, I was so proud to written my first monad that I typed up a big
ol[blog post about it.](https://sandymaguire.me/blog/jurisdiction-of-heaven/)
This seems like a fun thing to revisit, so let's do it.

To save you the trouble of reading that ancient-ass blog post, here's the gist.
Given a big piece of state, that has many smaller stateful subcomponents, for
example, a `World` is full of `Buffer`s:

```haskell
data World = World
  { wBuffers :: [Buffer]
  , wCurrent :: Int
  , wMode    :: Mode
  }

data Buffer = Buffer
  { bFilename :: FilePath
  , bContent  :: String
  }
```

my monad acted like `StateT` except that you can restrict the piece of the state
you're allowed to manipulate *without losing the ability to look at the rest of
the state.*

In the blog post, this monad is called `Jurisdiction`, but at some point in the
[source code](https://github.com/isovector/eden) it got renamed to
[`JailT`](https://github.com/isovector/eden/blob/master/src/Control/Monad/Jail.hs).
Cool name. Furthermore, the implementation changed rather dramatically from the
blog post, so let's chase the implementation as given. I'll reproduce it here:

```haskell
type RLens r s = Lens s s r r

newtype JailT s r m a =
    JailT
    { runJailT' :: Bool
                -> RLens r s
                -> s
                -> m (a, s, RLens r s, Bool) }
    deriving (Functor, Typeable)

instance (Applicative m, Monad m) => Applicative (JailT s r m) where
    pure x = JailT $ \v l s -> pure (x, s, l, v)
    (<*>)  = ap

instance (Applicative m, Monad m) => Monad (JailT s r m) where
    return   = pure
    ac >>= k = JailT $ \v l s ->
        if v
            then do
                (x, st', l', v') <- runJailT' ac v l s
                runJailT' (k x) v' l' st'
            else return (undefined, s, l, v)
```

Already there's a lot to look at. The most immediate thing that strikes me is
the formatting; now I'm very much a "use two spaces for indent" kind of guy ---
Haskell doesn't provide many opportunities for natural linebreaks, and our
horizontal space is much more limited than our vertical space. So don't throw
away your horizontal budget on initial spacing. It's minor, but being an artisan
means caring about the minor details.

```haskell
newtype JailT s r m a = JailT
  { runJailT'
      :: Bool
      -> RLens r s
      -> s
      -> m (a, s, RLens r s, Bool)
  }
  deriving (Functor, Typeable)
```

Much nicer.

The other exciting thing to see in the earlier snippet is that this code comes
from before the Functor-Applicative-Monad transition. Which is to say that it's
from the long long ago before `Applicative` was a superclass on `Monad`. There's
some history for you.

And then there is the elephant in the room. Whatever this `Bool` is being passed
around by `runJailT'`, the `Monad` instance branches on it and returns
`undefined` when it's `False`. What the hell is that???? Digging into the
`MonadPlus` instance provides some insight:

```haskell
instance (Applicative m, Monad m) => MonadPlus (JailT s r m) where
    mplus x y = JailT $ \v l s -> do
        x'@(xa, xs, xl, v') <- runJailT' x v l s
        if v'
           then return x'
           else runJailT' y v l s
    mzero = JailT $ \v l s -> return (undefined, s, l, False)
```

So `mzero` returns `undefined` and some `False` value, presumably which is there
to try to warn someone that there's an `undefined` floating around.

*This is a stupid design.* If you're ever in the business of needing to store
data-which-might-not-be-valid and a separate tag stating whether or not it's
valid, a much better design here would be to just use `Maybe a` instead of `(a,
Bool)`.

In fact, perhaps I realized this later on, because `runJailT` does exactly this
logic:

```haskell
runJailT :: (Functor m)
         => JailT s s m a
         -> s
         -> m (Maybe (a, s))
runJailT ac = fmap (\(a, s, _, v) ->
                            if v then Just (a, s) else Nothing)
                    . runJailT' ac True id
```

Let's roll back a bit. The pivotal primitive of `JailT` is the aptly-named
`jail`:

```haskell
jail :: (Monad m)
     => RLens r' r
     -> JailT s r' m a
     -> JailT s r m a
jail l' m = JailT $ \v l s -> do
    (a, s', _, v') <- runJailT' m v (l . l') s
    return (a, s', l, v')
```

Pretty reasonable definition here. I'm not sure what the idea behind `RLens`
being a flipped version of `Lens'` was for. The only odd choice here is that in
the big tuple returned in `jail`, `l` gets passed along unchanged. We can tell
from looking at it that `l` here is the current lens we're looking at.  But
`jail` is the only primitive that changes the lens, and it takes a `JailT` as an
argument. Which is all to say that there isn't anything actually stateful going
on with the `RLens`. So without looking any further, I'd bet dollars to donuts
that this `l` getting returned is purely vestigial and serves absolutely no
purpose. Which in turn means we should be able to chop it out of the definition
of `JailT`.

Speaking of stupid anti-patterns, here's another one:

```haskell
into :: RLens a (Maybe a)
into = lens fromJust (const Just)

jailMaybe :: (Applicative m, Monad m)
          => RLens (Maybe r') r
          -> a
          -> JailT s r' m a
          -> JailT s r m a
jailMaybe l d m =
    (gets $ view l) >>= \case
        Just _  -> jail (l . into) m
        Nothing -> return d
```

This is horrendous for a few reasons. `into` is an unsafe lens that will crash
if you try to read out of a `Nothing`. But then that behavior is guarded in
`jailMaybe` by checking that it isn't already nothing. Stupid.

The last function I want to point out is `parole`:

```haskell
parole :: (Applicative m, Monad m)
       => a
       -> JailT s r m (Maybe a)
       -> JailT s r m a
parole d m = do
    this <- get
    m >>= \case
        Just a  -> return a
        Nothing -> put this >> return d
```

which... does... something. I guess it attempts to run a `Maybe`-valued `JailT`,
and if it fails, unwinds the state and returns some default `a`. Rearing its
ugly head here, however, is the ghost of the `undefined` nonsense from `mzero`.
Note that if we invoke `parole a mzero` we will get a *crash* rather than the
roll-back-and-default behavior that it promises on the tin.

So, all in all, I am not particularly impressed with my first monad. Here's how
I'd write it today.

First, I don't think I've written a "control"-y sort of monad from scratch in
the last five years. Whatever behavior you want is almost always just the
composition of a few monad transformers. In this case, we have a `Reader` for
the current lens, a `State` for the original state, and a `Maybe` to give us
`mzero` semantics.

Since we want our state to roll-back when we take an alternative path, we must
put `MaybeT` *underneath* our `StateT`.[^try-it] This gives us the nice
formulation of a `JailT` as:

[^try-it]: Unwrap the definitions of `StateT s Maybe a` and `MaybeT (State s) a`
           to see why.

```haskell
newtype JailT s r m a = JailT
  { unJailT :: ReaderT (ALens' s r) (StateT s (MaybeT m)) a
  }
```

(we use `ALens' s r` here instead of `Lens' s r` since the latter requires
`-XImpredicativeTypes`. Which happens to be turned on in the original
implementation!)

Once nice thing about defining our monad as a `newtype` over a series of monad
transformers, is that it allows us to newtype-derive all of the relevant
instances:

```
  deriving newtype (Functor, Applicative, Monad, MonadIO, Alternative)
```

No implementation for such things is required, and therefore we know that the
derived instances must be correct. Which means we have many fewer things to
worry about.

I prefer to use `unWhatever` as my naming scheme for these newtypes, so that I
can provide `runWhatever` as a more user-friendly function.

```haskell
runJailT :: s -> Lens' s t -> JailT s t m a -> m (Maybe (a, s))
runJailT s l = runMaybeT . flip runStateT s . flip runReaderT l . unJailT
```

What's also nice about using standard monad transformers for your implementation
is that you can reuse all of their existing combinators. For example, to
implement `jail` all we need to do is invoke `withReaderT :: (r' -> r) ->
ReaderT r m a -> ReaderT r' m a`, which lets us change the type of the reader.

```haskell
jail :: Lens' t u -> JailT s u m a -> JailT s t m a
jail ltu = JailT . withReaderT (\lst -> cloneLens lst . ltu) . unJailT
```

Notice here that I like to minimize my points without going point-free; `jail`
as written is very legible, but writing it entirely pointfree is a crime against
humanity:

```
-- don't do this!
jail = (JailT .) . (. unJailT) . withReaderT . flip ((.) . cloneLens)
```

Rather than implementing `parole` directly, we can note that it is the
composition of two pieces --- (1) attempt something, (2) return a default if it
failed. Whenever you notice de-composition opportunities like this, take them!

We can write `attempt`, which is wildly general and doesn't care one fig about
jails or the legal system:

```haskell
attempt :: (Alternative m, Monad m) => m (Maybe a) -> m a
attempt m = maybe empty pure =<< m
```

and then `parole` is merely


```haskell
parole :: Monad m => a -> JailT s t m (Maybe a) -> JailT s t m a
parole a0 j =
  asum
    [ attempt j
    , pure a0
    ]
```

All in all, significantly nicer if you ask me. [But I'm just a TV. Don't take my
word for it.](https://www.youtube.com/watch?v=NgUGvZkQd0M) Compare for yourself!

<details>
<summary>Original Implementation</summary>

```haskell
{-# LANGUAGE GeneralizedNewtypeDeriving,
             FlexibleInstances, MultiParamTypeClasses,
             DeriveFunctor, ImpredicativeTypes, LambdaCase,
             DeriveDataTypeable #-}

import Control.Applicative (Alternative(..))
import Control.Monad (ap, MonadPlus(..))
import Control.Monad.State
import Control.Lens
import Data.Maybe (fromJust)
import Data.Typeable


type RLens r s = Lens s s r r

newtype JailT s r m a =
    JailT
    { runJailT' :: Bool
                -> RLens r s
                -> s
                -> m (a, s, RLens r s, Bool) }
    deriving (Functor, Typeable)

instance (Applicative m, Monad m) => Applicative (JailT s r m) where
    pure x = JailT $ \v l s -> pure (x, s, l, v)
    (<*>)  = ap

instance (Applicative m, Monad m) => Monad (JailT s r m) where
    return   = pure
    ac >>= k = JailT $ \v l s ->
        if v
            then do
                (x, st', l', v') <- runJailT' ac v l s
                runJailT' (k x) v' l' st'
            else return (undefined, s, l, v)

instance (Applicative m, Monad m) => MonadState r (JailT s r m) where
    get   = JailT $ \v l s -> return (view l s, s, l, v)
    put x = JailT $ \v l s -> return ((), set l x s, l, v)

instance MonadTrans (JailT s r) where
    lift x = JailT $ \v l s -> x >>= (\a -> return (a, s, l, v))

instance (Applicative m, MonadIO m) => MonadIO (JailT s r m) where
    liftIO = lift . liftIO

instance (Applicative m, Monad m) => MonadPlus (JailT s r m) where
    mplus x y = JailT $ \v l s -> do
        x'@(xa, xs, xl, v') <- runJailT' x v l s
        if v'
           then return x'
           else runJailT' y v l s
    mzero = JailT $ \v l s -> return (undefined, s, l, False)

instance (Applicative m, Monad m) => Alternative (JailT s r m) where
    (<|>) = mplus
    empty = mzero

runJailT :: (Functor m)
         => JailT s s m a
         -> s
         -> m (Maybe (a, s))
runJailT ac = fmap (\(a, s, _, v) ->
                            if v then Just (a, s) else Nothing)
                    . runJailT' ac True id

type Jail s r = JailT s r Identity
runJail :: Jail s s a
        -> s
        -> Maybe (a, s)
runJail ac = runIdentity . runJailT ac

jail :: (Monad m)
     => RLens r' r
     -> JailT s r' m a
     -> JailT s r m a
jail l' m = JailT $ \v l s -> do
    (a, s', _, v') <- runJailT' m v (l . l') s
    return (a, s', l, v')

into :: RLens a (Maybe a)
into = lens fromJust (const Just)

jailMaybe :: (Applicative m, Monad m)
          => RLens (Maybe r') r
          -> a
          -> JailT s r' m a
          -> JailT s r m a
jailMaybe l d m =
    (gets $ view l) >>= \case
        Just _  -> jail (l . into) m
        Nothing -> return d

escape :: (Applicative m, Monad m)
       => JailT s s m a
       -> JailT s r m a
escape m = JailT $ \v l s -> do
    (a, s', _, v') <- runJailT' m v id s
    return (a, s', l, v')

freedom :: (Applicative m, Monad m) => JailT s r m s
freedom = JailT $ \v l s -> return (s, s, l, v)

-- happens to be unused, because it's kinda insane??
overwrite :: (Applicative m, Monad m)
          => RLens r' r
          -> JailT r r' m a
          -> JailT s r m a
overwrite l' m = JailT $ \v l s -> do
    (a, s', _, v') <- runJailT' m v l' $ view l s
    return (a, set l s' s, l, v')

parole :: (Applicative m, Monad m)
       => a
       -> JailT s r m (Maybe a)
       -> JailT s r m a
parole d m = do
    this <- get
    m >>= \case
        Just a  -> return a
        Nothing -> put this >> return d

inspect :: (Applicative m, Monad m)
        => RLens i r
        -> JailT s r m i
inspect l = gets $ view l

inquire :: (Applicative m, Monad m)
        => RLens i s
        -> JailT s r m i
inquire l = view l <$> freedom

arrest :: (Applicative m, Monad m)
       => RLens r' r
       -> r'
       -> JailT s r m ()
arrest l v = do
    state <- get
    put $ set l v state

arrests :: (Applicative m, Monad m)
        => RLens r' r
        -> (r' -> r')
        -> JailT s r m ()
arrests l f = do
    state <- get
    put $ set l (f $ view l state) state
```

</details>

vs the

<details>
<summary>New Implementation</summary>

```haskell
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}

import Control.Applicative
import Control.Lens
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Trans.Maybe


newtype JailT s r m a = JailT
  { unJailT :: ReaderT (ALens' s r) (StateT s (MaybeT m)) a
  }
  deriving newtype (Functor, Applicative, Monad, MonadIO, Alternative)

instance Monad m => MonadState r (JailT s r m) where
  get = JailT $ do
    l <- asks cloneLens
    gets $ view l
  put r = JailT $ do
    l <- asks cloneLens
    modify $ set l r

runJailT :: s -> Lens' s t -> JailT s t m a -> m (Maybe (a, s))
runJailT s l = runMaybeT . flip runStateT s . flip runReaderT l . unJailT

jail :: Lens' t u -> JailT s u m a -> JailT s t m a
jail ltu = JailT . withReaderT (\lst -> cloneLens lst . ltu) . unJailT

escape :: JailT s s m a -> JailT s t m a
escape (JailT j) = JailT $ withReaderT (const id) j

freedom :: Monad m => JailT s t m s
freedom = JailT get

attempt :: (Alternative m, Monad m) => m (Maybe a) -> m a
attempt m = maybe empty pure =<< m

parole :: Monad m => a -> JailT s t m (Maybe a) -> JailT s t m a
parole a0 j =
  asum
    [ attempt j
    , pure a0
    ]

arrest :: Monad m => Lens' t u -> u -> JailT s t m ()
arrest l u = modify $ set l u
```

</details>

Maybe this was interesting to you. It certainly was fun for me, because I like
tearing apart bad code, and I don't get to see much of it now that I have very
talented colleagues. Thankfully I have a huge amount of crap code from my past,
including an even more egregious monad that we'll tackle next time around.

