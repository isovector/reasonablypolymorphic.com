---
title: "Polysemy: Chasing Performance in Free Monads"
author: Sandy Maguire
patat:
  wrap: true
  margins:
    top: 3
    left: 5
    right: 5
---

# Polysemy

## Chasing Performance in Free Monads

---

* **Sandy Maguire**
* sandy@sandymaguire.me

* reasonablypolymorphic.com
* github.com/isovector


Today's slides:

* reasonablypolymorphic.com/polysemy-talk

---

Our codebase was written by contractors.

Big ball o' IO spaghetti.

Impossible to test.

---

*Free monads* are what I think programming will look like in 30 years.

. . .

Write your applications in *domain specific language* designed for your exact
problem.

. . .

*Run a series of transformations* to compile your high-level specification into
lower-level DSLs.

---

Most programs are easy to describe.

. . .

The majority of a codebase is spent dealing with nitty-gritty details.

. . .

This is where most of the bugs are.

---

Let's turn implementation details into library code!

---

# Example

Data ingestion service that:

* reads encrypted CSV files
* emits them in batches to a streaming HTTP service
* records statistics in Redis

---

```haskell
ingest
    :: ( Member (Input Record) r
       , Member (Output Record) r
       , Member (Output Stat) r
       )
    => Eff r ()
ingest = input >>= \case
  Nothing     -> pure ()
  Just record -> do
    output record
    output ProcessedRecordStat
    ingest
```

---

```haskell
main = ingest

```

> Open Effects:
>
> { Input Record, Output Record, Output Stat }

---

```haskell
main = ingest
     & csvInput "file.csv"

```

> Open Effects:
>
> { FileProvider, Output Record, Output Stat }

---

```haskell
main = ingest
     & csvInput "file.csv"
     & decryptFileProvider
```

> Open Effects:
>
> { FileProvider, Output Record, Output Stat, Encryption }

---

```haskell
main = ingest
     & csvInput "file.csv"
     & decryptFileProvider
     & ftpFileProvider
```

> Open Effects:
>
> { FTP, Output Record, Output Stat, Encryption }

---

```haskell
main = ingest
     & csvInput "file.csv"
     & decryptFileProvider
     & ftpFileProvider
     & batch      @Record 500
```

> Open Effects:
>
> { FTP, Output [Record], Output Stat, Encryption }

---

```haskell
main = ingest
     & csvInput "file.csv"
     & decryptFileProvider
     & ftpFileProvider
     & batch      @Record 500
     & postOutput @Record mkApiCall

```

> Open Effects:
>
> { FTP, HTTP, Output Stat, Encryption }

---

```haskell
main = ingest
     & csvInput "file.csv"
     & decryptFileProvider
     & ftpFileProvider
     & batch      @Record 500
     & postOutput @Record mkApiCall
     & redisOuput @Stat   mkRedisKey
```

> Open Effects:
>
> {FTP, HTTP, Encryption, Redis}

---

```haskell
main = ingest
     & csvInput "file.csv"
     & decryptFileProvider
     & ftpFileProvider
     & batch      @Record 500
     & postOutput @Record mkApiCall
     & redisOuput @Stat   mkRedisKey
     & runEncryption

```

> Open Effects:
>
> { FTP, HTTP, Redis}

---

```haskell
main = ingest
     & csvInput "file.csv"
     & decryptFileProvider
     & ftpFileProvider
     & batch      @Record 500
     & postOutput @Record mkApiCall
     & redisOuput @Stat   mkRedisKey
     & runEncryption
     & runHTTP

```

> Open Effects:
>
> { FTP, Redis }

---

```haskell
main = ingest
     & csvInput "file.csv"
     & decryptFileProvider
     & ftpFileProvider
     & batch      @Record 500
     & postOutput @Record mkApiCall
     & redisOuput @Stat   mkRedisKey
     & runEncryption
     & runHTTP
     & runFTP

```

> Open Effects:
>
> { Redis }

---

```haskell
main = ingest
     & csvInput "file.csv"
     & decryptFileProvider
     & ftpFileProvider
     & batch      @Record 500
     & postOutput @Record mkApiCall
     & redisOuput @Stat   mkRedisKey
     & runEncryption
     & runHTTP
     & runFTP
     & runRedis
```

> Open Effects:
>
> { }

---

```haskell
main = ingest
     & csvInput "file.csv"
     & decryptFileProvider
     & ftpFileProvider
     & batch      @Record 500
     & postOutput @Record mkApiCall
     & redisOuput @Stat   mkRedisKey
     & runEncryption
     & runHTTP
     & runFTP
     & runRedis
     & runM

```

---

But maybe we want to test this without a million mocked services?

. . .

```haskell
test :: ([Stat], ([Record], ()))
test = ingest
     & runInput [record1, record2]
     & runPureOuput @Recor
     & runPureOuput @Stat
     & run
```

---


If both a test and real interpreter are correct,

. . .

And the program is correct under the test,

. . .

Then the program is correct under the real interpreter!

. . .

**Correctness composes!**

----

Two major players in the free monad space:

. . .

## freer-simple

* No boilerplate!
* Friendly to use!
* 35x slower than theoretically possible.
* Incapable of expressing lots of desirable effects.


. . .

## fused-effects

* SO MUCH BOILERPLATE.
* Not very friendly.
* As fast as possible!
* All effects are expressible!

. . .

**Neither of these is a good trade-off!**

----

My new library:

. . .

## polysemy

* No boilerplate!
* Friendly to use!
* As fast as possible!
* All effects are expressible!

. . .

*The best of both worlds!*

----

We'll discuss how this was possible!

. . .

But first, let's get you up to speed on naive free monads.

----


```haskell
data Teletype k
  = Done k
  | WriteLine String (Teletype k)
  | ReadLine (String -> Teletype k)


echo :: Teletype ()
echo = ReadLine $ \msg ->
       WriteLine msg
     $ Done ()
```

. . .


```haskell
instance Monad Teletype where
  return = Done
  Done          k >>= f = f k
  WriteLine msg k >>= f = WriteLine msg $ k >>= f
  ReadLine      k >>= f = ReadLine $ \str -> k str >>= f
```

----

Because it's a monad, we can write this more idiomatically.

```haskell
echo :: Teletype ()
echo = do
  msg <- ReadLine Done
  WriteLine msg $ Done ()
```

----

... and define evaluation semantics for it.

. . .

```haskell
runTeletypeInIO :: Teletype a -> IO a
runTeletypeInIO (Done a) = pure a
```
. . .
```haskell
runTeletypeInIO (WriteLine msg k) = do
  putStrLn msg
  runTeletypeInIO k
```
. . .
```haskell
runTeletypeInIO (ReadLine k) =  do
  msg <- getLine
  runTeletypeInIO $ k msg
```

----


```haskell
runTeletypePurely :: [String] -> Teletype a -> ([String], a)
runTeletypePurely _ (Done a) = ([], a)
```
. . .
```haskell
runTeletypePurely ls (WriteLine msg k) =
  let (rs, a) = runTeletypePurely ls k
   in (msg : rs, a)
```
. . .
```haskell
runTeletypePurely []       (ReadLine k) =
  runTeletypePurely [] $ k ""
```
. . .
```haskell
runTeletypePurely (l : ls) (ReadLine k) =
  runTeletypePurely ls $ k l
```

----

```haskell
data Teletype k
  = Done k
  | WriteLine String (Teletype k)
  | ReadLine (String -> Teletype k)
```

The `Done` constructor and the recursion are only necessary to make this a
`Monad`.

We can factor them out.


---

Before:

```haskell
data Teletype k
  = Done k
  | WriteLine String (Teletype k)
  | ReadLine (String -> Teletype k)
```

After:

```haskell
data Free f k
  = Pure k
  | Impure (f (Free f k))


data Teletype a
  = WriteLine String a
  | ReadLine (String -> a)
```

----

`Free f` is a `Monad` whenever `f` is a `Functor`!

```haskell
instance Functor f => Monad (Free f) where
  return = Pure
  Pure k   >>= f = f k
  Impure z >>= f = Impure $ fmap (\x -> x >>= f) z
```

----

Let's write some helper functions:

```haskell
writeLine :: String -> Free Teletype ()
writeLine msg = Impure $ WriteLine msg $ pure ()

readLine :: Free Teletype String
readLine = Impure $ ReadLine pure
```

. . .

`echo` is no longer conspicuous:

. . .
```haskell
echo :: Free Teletype ()
echo = do
  msg <- readLine
  writeLine msg
```

----

We can also factor out the evaluation plumbing:

```haskell
runFree
    :: Monad m
    => (∀ x. f x -> m x)
    -> Free f a
    -> m a
runFree _ (Pure a)  = pure a
runFree f (Impure k) = f k >>= runFree f
```

. . .

Less boilerplate in our interpretation:

```haskell
runTeletypeInIO :: Free Teletype a -> IO a
runTeletypeInIO = runFree $ \case
  WriteLine msg k -> do
    putStrLn msg
    pure k
  ReadLine k -> do
    msg <- getLine
    pure $ k msg
```

----

# Combining Multiple Effects

```haskell
data Bell k
  = RingBell k
  deriving Functor
```

. . .

```haskell
data Sum f g a
  = L (f a)
  | R (g a)

instance (Functor f, Functor g) => Functor (Sum f g)
```

. . .

```haskell
type TeletypeWithBell = Sum Teletype Bell
```

----

Before:

```haskell
writeLine :: String -> Free Teletype ()
writeLine msg = Impure $ WriteLine msg $ pure ()
```

After:

```haskell
writeLine :: String -> Free TeletypeWithBell ()
writeLine msg = Impure $ L $ WriteLine msg $ pure ()

ringBell :: Free TeletypeWithBell ()
ringBell = Impure $ R $ RingBell $ pure ()
```

----

We can interleave actions from both effects.

```haskell
ringItSingIt :: Free TeletypeWithBell ()
ringItSingIt = do
  msg <- readLine
  when (msg == "ring the bell!") ringBell
```

----

```haskell
interpret
    :: Monad m
    => (forall x. f x -> m x)
    -> (forall x. g x -> m x)
    -> Sum f g a
    -> m a
interpret hf _ (L mf) = hf mf
interpret _ hg (R mg) = hg mg
```

. . .

We can nest effects as deeply as we want inside of `Sum`!

----

# Effects a la Carte

```haskell
data Union r a
```

. . .

For example:

```haskell
Union '[Bell, Teletype, State Bool, Error InvalidArgument] a
```

. . .

`Union r` is a `Functor` iff every type inside of `r` is.

----

We can get in and out of a `Union`.


```haskell
class Member f r where
  inj  :: f a       -> Union r a
  proj :: Union r a -> Maybe (f a)
```


----


Before:

```haskell
writeLine :: String -> Free TeletypeWithBell ()
writeLine msg = Impure $ L $ WriteLine msg $ pure ()
```

After:


```haskell
writeLine :: Member Teletype r => String -> Free (Union r) ()
writeLine msg = Impure $ inj $ WriteLine msg $ pure ()
```

. . .

Now we are **polymorphic in our capabilities**.

----

This is where `freer-simple` and `fused-effects` start to differ.

. . .

> `freer-simple` diverges to get rid of the boilerplate.

. . .

> `fused-effects` diverges to get more speed and expressiveness.

. . .

Unfortunately, it's unclear how to merge the two differences.

----

# How Does `freer-simple` eliminate the boilerplate?

Insight: because we can't embed our effects, we can just keep them in a queue.

. . .

Rather than:

```haskell
echo = ReadLine $ \msg ->
       WriteLine msg
     $ Done ()
```

. . .


we can just write

```haskell
echo = [ReadLine, WriteLine]
```

. . .

(plus a little magic to thread the output of `ReadLine` to the input
of `WriteLine`)

---

With this encoding, we no longer need to have continuations in our effects.

. . .

Before:

```haskell
data Teletype a
  = WriteLine String a
  | ReadLine (String -> a)
```

. . .

After:

```haskell
data Teletype a where
  WriteLine :: String -> Teletype ()
  ReadLine  :: Teletype String
```

. . .

> Doesn't require `Functor` instances

> Exactly parallels the types of the actions

----

This is a great change, and is $O(n)$ faster than the naive encoding!

. . .

Unfortunately it has extremely high constant factors, due to needing to allocate
the intermediary queue of actions.


----

## Too Fast, Too Free

Two months ago, Li-Yao Xia:

<!-- TODO(sandy): get the real quote! -->

> I bet if you used the final encoding of `Freer`, it would be much faster.

```haskell
newtype Freer r a = Freer
  { runFreer
        :: ∀ m
         . Monad m
        => (∀ x. Union r x -> m x)
        -> m a
  }
```


. . .

What the heck is this thing??

----

`Free` is uniquely determined by its interpretation function:

```haskell
runFree
    :: Monad m
    => (∀ x. f x -> m x)
    -> Free f a
    -> m a
```

. . .

We can reshuffle the `Free` argument first, and use this function as our
definition of `Freer`.

----

Reshuffled:

```haskell
runFree
    :: Free (Union r) a
    -> ∀ m
     . Monad m
    => (∀ x. Union r x -> m x)
    -> m a
```

. . .

Put a newtype constructor around it:

```haskell
newtype Freer r a = Freer
  { runFreer
        :: ∀ m
         . Monad m
        => (∀ x. Union r x -> m x)
        -> m a
  }
```

----

It took me a few days to work through the implications of this encoding.

. . .

To my surprise, it improved the constant factors of `freer-simple` by 35x.

. . .

But why?

----

Consider the humble `ReaderT`:

```haskell
newtype ReaderT r m a = ReaderT
  { runReaderT :: r -> m a
  }
```

`ReaderT` lets you read a single, constant value of type `r`.

. . .

It is a zero-cost abstraction.

----

Anything look familiar?

```haskell
runReaderT
    :: Monad m
    => ReaderT r m a
    -> r
    -> m a
```
. . .
```haskell
runFreer
    :: Monad m
    => Freer r a
    => (∀ x. Union r x -> m x)
    -> m a
```

. . .

**`Freer` is just `ReaderT` in disguise!**

----

The proof:

```haskell
instance Monad (Freer f) where
  return a = Freer $ \nt -> pure a
  m >>= f  = Freer $ \nt -> do
    a <- runFreer m nt
    runFreer (f a) nt

instance (Monad m) => Monad (ReaderT r m) where
  return a = ReaderT $ \r -> pure a
  m >>= f  = ReaderT $ \r -> do
    a <- runReaderT m r
    runReaderT (f a) r
```

Identical `Monad` instances!


----

We can use the natural transformation to make effects zero cost.

. . .

```haskell
liftFreer :: Member f r => f a -> Freer r a
liftFreer fa = Freer $ \nt -> nt $ inj fa
```

. . .

Now:

```haskell
writeLine' :: Member Teletype r => String -> Freer r ()
writeLine' msg = liftFreer $ WriteLine msg
```

----

What the heck is going on?

Now any time our free monad wants to use an action, it immediately runs it in
the final monad.

---

# Even freer freer monads

```haskell
echo :: Member Teletype r => Freer r ()
echo = do
  msg <- readLine
  writeLine msg

echoIO :: IO ()
echoIO = runFreer runTeletypeInIO echo
```

----

```haskell
echoIO :: IO ()
echoIO = runFreer runTeletypeInIO echo
```

----

```haskell
echoIO :: IO ()
echoIO = runFreer runTeletypeInIO $ do
  msg <- readLine
  writeLine msg
```

----

```haskell
echoIO :: IO ()
echoIO = runFreer runTeletypeInIO $ do
  msg <- liftFreer ReadLine
  liftFreer $ WriteLine msg
```
----

```haskell
echoIO :: IO ()
echoIO = runFreer runTeletypeInIO $ do
  msg <- Freer $ \nt -> nt ReadLine
  Freer $ \nt -> nt $ WriteLine msg
```
----

```haskell
echoIO :: IO ()
echoIO = do
  msg <- runTeletypeInIO ReadLine
  runTeletypeInIO $ WriteLine msg
```

----

```haskell
echoIO :: IO ()
echoIO = do
  msg <- case ReadLine of
           ReadLine    -> getLine
           WriteLine s -> putStrLn s
  case WriteLine msg of
    ReadLine    -> getLine
    WriteLine s -> putStrLn s
```

----

```haskell
echoIO :: IO ()
echoIO = do
  msg <- case ReadLine of
           ReadLine    -> getLine
           -- WriteLine s -> putStrLn msg
  case WriteLine msg of
    -- ReadLine    -> getLine
    WriteLine s -> putStrLn s
```

----

```haskell
echoIO :: IO ()
echoIO = do
  msg <- case ReadLine of
           ReadLine -> getLine
  case WriteLine msg of
    WriteLine s -> putStrLn s
```

----

```haskell
echoIO :: IO ()
echoIO = do
  msg <- getLine
  putStrLn msg
```

. . .

So free!

----

We've now shown how to solve the boilerplate and performance problems.

. . .

## Lets rewind and look at the changes `fused-effects` makes.

----

# Down the other trouser (where we left off)

```haskell
data Free r k
  = Pure k
  | Impure (Union r (Free r k))


data Teletype a
  = WriteLine String a
  | ReadLine (String -> a)
  deriving Functor


writeLine :: Member Teletype r => String -> Free r ()
writeLine msg = Impure $ inj $ WriteLine msg $ pure ()
```

----

An effect we'd like, but can't have:

```haskell
throw
    :: Member (Error e) r
    => e
    -> Free r a

catch
    :: Member (Error e) r
    => Free r a
    -> (e -> Free r a)
    -> Free r a
```

`catch` contains an embedded `Free`.

----

What we'd like:
```haskell
data Error e k
  = Throw e
  | ∀ x. Catch (???)
               (e -> ???)
               (x -> k)
```

----

Maybe

```haskell
data Error e r k
  = Throw e
  | ∀ x. Catch (Free r x)
               (e -> Free r x)
               (x -> k)
```

?

. . .

Unfortunately this type cannot be embedded inside a `Union` :(

----

Instead:

```haskell
data Error e m k
  = Throw e
  | ∀ x. Catch (m x)
               (e -> m x)
               (x -> k)
```

. . .

Just force `m` to be `Free r`:

. . .

```haskell
data Free r a
  = Pure a
  | Impure (Union r (Free r) a)

liftFree :: Member f r => f (Free r) (Free r a) -> Free r a
```

----

Effects don't need to use `m` if they don't want to.

```haskell
data State s m k
  = Get (s -> k)
  | Put s k
```

----

## The Problem

How do `State` and `Error` interact?

. . .

How can we thread state changes through a `Catch` action?

----

## The Solution: Functors!

. . .

What is a functor, really?

. . .

Just a value in some sort of context.

. . .

In particular, a value of `f ()` is *only* a context!

----

We can abuse this fact, and wrap up the state of the world as some functor.

. . .

```haskell
class Effect e where
  weave :: Functor tk
        => tk ()
        -> (∀ x. tk (m x) -> n (tk x))
        -> e m a
        -> e n (tk a)
```

. . .

* `tk ()` is the state of the world when the effect starts

* `(∀ x. tk (m x) -> n (tk x))` is a distribution law for describing how to run
  effects in a context.

. . .

`weave` allows an effect to have other effects "pushed through it."

----

Weaving through `Error`:

```haskell
instance Effect (Error e) where
  weave _ _ (Throw e) = Throw e
  weave tk distrib (Catch try handle k) =
    Catch (distrib $ try <$ tk)
          (\e -> distrib $ handle e <$ tk)
          (fmap k)
```

. . .

The "ice-cream cone" operator replaces the contents of a `Functor`:

```haskell
(<$) :: Functor f => a -> f b -> f a
```

----

The `State` effect needs to push its state through other effects'
subcomputations.

It can call `weave` to do this.

. . .

```haskell
runState :: s -> Free (State s ': r) a -> Free r (s, a)
runState s (Pure a) = pure (s, a)
runState s (Impure u) =
  case decomp u of
    Left other -> Impure $
      weave (s, ())
            (\(s', m) -> runState s' m)
            other
    Right (Get k)    -> pure (s,  k s)
    Right (Put s' k) -> pure (s', k)
```

. . .

`decomp` can extract a single effect out of a `Union`; or prove that it was
never there to begin with.

. . .

```haskell
decomp
    :: Union (e ': r) m a
    -> Either (Union r m a) (e m a)
```

----

Surprisingly, this thing works!

. . .

But it's slow.

. . .

Because `runState` is recursive, GHC won't perform any optimizations on it :(



----

We can "break the recursion" by hand.

```haskell
runState :: s -> Free (State s ': r) a -> Free r (s, a)
runState s (Pure a) = pure (s, a)
runState s (Impure u) =
  case decomp u of
    Left other -> Impure $
      weave (s, ())
            (\(s, m) -> runState_b s m)
            other
    Right (Get k)    -> pure (s,  k s)
    Right (Put s k) -> pure (s, k)
{-# INLINE runState #-}
```

. . .
```haskell
runState_b :: s -> Free (State s ': r) a -> Free r (s, a)
runState_b = runState
{-# NOINLINE runState_b #-}
```

. . .

Now GHC is happy and will make our program **fast**!

----

Lots of the boilerplate in `fused-effects` comes from needing to write `Effect`
instances.

. . .

But these instances are necessary for higher-order effects!

. . .

Are we cursed to always have this boilerplate?

----

No!

. . .

```haskell
data Yo e m a where
  Yo :: Functor tk
     => e m a
     -> tk ()
     -> (forall x. tk (m x) -> n (tk x))
     -> (tk a -> b)
     -> Yo e n b
```

`Yo` is the free `Effect`!

. . .

```haskell
instance Effect (Yo e) where
  weave tk' distrib' (Yo e tk distrib f) =
    Yo e (Compose $ tk <$ tk')
         (fmap Compose . distrib' . fmap distrib . getCompose)
         (fmap f . getCompose)
```

----

And we can get into a `Yo` by using an `Identity` functor as our initial state.

```haskell
liftYo :: Functor m => e m a -> Yo e m a
liftYo e = Yo e (Identity ())
                (fmap Identity . runIdentity)
                runIdentity
```

----

Somewhat amazingly, this works!

. . .

But all it means is we've delayed giving a meaning for `Effect` until we need to
interpret it.

----

A problem:

The type of `runFree` doesn't allow us to change the return type.

```haskell
runFree
    :: ∀ m. Monad m
    => Free r a
    -> (∀ x. Union r (Free r) x -> m x)
    -> m a
```

. . .

It seems like maybe we could just stick a functor in here.

. . .

```haskell
runFree
    :: ∀ m tk. (Monad m, Functor tk)
    => Free r a
    -> (∀ x. Union r (Freer r) x -> m (tk x))
    -> m (tk a)
```

. . .

**Unfortunately this is no longer a `Monad`!**

----

Recall that we're allowed to pick *any* `Monad` for the result of `runFree`.

Instead of evaluating to the final monad `m`...

----

Just transform it into `StateT s m` and immediately evaluate *that*!

. . .

```haskell
import qualified Control.Monad.Trans.State as S

runState
    :: s
    -> Free (e ': r) a
    -> Free r (s, a)
runState s (Free m) = Free $ \nt ->
  S.runStateT s $ m $ \u ->
    case decomp u of
      Left x -> S.StateT $ \s' ->
        nt . weave (s', ()) (uncurry $ runState f)
           $ x
      Right (Yo Get _ f)      -> fmap f $ S.get
      Right (Yo (Put s') _ f) -> fmap f $ S.put s'
```

----

We've solved all of the problems! We now have solutions for

* *performance*
* *expressiveness*
* *boilerplate*

all of which work together!

. . .

But what we've built isn't yet a joyful experience.

. . .

In particular, dealing with `Yo` is painful.

----

We can clean up the mess of writing effect handlers...

. . .

...

. . .

...with an effect-handler effect!

---

Instead of this:

```haskell
instance Effect (Error e) where
  weave _ _ (Throw e) = Throw e
  weave tk distrib (Catch try handle k) =
    Catch (distrib $ try <$ tk)
          (\e -> distrib $ handle e <$ tk)
          (fmap k)
```

---

We can just write this:

```haskell
runError = interpretH $ \case
  Catch try handle -> do
    t <- runT try
    tried <- runError t
    case tried of
      Right a -> pure $ Right a
      Left e -> do
        h <- bindT handle
        handled <- h e
        case handled of
          Right a -> pure $ Right a
          Left e2 -> pure $ Left e2
```

The magic is in `runT` and `bindT`.

----

These combinators come from the `Tactics` effect:

. . .

```haskell
data Tactics tk n r m a where
  GetInitialState     :: Tactics tk n r m (tk ())
  HoistInterpretation :: (a -> n b)
                      -> Tactics tk n r m (tk a -> Free r (tk b))
```
. . .

- `GetInitialState` is the `tk ()` parameter

. . .

- `HoistInterpretation` is the distribution law

----

```haskell
type WithTactics e tk m r = Tactics tk m (e ': r) ': r
```

. . .

```haskell
pureT
   :: a
   -> Free (WithTactics e tk m r) (tk a)
```
. . .
```haskell
runT
    :: m a
    -> Free (WithTactics e tk m r)
                (Free (e ': r) (tk a))

```
. . .
```haskell
bindT
    :: (a -> m b)
    -> Free (WithTactics e tk m r)
                (tk a -> Free (e ': r) (tk b))
```

----

This is where we stop.

. . .

We've now simultaneously solved the boilerplate and
performance problems, as well as put a friendly UX around the whole thing.

----

I'd like to leave you with a comparison.

. . .

First, the implementation of `bracket` in `fused-effects`:

----

```haskell

data Resource m k
  = forall resource any output.
      Resource (m resource)
               (resource -> m any)
               (resource -> m output)
               (output -> k)

deriving instance Functor (Resource m)

instance HFunctor Resource where
  hmap f (Resource acquire release use k) =
    Resource (f acquire) (f . release) (f . use) k

instance Effect Resource where
  handle state handler (Resource acquire release use k)
    = Resource (handler (acquire <$ state))
               (handler . fmap release)
               (handler . fmap use)
               (handler . fmap k)

bracket :: (Member Resource sig, Carrier sig m)
        => m resource
        -> (resource -> m any)
        -> (resource -> m a)
        -> m a
bracket acquire release use =
  send (Resource acquire release use pure)

runResource :: (forall x . m x -> IO x)
            -> ResourceC m a
            -> m a
runResource handler = runReader (Handler handler) . runResourceC

newtype ResourceC m a = ResourceC
  { runResourceC :: ReaderC (Handler m) m a
  }
  deriving ( Alternative, Applicative, Functor, Monad, MonadFail, MonadIO, MonadPlus)

instance MonadTrans ResourceC where
  lift = ResourceC . lift

newtype Handler m = Handler (forall x . m x -> IO x)

runHandler :: Handler m -> ResourceC m a -> IO a
runHandler h@(Handler handler) = handler . runReader h . runResourceC

instance (Carrier sig m, MonadIO m) =>
      Carrier (Resource :+: sig) (ResourceC m) where
  eff (L (Resource acquire release use k)) = do
    handler <- ResourceC ask
    a <- liftIO (Exc.bracket
      (runHandler handler acquire)
      (runHandler handler . release)
      (runHandler handler . use))
    k a
  eff (R other) = ResourceC (eff (R (handleCoercible other)))
```

----

Compare to `polysemy`:

----


```haskell

data Resource m a where
  Bracket :: m a -> (a -> m ()) -> (a -> m b) -> Resource m b

makeSemantic ''Resource


runResource
    :: Member (Lift IO) r
    => (∀ x. Semantic r x -> IO x)
    -> Semantic (Resource ': r) a
    -> Semantic r a
runResource finish = interpretH $ \case
  Bracket alloc dealloc use -> do
    a <- runT  alloc
    d <- bindT dealloc
    u <- bindT use

    let runIt = finish .@ runResource
    sendM $ X.bracket (runIt a) (runIt . d) (runIt . u)
```

----

## Shoutouts

> My girlfriend Virginie for putting up with me talking about free monads for
two months.

. . .

> Li-Yao Xia for showing me the final encoding of `Freer`.

. . .

> Rob Rix for sitting down with me and explaining how the heck `fused-effects` is so fast.

----

# Thanks for listening!

. . .

Questions?


