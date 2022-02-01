---
layout: post
title: "GHC's Specializer: Much More Than You Wanted to Know"
date: 2019-05-18 21:59
comments: true
tags: ghc, haskell, polysemy, optimization
---

In the course of [tracking down why free monads were so slow][slow], I fell into
a deep labyrinth of scary GHC internals. Six weeks later, I emerged,
significantly more knowledgeable, and having implemented some changes in the
compiler that will allow [`polysemy`][polysemy] to be optimized much better. The
improvements will be available in 8.10.1.

[slow]: /blog/freer-yet-too-costly/
[polysemy]: https://hackage.haskell.org/package/polysemy

All of this seems like a good opportunity to share what I've learned, so today
let's talk about GHC's *specialization pass.* This optimization is more
popularly known as "the reason why `mtl` is so fast."

At a high level, the specialization pass is responsible for optimizing away uses
of ad-hoc polymorphism (typeclasses) in Haskell source code. When `-fspecialise`
is enabled, GHC will make a monomorphic copy of every polymorphic method --- one
for every unique type it's called with. The result should feel similar to anyone
who's written modern C++, as it's completely analogous to how templates work.

While polymorphic functions are great for *humans to write*, they're
significantly slower for *machines to execute,* since you need to pass around
vtables and perform dynamic dispatches, and all sorts of crazy things. This is
exactly the purpose of GHC's specialization pass, to simply get rid of all of
that machinery and keep only the pieces that are explicitly used.

Let's take an example. Consider the following program:

```haskell
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC
      -ddump-simpl
      -dsuppress-idinfo
      -dsuppress-coercions
      -dsuppress-module-prefixes
      -fforce-recomp
      #-}

import           Control.Monad.State.Class
import qualified Control.Monad.Trans.State as S

countdown :: S.StateT Int IO ()
countdown = do
  v <- get
  case v of
    0 -> pure ()
    _ -> do
      put $ v - 1
      countdown

main :: IO ()
main = S.evalStateT countdown 10
```

When compiled via `ghc Example.hs -O -fno-specialise`[^1], we can
look directly at the resulting Core of this program. If you're unfamiliar with
Core, it's GHC's intermediate language between source-level Haskell and the
generated machine code. Core differs in two notable ways from source Haskell:
its evaluation is explicit via `case` expressions, and both types and typeclass
instances are explicitly passed around.

[^1]: The meaning of the flags is --- `-O`: enable optimizations; `-fno-specialise`: disable the specialization pass.

Anyway, here's the relevant Core for our above program:

```haskell
Rec {
-- RHS size: {terms: 14, types: 13, coercions: 0, joins: 0/0}
$wcountdown
  :: Int# -> State# RealWorld -> (# State# RealWorld, ((), Int) #)
$wcountdown
  = \ (ww_s49L :: Int#) (w_s49I :: State# RealWorld) ->
      case ww_s49L of ds_X2I1 {
        __DEFAULT -> $wcountdown (-# ds_X2I1 1#) w_s49I;
        0# -> (# w_s49I, lvl1_r4ap #)
      }
end Rec }

-- RHS size: {terms: 12, types: 29, coercions: 0, joins: 0/0}
main1 :: State# RealWorld -> (# State# RealWorld, () #)
main1
  = \ (s_a2Ks :: State# RealWorld) ->
      case $wcountdown 10# s_a2Ks of { (# ipv_a2Kv, ipv1_a2Kw #) ->
      (# ipv_a2Kv,
         case ipv1_a2Kw of { (a1_a2I6, ds2_a2I7) -> a1_a2I6 } #)
      }
```

As you can see, this is very short and to the point. Reading Core is a bit of an
art, but the gist of it is this: `main1` calls `$wcountdown`, which recursively
calls itself, until the value of `w_s49I` is `0#` when it stops. It's probably
exactly the same code you'd write by hand, if for some reason you were writing
Core by hand.

Our program above is written directly against `transformers`, but nobody
actually writes code against `transformers` in the real world. Choosing a
concrete monad transformer stack is limiting, and at the same time, prevents you
from restricting access to pieces of the stack. Instead, we're encouraged to
write code against abstract monad capabilities, traditionally `mtl`.

So let's subtly change the type of `countdown` above:

```haskell
countdown :: MonadState Int m => m ()
```

Nothing else in the program needs to change. Let's now compile this program
again via `ghc Example.hs -O -fno-specialise`. The result is
*horrendously* worse Core:

```haskell
Rec {
-- RHS size: {terms: 35, types: 47, coercions: 0, joins: 0/2}
$wcountdown
  :: forall (m :: * -> *).
     Applicative m =>
     (forall a b. m a -> (a -> m b) -> m b)
     -> (forall a b. m a -> m b -> m b)
     -> m Int
     -> (Int -> m ())
     -> m ()
$wcountdown
  = \ (@ (m_s4WK :: * -> *))
      (ww_s4WR :: Applicative m_s4WK)
      (ww1_s4WS :: forall a b. m_s4WK a -> (a -> m_s4WK b) -> m_s4WK b)
      (ww2_s4WT :: forall a b. m_s4WK a -> m_s4WK b -> m_s4WK b)
      (ww3_s4WX :: m_s4WK Int)
      (ww4_s4WY :: Int -> m_s4WK ()) ->
      let {
        lvl6_s4W1 :: m_s4WK ()
        lvl6_s4W1
          = $wcountdown
              @ m_s4WK ww_s4WR ww1_s4WS ww2_s4WT ww3_s4WX ww4_s4WY } in
      let {
        lvl7_s4W2 :: m_s4WK ()
        lvl7_s4W2 = pure @ m_s4WK ww_s4WR @ () () } in
      ww1_s4WS
        @ Int
        @ ()
        ww3_s4WX
        (\ (v_a192 :: Int) ->
           case v_a192 of { I# ds_d3xJ ->
           case ds_d3xJ of ds1_X3xT {
             __DEFAULT ->
               ww2_s4WT @ () @ () (ww4_s4WY (I# (-# ds1_X3xT 1#))) lvl6_s4W1;
             0# -> lvl7_s4W2
           }
           })
end Rec }

-- RHS size: {terms: 17, types: 32, coercions: 21, joins: 0/0}
main1 :: State# RealWorld -> (# State# RealWorld, () #)
main1
  = \ (s_a3z5 :: State# RealWorld) ->
      case (((($wcountdown
                 @ (StateT Int IO)
                 lvl_r4VN
                 lvl1_r50i
                 lvl2_r50j
                 (lvl3_r50k `cast` <Co:13>)
                 lvl4_r50l)
              `cast` <Co:4>)
               lvl5_r50m)
            `cast` <Co:4>)
             s_a3z5
      of
      { (# ipv_a3z8, ipv1_a3z9 #) ->
      (# ipv_a3z8,
         case ipv1_a3z9 of { (a1_a3y3, ds2_a3y4) -> a1_a3y3 } #)
      }
```

Yikes! What a mess! It's amazing how much of a difference that one type
signature made!  Our simple `mtl` program above has turned into an unholy
mess of passing around overly-polymorphic functions. We've paid an awful price
to abstract away our monad stack, *even though the actual program being run
didn't change!*

Of course, this isn't a *real problem* in the wild. Compile the program again,
this time without the `-fno-specialise` flag[^2] --- `ghc Example.hs -O`:

[^2]: `-fspecialise` is included in `-O`.

```haskell
Rec {
-- RHS size: {terms: 14, types: 13, coercions: 0, joins: 0/0}
$w$scountdown
  :: Int# -> State# RealWorld -> (# State# RealWorld, ((), Int) #)
$w$scountdown
  = \ (ww_s5dY :: Int#) (w_s5dV :: State# RealWorld) ->
      case ww_s5dY of ds_X3xU {
        __DEFAULT -> $w$scountdown (-# ds_X3xU 1#) w_s5dV;
        0# -> (# w_s5dV, lvl1_r5jV #)
      }
end Rec }

-- RHS size: {terms: 12, types: 29, coercions: 0, joins: 0/0}
main1 :: State# RealWorld -> (# State# RealWorld, () #)
main1
  = \ (s_X3Bw :: State# RealWorld) ->
      case $w$scountdown 10# s_X3Bw of { (# ipv_a3z9, ipv1_a3za #) ->
      (# ipv_a3z9,
         case ipv1_a3za of { (a1_a3y4, ds2_a3y5) -> a1_a3y4 } #)
      }
```

Whew! We're back to the speedy program we started with. `-fspecialise` has done
the hard work of transforming our *abstract code* into *fast code* for us ---
exactly as a good compiler should.


## What's Going On?

It's amazing how drastic the differences are in the generated code, just from
flipping a switch!

Before we can discuss exactly how this transformation helps, we need to first
go over some details of how GHC implements a few source-level Haskell features.
The first is *dictionaries*, which are how typeclass dispatch works.

### Dictionaries

Consider the following program in source-level Haskell:

```haskell
class Eq a where
  (==) :: a -> a -> Bool

instance Eq () where
  (==) _ _ = True

equate :: Eq a => a -> a -> Bool
equate a1 a2 = a1 == a2

main :: IO ()
main = print $ equate () ()
```

Internally, GHC will generate the equivalent program:

```haskell
data Eq a = Eq  -- #1
  (a -> a -> Bool)

(==) :: Eq a -> a -> a -> Bool
(==) dEq'a =  -- #2
  case dEq'a of
    Eq eqMethod -> eqMethod

eqUnit :: Eq ()  -- # 3
eqUnit = Eq
  (\_ _ -> True)

equate :: Eq a -> a -> a -> Bool  -- #4
equate dEq'a a1 a2 = (==) dEq'a a1 a2  -- #5

main :: IO ()
main = print $ equate eqUnit () ()  -- #6
```

Notably, the following changes occur:

1. The `class Eq a` is transformed into `data Eq a`, with each class method
   becoming a field.
2. The class method `(==)` receives a new `Eq a` parameter, and becomes a
   function which pattern matches on it.
3. The `instance Eq ()` becomes a top-level declaration of an `Eq ()` value.
4. The `Eq a` *constraint* on `equate` becomes a *parameter* of the new `Eq a`
   datatype.
5. The usage of `(==)` in `equate` receives the new `dEq'a` parameter.
6. The usage of `equate` at type `a ~ ()` in `main` receives the new top-level
   `eqUnit :: Eq ()` value as an argument.

We call the values `eqUnit` and `dEq'a` *dictionaries*. More precisely, a
dictionary is any value whose type is a data type corresponding to a typeclass.
Dictionaries do not exist in source-level Haskell, only in the generated Core.
In real Core, dictionaries have names that start with `$d`, but we'll omit the
leading `$` today, so we don't get it confused with the `($)` operator.

From all of this that we see that, under the hood, `class` definitions are just
`data` definitions, and that constraints are just invisible parameters.


### Case of Known Constructor

Consider the following program:

```haskell
blah =
  case True of
    True  -> foo
    False -> bar
```

Because we're scrutinizing on a constant value here, the result of this
expression must always be `foo`.  As such, it's safe to replace the entire
pattern match expression with `foo`:

```haskell
blah = foo
```

This transformation is known as the *case of known constructor* optimization.
While humans would never write such a thing by hand, expressions like these
often come up as the result of other optimizing transformations.


### Rewrite Rules

One final thing to discuss is GHC's term rewriting mechanism, known as *rewrite
rules*.

Rewrite rules are little statements that say "*this thing* can be written as
*that thing*." Whenever GHC encounters *this thing*, it will duly rewrite it as
*that thing*. The motivating use case is to allow library authors to implement
domain-specific optimizations --- such as ensuring composing functions don't
generate intermediate structures. You might have heard of "list fusion," which
is implemented via rewrite rules.

Rewrite rules must preserve the type of the expression, but besides that are
free to do anything they'd like. Just as an example, we can write a program
which prints `hello world` seemingly from nowhere:

```haskell
{-# RULES
  "it's magic!"
    pure () = putStrLn "hello world"
  #-}

main :: IO ()
main = pure ()
```

Compiling this with `-O0` won't print any message when run, but will print
`hello world` when compiled with `-O`. Spooky!

When `-XTypeApplications` is enabled, rewrite rules are allowed to match on
types too! For example, the following program will print `2 1 1`:

```haskell
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeApplications    #-}

magic :: forall b a. a -> a
magic = id
{-# NOINLINE magic #-}

{-# RULES "it's magic!"
      forall (a :: Int).
        magic @String a = a + 1
      #-}

main :: IO ()
main = do
  print $ magic @String (1 :: Int)
  print $ magic @Bool   (1 :: Int)
  print $ magic @String (1 :: Integer)
```

Of course, you shouldn't abuse rewrite rules like this --- make sure any rules
you write are just more efficient versions of an equivalent program --- but it's
helpful to demonstrate what's going on.

Internally, GHC uses lots of rewrite rules itself! All of its constant-folding
(e.g. replacing `2 + 3` with `5` at compile time) is done via rewrite rules,
which helps separate that logic from the main compiler.



## Specialization


So with all of that background information out of the way, we're finally ready
to talk about how the specializer works.

Recall our original `mtl` program, transformed so it has its dictionaries
explicitly passed:

```haskell
countdown :: Monad m -> MonadState Int m -> m ()
-- There is a `Monad m` constraint on `MonadState s m`, which is where this
-- extra constraint comes from.
countdown dMonad'm dMonadState'm = do dMonad'm
  v <- get dMonadState'm
  case v of
    0 -> pure dMonad'm ()
    _ -> do dMonad'm
      put dMonadState'm $ v - 1
      countdown dMonad'm dMonadState'm

main :: IO ()
main =
  S.evalStateT
    (countdown
      (dMonadStateT dMonadIO)
      (dMonadStateStateT dMonadIO))
    10
```

When `-fspecialise` is set, the specializer will look for any calls to
polymorphic functions with all of their dictionaries saturated by "interesting"
dictionaries. The dictionaries `dMonad'm` and `dMonadState'm` in `countdown`
aren't interesting, since they're just opaque dictionary variables; we don't
know anything about them.

However, GHC notices that `countdown` is called with `m ~ StateT Int IO`, and
that all of its dictionaries are statically known. As such, it emits a
*specialized* version of `countdown`, monomorphized to `StateT Int IO ()`:

```haskell
scountdown_StateT :: StateT Int IO ()
scountdown_StateT = do (dMonadStateT dMonadIO)
  v <- get (dMonadStateStateT dMonadIO)
  case v of
    0 -> pure (dMonadStateT dMonadIO) ()
    _ -> do (dMonadStateT dMonadIO)
      put (dMonadStateStateT dMonadIO) $ v - 1
      scountdown_StateT
```

In addition, the specializer will emit a rewrite rule:

```haskell
{-# RULES "SPEC countdown @ (StateT Int IO)"
      forall (dMonad'm :: Monad (StateT Int IO))
             (dMonadState'm :: MonadState Int (StateT Int IO)).
        countdown @(StateT Int IO) dMonad'm dMonadState'm =
          scountdown_StateT
      #-}
```

This rewrite rule will find any call to countdown at `m ~ StateT Int IO`, ignore
the dictionaries passed to it, and replace the entire expression with the
specialized `scountdown_StateT` function.

In particular, this means that `main` becomes:

```haskell
main :: IO ()
main = S.evalStateT scountdown_StateT 10
```

The rule takes advantage of the fact that dictionaries are known to be
consistent (all expressions for a dictionary of a given type eventually evaluate
to the same record), so it can completely ignore its two dictionary arguments.
However, in principle there's *absolutely no reason* this same technique
couldn't be used to specialize on other, non-dictionary, arguments!

Notice now that `pure`, `get`, and the two do-blocks in `scountdown_StateT` are
now called with interesting dictionaries, so `pure`, `get` and `>>=` can now all
also be specialized at `StateT Int IO`.

Eventually the concrete dictionaries and corresponding specializations have
propagated throughout the entire program. The optimizer can take advantage of
two other properties now, namely that class methods were already transformed
into pattern matches, and that all of the dictionaries are statically known.
Which means, we have created several places in which we can now *case of known
case!*

For example, let's consider the `get` in `countdown`. It now looks something
like this:

```haskell
  v <- case MonadState (StateT $ \s -> implOfPureForIO (s, s)) ... of
         MonadState getMethod _ _ -> getMethod
```

which can obviously be simplified to

```haskell
  v <- StateT $ \s -> implOfPureForIO (s, s)
```

This is already a great improvement! But it gets better, recall that we're
binding in the `StateT` monad, which in turn is calling bind in `IO`. But bind
in `IO` is itself implemented as a pattern match, and so
case-of-known-constructor applies there too!

The end result is that GHC spins for a while, alternatingly specializing,
inlining, case-of-known-casing, and performing a few other optimizations. Each
of these in turn opens up additional opportunities for the others to fire. After
a few iterations of this, the resulting code is often *orders of magnitude*
faster!


## Coming in 8.10.1...

Everything described above is how the compiler behaves today in GHC 8.6.5 (and
has, since like 2007 or something.) However, when digging into the performance
of my free monad library [`polysemy`][polysemy], I noticed that code written
against my library wasn't benefiting from the specialization pass! As a result,
my library was performing anywhere between 10x and 1000x *worse* than `mtl`,
even though *the eventual code being run was identical to `mtl`.*

Like our experiments above into `mtl`, I was paying a performance cost for
abstraction, even though the concrete program was identical.

Some investigation by the indefatigable [mpickering][mpickering] pointed out
that the specializer was failing to specialize. As it happens, the specializer
is more than happy to optimize away dictionaries that are passed as the *first*
non-type arguments to a function, but no others.

[mpickering]: https://mpickering.github.io/

That means it will go home early if it runs into a function whose signature is
of the form:

```haskell
foo :: Int -> forall a. Eq a => ...
```

Again, humans would never write such a thing, but the optimizer is more than
happy to spit these things out. Additionally, code like this often shows up
whenever you use a newtype to get around GHC's annoying error that it "does not
(yet) support impredicative polymorphism".

Anyway, all of this is to say that in 8.10.1, the specialization pass is [now
smart enough][patch] to specialize functions like `foo`. As a result, we should
see very real performance improvements in libraries like `polysemy` and `lens`,
and, excitingly, *any programs which use them!*

[patch]: https://gitlab.haskell.org/ghc/ghc/merge_requests/668

