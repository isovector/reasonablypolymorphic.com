---
layout: post
title: "Freer Monads: Too Fast, Too Free"
date: 2019-02-18 14:56
comments: true
tags: freer-monads, extensible-effects, performance, technical
---

The venerable [Lyxia][lyxia] had this to say about my [last post on freer
monads][freer]:

[lyxia]: https://poisson.chat/
[freer]: https://reasonablypolymorphic.com/blog/freer-monads/

> I agree the performance argument is way less important than the frequency at
> which it's thrown around makes it seem. The reason freer performance sucks is
> that you're repeatedly constructing and deconstructing trees at runtime.
> However, that is only a consequence of the implementation of freer as a GADT
> (initial encoding). I bet the final encoding can do wonders:
>
> `newtype Freer f a = Freer (forall m. Monad m => (forall t. f t -> m t) -> m a)`

I spent a few days working through the implications of this, and it turns out to
be a particularly compelling insight. Behold the microbenchmarks between
`freer-simple` and an equivalent program written against `mtl`:

```
benchmarking freer-simple
time                 745.6 μs   (741.9 μs .. 749.4 μs)
                     1.000 R²   (0.999 R² .. 1.000 R²)
mean                 745.1 μs   (742.2 μs .. 748.5 μs)
std dev              10.68 μs   (8.167 μs .. 14.23 μs)

benchmarking mtl
time                 10.96 μs   (10.93 μs .. 10.98 μs)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 10.95 μs   (10.92 μs .. 10.99 μs)
std dev              119.3 ns   (93.42 ns .. 153.7 ns)
```

Not so good; `freer-simple` is like 75x worse in this case! But the same program
again when written in this final encoding is pretty damn fast:

```
benchmarking too-fast-too-free
time                 24.23 μs   (24.10 μs .. 24.37 μs)
                     1.000 R²   (1.000 R² .. 1.000 R²)
mean                 24.27 μs   (24.15 μs .. 24.40 μs)
std dev              448.8 ns   (355.8 ns .. 586.1 ns)
```

It's roughly 2x slower than `mtl`, which is AKA 35x faster than `freer-simple`.
This is pretty sweet, and it comes with the benefit of getting to keep the
underlying semantics of `freer-simple`.

So without further ado, I'd like to share my work-in-progress with you,
tentatively named [`too-fast-too-free`][tftf]. This is ready for prime-time, but
I'd prefer to merge it to someone upstream rather than pollute hackage with yet
another free(r) monad extensible effects package.

[tftf]: https://github.com/isovector/too-fast-too-free

I'll do it if I have to, but the performance is fair game for anyone who wants
it. If I don't hear from anyone by next week, I'll publish a new package to
hackage and begin the freer monad revolution we've all been waiting for.


## What the Heck Is Any of this Stuff Anyway?

Let's investigate this finally-encoded type and see where this performance comes
from:

```haskell
newtype Freer f a = Freer
  { runFreer :: forall m. Monad m => (forall t. f t -> m t) -> m a
  }
```

The type of `runFreer` is saying "if you give me a `Freer f a` and a natural
transformation from `f` to some monad `m`, then I can give you back an `m a`."
Sounds promising, right?

`Freer`'s instance for `Monad` is written in terms of this final `m`, and so
short of shunting around some functions, we're not really paying any cost for
binds compared to just writing in terms of `m`:

```haskell
instance Monad (Freer f) where
  Freer ma >>= f = Freer $ \k -> do
    a <- ma k
    runFreer (f a) k
```

Compare this to the approach used by `freer-simple` which needs to allocate
leafs in a tree for every bind (and for every `fmap` and `ap`!) That's a huge
win already.

Turning `Freer` into `Eff` uses the same trick as `freer-simple`---let `Eff r`
be `Freer (Union r)`, where `Union r` is a value that can be any effect in `r`.
A natural transformation `forall m. Monad m => (forall t. Union r t -> m t)`
must therefore handle every possible effect in `r`, and so we haven't lost
any capabilities with our new encoding.

The challenging part was figuring out how to plumb state through the encoding of
`Freer f a`---after all, many interesting interpreters are necessarily stateful.

Fortunately there's a trick. Because `Eff (e ': r) a` can be interpreted
in terms of *any* `Monad` `m`, we can choose `m ~ StateT s (Eff r)`, and get our
statefulness from `StateT` directly. Because `StateT`'s bind is written in terms
of its underlying monad, this trick doesn't cost us anything more than shunting
another few functions around.

We can achieve short-circuiting interpreters similarly by evaluating them via
`ExceptT (Eff r)`. In fact, this pattern turns out to be pretty common---and it
generalizes thusly:

```haskell
transform
    :: ( MonadTrans t
       , MFunctor t
       , forall m. Monad m => Monad (t m)
       )
    => (forall m. Monad m => t m a -> m b)
       -- ^ The strategy for getting out of the monad transformer.
    -> (eff ~> t (Eff r))
    -> Eff (eff ': r) a
    -> Eff r b
transform lower f (Freer m) = Freer $ \k -> lower $ m $ \u ->
  case decomp u of
    Left  x -> lift $ k x
    Right y -> hoist (usingFreer k) $ f y
```

Admittedly the type is a little terrifying, but library code can [specialize
it][stateful] down to [less offensive][shortcircuit] combinators.

[stateful]: https://github.com/isovector/too-fast-too-free/blob/91aad992db3b35401acf7335ef24dad39d481648/src/Eff/Interpretation.hs#L36-L43
[shortcircuit]: https://github.com/isovector/too-fast-too-free/blob/91aad992db3b35401acf7335ef24dad39d481648/src/Eff/Interpretation.hs#L76-L83

At the end of the day, this final encoding means that `Freer` code specializes
down to its eventual result anyway, giving us the "fusion" of
[`fused-effects`][fused] without the boilerplate.

[fused]: https://github.com/robrix/fused-effects

Hopefully these results are enough to finally put the "free monads have bad
performance" argument to rest. I'll have some promising results on the `bracket`
front as well that require some refinement, but hopefully those will come sooner
than later.

¡Viva la freer monad revolucion!

