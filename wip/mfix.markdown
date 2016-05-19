---
layout: post
title: mfix
date: TO_BE_DETERMINED
comments: true
tags: foo, bar
---

As is so often the case in the land of Haskell, sometimes you run into a problem
that you have no idea how to solve. In the realm of popular programming
languages, the solution is usually to go post on [stack overflow][so] and have
someone else figure it out for you. Generally this approach doesn't work in
Haskell. In Haskell, you need to go read a paper.

Last week I was working on tying a [recursive knot][mfix] (constructing
immutable objects in terms of one another) in my [extensibly effective][eff]
[functionally reactive][frpnow] game. As far as I know, this has never been done
before. It was all working well enough, and I should have left it alone, but I
wanted to tighten that knot and add an extra mutually-recursive dependency. I
just had to go and do it.

In one of the most extreme counterexamples I've seen to the Haskell rule of "if
it compiles, it works", my code compiled, but, as you can probably guess, it
didn't work.

> "thread blocked indefinitely in an MVar operation"

I'm still not 100% sure what this means, but I assume it means `A` is holding
off on being constructed until `B` is done, but `B` is likewise waiting for `A`.
If my analytics are correct, we've got a genuine case of the [dining
philosophers][philosophers] on our hands.

What do? Don't know. Google didn't help.

And like so often before, I went off to read a paper. I assumed it was my
knot-tying that was the issue, so I started there.

The paper I found was called [Value Recursion in Monadic Computations][paper].
It's about how we can construct monadic values out of functions which *produce*
monadic values. Granted, this doesn't sound very impressive, until you look at
the type of the crazy thing we're building:

`mfix :: Monad m => (a -> m a) -> m a`

Somehow we're pulling an `m a` out of a `a -> m a` without having an `a` to
apply to the damn thing. But how? Magic.

This paper didn't actually help with my problem, but (like always) it was a
fascinating read. The `mfix` bits were OK, but instead what I got out of it was
a new interpretation of monads that I hadn't internalized before. So I wanted to
talk about that.

[so]:
[mfix]:
[eff]:
[frpnow]:
[philosophers]:
[paper]:


## Motivation

> This section is *very strongly inspired* by _Value Recursion in Monadic
Computations_.

Imagine we wanted to implement a system that would simulate electrical circuits
which evolved discretely. We will model `Signal`s with `List`s indexed by time.

```haskell
type Signal a = [a]

and, xor :: Signal Bool -> Signal Bool -> Signal Bool
and a b = zipWith (&&) a b
xor a b = zipWith (/=) a b

invert :: Signal Bool -> Signal Bool
invert a = map not a

delay :: String -> a -> Signal a -> Signal a
delay name start sig = start : sig
```

The first few functions are uninteresting; they compute the `and`, `xor` and
negation of `Signal`s of `Bool`s, simply by running a function pairwise on the
input signals.

`delay`, however, is a little more interesting -- it creates a new signal which
is one tick out of phase with the input signal, and has an initial value for the
first tick. As an example, `delay "ones" 0 [1,1,1] = [0,1,1,1]`. We attach a
name to it for future work.

