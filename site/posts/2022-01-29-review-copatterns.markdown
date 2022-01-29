---
layout: post
title: "Review: Copatterns"
date: 2022-01-29 11:39
comments: true
tags: review, types, copatterns, abel, pientka, thibodeau, setzer
---

Another week, another paper review. This week my plan was to look at the
word2vec paper, but I made the mistake of not looking into it early in the week,
and by the time I did, it was extremely underwhelming. So instead, we're going
to take a look at Abel, Pientka, Thibodeau and Setzer's [Copatterns: Programming
Infinite Structures by Observations][copatterns].

[copatterns]: http://www2.tcs.ifi.lmu.de/~abel/popl13.pdf

In this paper, Abel et al. present *copatterns,* the categorical duals of
pattern matching. I'd briefly encountered copatterns when playing with Agda, but
thought it was just a funny syntax for building records. I didn't look much into
it --- instead being distracted by all the cool things I could do with dependent
types.

The paper presents copatterns, gives some motivating examples, and then does a
bunch of type theory stuff to prove they play nicely. Today I'm going to look
only at the first two sections, omitting the type theory stuff. Not because I'm
not interested, but because I'd like to find a nice introductory paper to type
theory stuff, rather than try to hammer it through my thick skull at the same
time as trying to figure out what Abel et al. are trying to show me. Note to
self, that would be a good paper to tackle for next week.

So, what is a copattern? While patterns let us map out of inductive types,
copatterns let us map into coinductive types. Right, ok, but what does that
really mean? Pattern matching lets us branch on the way a piece of data was
built. But dually, copattern matching lets us branch to define a piece of
codata.

Some examples will help.

The paper: "one should distinguish between finite, inductive data defined by
constructors and infinite, coinductive data which is better described by
observations... one can declare codatatypes via a list of their destructors."

It's a little hard to see this for me, coming from Haskell where laziness lets
us play very fast and loose in the differences between data and codata. But
fundamentally, data is built inductively: by taking smaller pieces, and
assembling them into something bigger. Thus, data is always finite.

## Streams

Codata, however, is infinite, and accomplishes that by being built out of
*bigger* pieces. The canonical example given to us is a `Stream`:

```agda
record Stream (A : Set) : Set where
  coinductive
  constructor _:>_
  field
    head : A
    tail : Stream A
```

In order to build a `Stream A`, *you must already have one.* There is no base
case! That's actually pretty wild, if you think about it!

Returning to the paper, we can think of `Stream`s as being opaque objects,
equipped with two observations:

```agda
head : Stream A -> A
tail : Stream A -> Stream A
```

and fact, any other observation on `Stream`s "factors out" into at least one of
these observations (by virtue of their being the definition of `Stream`.) The
paper gives an example of a stream producer that builds the stream `N, N-1, N-2,
..., 0, N, N-1 ...`. Their presentation leaves a bit to be desired, so I've
changed it a little here:

```agda
cycleNats : Nat -> Nat -> Stream Nat
cycleNats N x = ?
```

where `N` is the `Nat` we're counting down from, and `x` is the `Nat` we're
currently at. Here, we'd like to *build* a `Stream`, and the idea of copatterns
is that we can define a function by defining every observation over it:

```agda
cycleNats : Nat -> Nat -> Stream Nat
Stream.head (cycleNats N x) = ?
Stream.tail (cycleNats N x) = ?
```

Take a moment to think about what's going on here, because it's *fucking crazy*
if you're coming from Haskell like I am. We are defining `cycleNats` by giving
two projections *out of it!* The `head` projection is easy to fill in:

```agda
cycleNats : Nat -> Nat -> Stream Nat
Stream.head (cycleNats _ x) = x
Stream.tail (cycleNats N x) = ?
```

but in the tail case, we want to wrap around from `x = zero` back to `x = N`.
Thus, we can do a usual, everyday **pattern** match on `x`:

```agda
cycleNats : Nat -> Nat -> Stream Nat
Stream.head (cycleNats _ x) = x
Stream.tail (cycleNats N zero) = ?
Stream.tail (cycleNats N (suc x)) = ?
```

and can now give the `tail` projections of `cycleNats` in terms of `cycleNats`:

```agda
cycleNats : Nat -> Nat -> Stream Nat
Stream.head (cycleNats _ x) = x
Stream.tail (cycleNats N zero) = cycleNats N N
Stream.tail (cycleNats N (suc x)) = cycleNats N x
```

Amazingly, Agda accepts this program.

So what happened here? We defined a function that produces a coinductive type
indirectly, by giving the projections *out* of the function. The copatterns
build new function heads, in which we can do everyday pattern matching to help
refine the cases further.

For the sake of comparison, I wanted to write `cycleNats` without copatterns,
just to get a sense for it:

```agda
{-# TERMINATING #-}
cycleNats' : Nat -> Nat -> Stream Nat
cycleNats' N zero = zero :> cycleNats' N N
cycleNats' N (suc x) = suc x :> cycleNats' N x
```

For arcane reasons I don't understand, I need to mark `cycleNats'` as
`TERMINATING` (but it's not) in order for Agda to let me do any reasoning over
it.

Presented like this, the copattern version is definitely doing some work; it
lets us factor out the shared logic for defining the `head`. The copattern
version doesn't yet feel natural to me, but that might be a byproduct of having
my brain stuck in Haskell land for the better part of a decade.


## Lift Instances over Newtypes

We can write `Monad`s in Agda:

```agda
record Monad (M : Set -> Set) : Set where
  constructor is-monad
  field
    pure : {A : Set} -> A -> M A
    _>>=_ : {A B : Set} -> M A -> (A -> M B) -> M B
```

and then define the `State` monad:

```agda
State : Set -> Set -> Set
State S A = S -> S × A

Monad-State : {S : Set} -> Monad (State S)
pure Monad-State a s = s , a
_>>=_ Monad-State ma f s =
  let s' , a = ma s
   in f a s'
```

where we have used a copattern to define the `Monad` methods for `Monad-State`.
But, the paper says, what if we want to implement `State` as a new type, rather
than just a type alias? Fine:

```agda
record State' (S : Set) (A : Set) : Set where
  constructor state
  field
    runState : S -> S × A
```

If we'd like now to give an instance of `Monad` for `State'`, the
straight-forward way is to explicitly use the constructor to build a `State'`:

```agda
Monad-State₁ : {S : Set} -> Monad (State' S)
pure Monad-State₁ a = state λ s -> s , a
_>>=_ Monad-State₁ ma f = state λ s ->
  let s' , a = runState ma s
   in runState (f a) s'
```

This is fine, but we've lost some symmetry with `Monad-State` --- namely, we can
no longer bind `s` on the left side of the equals sign, and we have this noisy
`state` thing everywhere.

Instead, the paper points out, we can use a copattern binding to define `Monad`
for `State' S`. Not, mind you, a copattern to match on the monad methods, but a
copattern to match on `runState` inside of the monad methods:

```agda
Monad-State₂ : {S : Set} -> Monad (State' S)
runState (pure Monad-State₂ a) s = s , a
runState (_>>=_ Monad-State₂ ma f) s =
  let s' , a = runState ma s
   in runState (f a) s'
```

This is *much* nicer than `Monad-State₁`! All of a sudden, `state` is gone, we
can match `s` on the left side of the equals, and the whole thing looks a lot
like `runState` over the original (type-synonymed) version of `Monad-State`.

What's also interesting here is the composition of copatterns; we're defining
`Monad` by giving it in terms of `pure` and `_>>=`, and then defining *those* by
way of observing them via `runState`. I hadn't noticed or appreciated this the
first time through the paper, so it seems like my review project is facilitating
more learning than I would be doing otherwise.


## Fibonacci Numbers

As another example, the authors show us how to construct the Fibonacci numbers.
Consider the following definition, in Haskell:

```haskell
fib : [Int]
fib = 0 : 1 : zipWith (+) fib (tail fib)
```

We can implement this too (but over `Stream Nat`) with copatterns. But first,
let's define `zipWith`:

```agda
zipWith : {A B C : Set} -> (A -> B -> C) -> Stream A -> Stream B -> Stream C
zipWith f sa sb = ?
```

I think I'm starting to get the hang of this, so I tried defining it via a
copattern, and the result was actually quite delightful:

```agda
zipWith : {A B C : Set} -> (A -> B -> C) -> Stream A -> Stream B -> Stream C
head (zipWith f sa sb) = f (head sa) (head sb)
tail (zipWith f sa sb) = zipWith f (tail sa) (tail sb)
```

I really like how the copattern syntax makes clear the homomorpic nature of
`zipWith`.

We can now give a copattern definition for `fib`, where we explicitly copattern
match on the first two terms:

```agda
fib : Stream Nat
head fib = zero
head (tail fib) = suc zero
tail (tail fib) = zipWith _+_ fib (tail fib)
```

Again, notice the composition of copatterns here, in last two cases.

I'm not sure how I feel about this definition; maybe it's clearer to the math
guys, but this one is a little harder for me to wrap my head around.


## Conclusion

The rest of the paper is type theory stuff. There are quite a lot of gammas and
turnstiles, way more than I want to try tackling today. But nevertheless,
*Copatterns* has given me a significantly better understanding of that "weird
record syntax" I'd seen in Agda. I don't yet love the copattern formulation of
every example presented in the paper, but will admit that `Monad-State₂` and
`zipWith` are particularly beautiful under copatterns.

As usual, [the code is on Github.](https://gist.github.com/isovector/37a1c1e21a3618e4f4885482a1454396)

