---
layout: post
title: "FRP in Yampa: Part 2: Arrowized FRP"
date: 2023-12-22 15:16
comments: true
tags: FRP, yampa, haskell, technical, programming, gamedev
---

In the last part, we got a feel for how FRP can help us with real-time
programming tasks, especially when contrasted against implicit models of time.
However, the interface we looked at yesterday left much to be
desired---stringing together long signal functions felt clunky, and since `SF`s
don't form a monad, we couldn't alleviate the problem with do-notation.

So today we'll look at one of Haskell's lesser-known features---arrow
notation---and learn how it can help structure bigger reactive programs.


## Arrows

What an awful, overloaded word we've found ourselves with. Being Haskell
programmers, we're all very familiar with the everyday function arrow `(->)`,
which you should think of as a special case of a more general notion of *arrow.*

Notice how both function arrows (`i -> o`) and signal functions (`SF i o`) have
two type parameters---one for the input side of things, and another for the
output side. And indeed, we should think of these as *sides* of the computation,
where we are transforming an `i` into an `o`.

For our purposes today, we'll want to be very precise when we differentiate
between functions-as-data and functions-as-ways-of-building things. In order to
do so, we will give give ourselves a little type synonym to help differentiate:

```haskell
type Fn i o = i -> o
```

And henceforth, we will use the `Fn` synonym to refer to functions we're
manipulating, reserving `(->)` to talk about combinators for *building* those
functions.

For example, our favorite identity function is a `Fn`:

```haskell
id :: Fn a a
```

We usually give the constant function the type `a -> b -> a`, but my claim is
that it ought to be:

```haskell
const :: a -> Fn b a
```

The subtle thing I'm trying to point out is that there is a (conceptual)
difference between the functions we want to operate on at runtime (called
`Fn`s), and the *combinators* we use to build those functions (called `(->)`.)

Like I said, it's a bit hard to point to in Haskell, because one of the great
successes of functional programming has been to *blur* this distinction.

Anyway, let's return to our discussion of arrows. Both functions and `SF`s admit
a notion of composition, which allow us to line up the *output* of one arrow
with the *input* of another, fusing the two into a single computation. The types
they have are:

- `(.)   :: Fn b c -> Fn a b -> Fn a c`
- `(<<<) :: SF b c -> SF a b -> SF a c`

Despite our intimate familiarity with functions, this pattern of types with both
an input and an output is quite uncommon in Haskell. Due to the immense
mindshare that the monad meme takes up, we usually think about computation in
terms of monads, and it can be hard to remember that not all computation is
monadic (nor applicative.)

Monadic values are of the shape `M o`, with only a single type parameter that
corresponds (roughly) with the *output* of the computation. That is to say, all
of the interesting computational structure of a monad exists only in its output,
and *never in its input*---in fact, we can't even *talk* about the input to a
monad. What we do instead is cheat; we take the input side of the computation
directly from the function arrow.

If we expand out the types of `(<*>)` and `flip (>>=)`, using our `Fn` notation
from above, they get the types:

- `(<*>)      :: M (Fn i o) -> Fn (M i) (M o)`
- `flip (>>=) :: Fn i (M o) -> Fn (M i) (M o)`

which makes it much clearer that the relevant interactions here are some sort of
distributivity of our monad over the regular, everyday function arrows. In other
words, that monads are cheating by getting their "inputs" from functions.


## What the Hell?

Enough philosophy. What the hell *are* arrows? The example that really made it
stick for me is in the domain of *digital circuits.* A digital circuit is some
piece of silicon with wire glued to it, that moves electrons from one side to
the other---with the trick being that the eventual endpoint of the electrons
depends on their original positions. With enough squinting, you can see the
whole thing as a type `Circuit i o`, where `i` corresponds to which wires we
chose to put a high voltage on, and `o` is which wires have a high voltage at
the end of the computation. With a little more squinting, it's not too hard to
reconceptualize these wires as bits, which we can again reconceptualize as
encodings of particular types.

The point I was trying to make earlier about the distinction between `(->)` and
`Fn` makes much more sense in this context; just replace `Fn` with `Circuit`.



