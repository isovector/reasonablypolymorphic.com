---
layout: post
title: "FRP in Yampa: Part 2: Arrowized FRP"
date: 2023-12-22 22:56
comments: true
tags: FRP, yampa, haskell, technical, programming, gamedev, arrows
---

In the [last part](https://reasonablypolymorphic.com/blog/yampa-frp/index.html),
we got a feel for how FRP can help us with real-time programming tasks,
especially when contrasted against implicit models of time. However, the
interface we looked at yesterday left much to be desired---stringing together
long signal functions felt clunky, and since `SF`s don't form a monad, we
couldn't alleviate the problem with do-notation.

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
Here it makes much more sense to think about the identity circuit:

```haskell
id :: Circuit a a
```

which is probably just a bundle of wires, and the constant circuit:

```haskell
const :: o -> Circuit i o
```

which lets you pick some particular `o` value (at design time), and then make a
circuit that is disconnected from its input wires and merely holds the chosen
`o` value over its output wires.

Anyway. The important thing about digital circuits is that you have infinite
flexibility when you are designing them, but once they're manufactured, they
stay that way. If you chose to wire the frobulator directly to the
zanzigurgulator, those two components are, and always will be, wired together.
In perpetuity.

Of course, you can do some amount of dynamic reconfiguring of a circuit, by
conditionally choosing which wires you consider to be "relevant" right now, but
those wires are going to have signals on them whether you're interested in them
or not.

In other words, there is a strict phase distinction between the components on
the board and the data they carry at runtime.

And this is what arrows are all about.

Arrows are about computations whose internal structure must remain constant.
You've got all the flexibility in the world when you're designing them, but you
can't reconfigure anything at runtime.


## Arrow Notation

Yesterday's post ended with the following code, written directly with the arrow
combinators.

```haskell
onPress :: (Controller -> Bool) -> a -> SF () (Event a)
onPress field a = fmap (fmap (const a)) $ fmap field controller >>> edge

arrowEvents :: Num a => SF () (Event (V2 a))
arrowEvents =
  (\u d l r -> asum [u, d, l r])
    <$> onPress ctrl_up    (V2 0 (-1))
    <*> onPress ctrl_down  (V2 0 1)
    <*> onPress ctrl_left  (V2 (-1) 0)
    <*> onPress ctrl_right (V2 1    0)

snakeDirection :: SF () (V2 Float)
snakeDirection = arrowEvents >>> hold (V2 0 1)

snakePosition :: SF () (V2 Float)
snakePosition = snakeDirection >>> integral
```

While technically you can get anything done in this style, it's a lot like
writing all of your monadic code directly in terms of `(>>=)`. Possible
certainly, but indisputably clunky.

Instead, let's rewrite it with arrow notation:

```haskell
{-# LANGUAGE Arrows #-}

snakePosition :: SF () (V2 Float)
snakePosition = proc i -> do
  u <- onPress ctrl_up    $ V2 0 (-1) -< i
  d <- onPress ctrl_down  $ V2 0 1    -< i
  l <- onPress ctrl_left  $ V2 (-1) 0 -< i
  r <- onPress ctrl_right $ V2 1    0 -< i

  dir <- hold $ V2 0 1 -< asum [u, d, l r]
  pos <- integral -< dir

  returnA -< pos
```

Much tidier, no? Reading arrow notation takes a little getting used to, but
there are really only two things you need to understand. The first is that
`proc i -> do` introduces an arrow computation, much like the `do` keyword
introduces a monadic computation. Here, the input to the entire arrow is bound
to `i`, but you can put any legal Haskell pattern you want there.

The other thing to know about arrow notation is that `<-` and `-<` are two
halves of the same syntax. The notation here is:

```haskell
  output <- arrow -< input
```

where `arrow` is of type `SF i o`, and `input` is any normal everyday Haskell
value of type `i`. At the end of the day, you bind the result to `output`, whose
type is obviously `o`.

The mnemonic for this whole thing is that you're shooting an arrow (of bow and
arrow fame) from the input to the output. And the name of the arrow is written
on the shaft. It makes more sense if you play around with the whitespace:

```haskell
  output   <-arrow-<   input
```

More importantly, the name of that arrow can be any valid Haskell expression,
including one with infix operators. Thus, we should parse:

```haskell
  u <- onPress ctrl_up $ V2 0 (-1) -< i
```

as

```haskell
  u <- (onPress ctrl_up $ V2 0 (-1)) -< i
```

What's likely to bite you as you get familiar with arrow notation is that the
computations (the bits between `<-` and `-<`) exist in a completely different
*phase*/*namespace* than the inputs and outputs. That means the following
program is illegal:

```haskell
  proc (i, j) -> do
    x <- blah  -< i
    y <- bar x -< j
    ...
```

because `x` simply *isn't in scope* in the expression `bar x`. It's the
equivalent of designing a circuit board with `n` capacitors on it, where `n`
will be determined by an input voltage supplied by the end-user. Completely
nonsensical!


## Wrapping Up

That's all for today, folks. The day caught me by surprise, so we'll be back
tomorrow to talk about building state machines in Yampa---something extremely
important for making real video games.

