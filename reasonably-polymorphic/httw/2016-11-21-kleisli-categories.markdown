---
layout: post
title: Kleisli Categories
date: 2016-11-21 20:00
comments: true
tags:
---

In the last chapter, we came across a frankly startling realization -- that our
machines need not be differentiated from the values they manipulate. As it turns
out, our symbolic computations are powerful enough to allow machines to
themselves manipulate other machines. We called such things *higher-order
machines*, and we studied some of their properties. In particular, we looked at
how this strange bedfellow, our old friend *machine composition*, turned out to
be nothing more than a specific example of a higher-order machine.

Such an occurrence should be an excuse to celebrate. Not only have we come up
with a more *parsimonious* formulation of our toolset, but we have also
reconciled seemingly-disjoint concepts. Our world-view is a little nicer now
than it was, and, having discovered that these two things are one-and-the-same,
we pave the way for finding other examples of the same pattern.

As promised, there are more ways of composing machines together than just
`compose : (a -> b) -> (b -> c) -> (a -> c)`, and the pattern hiding behind them
will form the tool we need to create machines capable of remembering the past.



## A Pattern of Failures

Some time ago, we discussed a polymorphic type, called `Maybe a`. As you might
recall, `Maybe a` is defined as such:

```
type Maybe a = Just a
             | Nothing
```

and it represented a value of type `a` which *may or may not be there*. A
missing value was represented as `Nothing`, but a value which did in fact exist
was represented by `Just value`, for some `value : a`.

We originally used a `Maybe Bool` to represented whether we wanted to read or
write from a `Snap` machine (the `Bool` part), or whether we wanted to leave the
latch alone (a `Nothing` input).  And so, as an input, a `Maybe a` corresponds
to something which may or may not be desired.

Remember, we also made a type `Nat`, which corresponded to the natural numbers
(0, 1, 2, and so on). It was defined like this:

```
type Nat = Zero
         | S Nat
```

which means that a `Nat`ural number is either `Zero`, or the successive number
of a `Nat`ural number. Constructing a `succ` function to get the successive
number of a given input is rather easy:

```
succ : Nat -> Nat
succ a = S a
```

but note that it's much harder to get the `prev`ious number:

```
prev : Nat -> Nat
prev (S num) = num
prev Zero    = ???
```

The issue of course, is that in our definition of `Nat`, there *is* no number
that is `prev`ious to `Zero`! `Zero` is the first number, and we can't go back
any further than that! The problem is that sometimes there is no answer to the
question we're asking in `prev`. You could say that *maybe* there is no answer.

And so, as you might imagine, we can use `Maybe` to work backwards:

```
prev : Nat -> Maybe Nat
prev (S num) = Just num
prev Zero    = Nothing
```

We can think of a function which outputs a `Maybe` something as a computation
which could possibly fail. A computation which maybe might not actually produce
any output.

In blunt, `Maybe a` describes an `a` which might go wrong.

What if, for some reason, we wanted to add together two numbers. But, to make
things interesting, we don't want to add the numbers we're given -- we'd live to
add the `prev`s of the numbers we're given. Now obviously, this is a computation
that can go wrong. If either of the numbers we are given to add together are
`Zero`, clearly there is no `prev` to take, and so the entire computation must
fail.

```
addPrevs : Nat -> Nat -> Maybe Nat
addPrev a b = addMaybeNats (prev a) (prev b)
  where
    addMaybeNats : Maybe Nat -> Maybe Nat -> Maybe Nat
    addMaybeNats (Just ma) (Just mb) = Just (ma + mb)
    addMaybeNats _         _         = Nothing
```

Here, we've defined our function `addPrevs` in terms of a lemma `addMaybeNats`,
which adds two `Nat`s together if they're both tagged with `Just` -- which is to
say that they both definitely exist. The result is also tagged with a `Just`. In
any other case (either or both of the inputs are `Nothing`), `addMaybeNats`
gives back a `Nothing`.

We can view `addPrevs` as a kind of machine composition -- it's made out of two
machines (`prev`), either of which can fail. `addPrevs` itself inherits this
"can fail" property from the submachines from which it is built. However, it
should be pointed out that this is *not* the usual kind of composition with
which we are familiar.

Our usual composition was of the form

```
compose : (a -> b) -> (b -> c) -> (a -> c)
```

which is to say that if you gave it a machine from `a -> b` (read: "from `a` to
`b`") and another machine from `b -> c`, `compose` could combine them for you
into a single machine which was from `a -> c`. It did this by gluing the output
of the first machine to the input of the second.

However, in the case of our `addPrevs`, we want a composition that is somehow
"smart enough" to handle failure. A method of composition that knows that if one
of the sub-machines fails, the entire thing has to fail as well.

In short, what we want is a machine:

```
composeMaybe : (a -> Maybe b) -> (b -> Maybe c) -> (a -> Maybe c)
```

`composeMaybe` is a machine which connects a machine `a -> Maybe b` to a machine
`b -> Maybe c`. It does this by attempting to run the first machine, and *if it
succeeds*, it passes connects the successful output from the first machine to
the input of the second machine. The resulting machine takes an `a` and outputs
a `Maybe c`, where the computation can spit out a `Nothing` if either the first
*or* the second machine fails.

As a machine diagram, it might look something like this:

```{#kleisli}
circuit = (||| sspacer) $ labeled "ComposeMaybe[M1, M2]" $ runCircuit $ void $ do
  m1 <- liftDia $ machine' [inputWire, nothing] ["a", ""] ["OK", "Fail"] "M1"
  m2 <- liftDia $ machine' [inputWire, nothing] ["b", ""] ["OK", "Fail"] "M2"
  m1out <- liftDia $ scaleX 1 <$> wire
  m2out <- liftDia $ (\x -> x # scaleX 2 ||| wireLabel "Just c") <$> wire
  m1fail <- liftDia wire
  m1down <- liftDia vwire
  m2fail <- liftDia wire
  m2down <- liftDia vwire
  m2con <- liftDia con
  m2done <- liftDia $ (||| wireLabel "Nothing") <$> wire
  connecting [ (m1, undefined, Out 0)
             , (m1out, In 0, Out 0)
             , (m2, In 0, Out 0)
             , (m2out, In 0, undefined)
             ]
  connecting [ (m1, undefined, Out 1)
             , (m1fail, In 0, Out 0)
             , (m1down, In 0, Out 0)
             ]
  connecting [ (m2, undefined, Out 1)
             , (m2fail, In 0, Out 0)
             , (m2down, In 0, Out 0)
             , (m2con, Split, Split)
             , (m2done, In 0, undefined)
             ]
  arr (m1down, Out 0) (m2con, Split)
```

where only one of the `Just c` or `Nothing` wires will be raised at any given
time, depending on whether or not the composed machine succeeded.

We can actually write such a thing as a symbolic computation as well:

```
composeMaybe : (a -> Maybe b) -> (b -> Maybe c) -> (a -> Maybe c)
composeMaybe m1 m2 = composed
  where
    composed : a -> Maybe c
    composed a = bridge (m1 a)

    bridge : Maybe b -> Maybe c
    bridge (Just b) = m2 b
    bridge Nothing  = Nothing
```

which, as promised, is another way we can combine two machines.



## Kleisli Categories

This function, `composeMaybe : (a -> Maybe b) -> (b -> Maybe c) -> (a -> Maybe
c)` is what's known as a **Kleisli composition**. A *Kleisli composition* is a
way of combining two machines which output things that are not just plain types
(they are of the form `Maybe a`, for example, rather than just `a`).

In order for such a thing to truly be a *Kleisli composition*, we must have one
additional function, which we will call `inject`. For `Maybe`, it's really
simple:

```
injectMaybe : a -> Maybe a
injectMaybe a = Just a
```

All together, the combination of these three things: `Maybe`, `compose` and
`inject` form what's known as a **Kleisli category**. *Kleisli categories* will
turn out to be a huge amount of interest to us in the near future. Because of
the fact that the functions `composeMaybe` and `injectMaybe` exist, we say that
"`Maybe` is *Kleisli*".

If "`Maybe` can be *Kleisli*", maybe other things can be as well? And indeed,
being *Kleisli* is nothing more than an interesting pattern that forms around
certain *type constructors*, such as `Maybe`. We will look at *why* Kleisli
categories are interesting in a moment, but for now, the important part is
merely that there is a common pattern in what it means to be *Kleisli*.

As a rather contrived example, we can look at a new type:

```
type Identity a = Identity a
```

`Identity a` is a boring thing, it is merely a wrapper around `a`, but serves no
other purpose. Observe that we can write `injectIdentity` and `composeIdentity`
functions:

```
injectIdentity : a -> Identity a
injectIdentity a = Identity a
```

and

```
composeIdentity : (a -> Identity b) -> (b -> Identity c) -> (a -> Identity c)
composeIdentity m1 m2 = composed
  where
    composed : a -> Identity c
    composed a = bridge (m1 a)

    bridge : Identity b -> Identity c
    bridge (Identity b) = m2 b
```

As such, the combination of `Identity` (note, *not* `Identity a`),
`injectIdentity` and `composeIdentity` form a *Kleisli category*, and so we can
say too that `Identity` is also *Kleisli*.

So. We have identified a common pattern: a type constructor which takes a single
type variable (call it `m` for now), a function `inject : a -> m a`, and a
function `compose : (a -> m a) -> (b -> m c) -> (a -> m c)`. Any `m` which
satisfies such things is *Kleisli*. But *what does that mean?*

It means that we have those functions: `inject` and `compose` for our type
constructor `m`.

Sorry, that was cheeky of me. The question we really wanted to ask was "why
should we care whether something is *Kleisli* or not?"

Well, being *Kleisli* means that we have some notion of what it means to
"compute in a some kind of environment or context." The particular
context/environment we're computing in depends on our choice of `m`, and for
every `m`, we will get a different environment. The environment behind the
Kleisli-ness of `Maybe` is "computations which might fail", while the
environment behind `Identity` is "computations without any particular context".

In that light, `Identity` sounds stupid, and it is. The key point is that even
if we have an environment, we can choose to ignore it.

All of this should be oddly reminiscent of our earlier discussions of the
`RealWorld` -- computations which take place "in the context of reality", as
opposed to our toy logic world that we've been working in thus far. As it turns
out, **reality itself is *Kleisli***, and this fact is our first glimpse into
the mindset that maybe all of this isn't merely just a toy logic world after
all.

