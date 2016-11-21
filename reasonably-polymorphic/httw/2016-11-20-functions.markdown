---
layout: post
title: Functions
date: 2016-11-20 20:00
comments: true
tags:
---

In the last chapter, we attempted to translate our latches (machines which
"remembered" the past) into symbolic computations. We ran into problems when we
noticed that attempting to evaluate an expression containing such a latch
resulted in an infinite expansion -- the expression never simplified down to a
value. We investigated, and realized that the problem was that our machines
weren't pure functions -- their outputs weren't always the same for a given
input.

We'd like to reconcile this, by finding ways of describing machines as symbolic
computations, but allow them to still change depending on the past. The eventual
solution to this problem is for us to come up with some way of describing a
"context" in which such computations should be run. We can then describe the
output of a latch machine as one whose context depends on the past, and our
problems will be solved.

But we're not ready to do that yet. Before we can dive in and directly work on
that problem, we have one more kind of *type* to look at.



## Function Types

Recall that we have a notation for describing the "interfaces" of machines,
which we called their **function signatures**, or just **signatures** for short.
As an example, the signature of `add1` was this:

```
add1 : Bool -> Bool -> Bool -> (Bool, Bool)
```

Our strategy for reading these things was to take the very last type, the one
after the final arrow (`->`), and to call that the *output*. The remainder of
the signature was the inputs, each separated by an arrow.

Such a convention seemed rather suspicious, even when we first looked at it.
Surely the notation should make a better distinction between things that were
inputs and things that were outputs. Today we'll look at the reasoning behind
why this notation is what it is, and related things that that knowledge affords
us.

A few chapters back, we looked at some *constructions on types* -- ways of
building more complicated types out of types we already had. We looked at two
such examples: the *product* type `(a, b)` and the *sum* type `Either a b`.
Product types corresponded to some intuition of "and" between types, and
conversely, sum types were more of an "or" sort of deal.

As it happens, there is one more construction on types. It's called the
**function type** and it looks like this `a -> b`. A function type from `a -> b`
corresponds *exactly* with your intuitions of "a machine which takes an input of
type `a` and gives back some output of type `b`". Of course, if this is a type,
it must have some value, and the values of function types are exactly the
machines with those signatures.

For example, if we are looking for a type `Bool -> Bool`, one potential
candidate is the machine `not`. Why? Because `not` is a function that takes a
`Bool` as an input, and outputs a `Bool`. Therefore its type is `Bool -> Bool`,
and we can write the entire thing as

```
not : Bool -> Bool
```

which, again, corresponds *exactly* to how we've been working with machines thus
far. One question remains though, if a function type is of the form `a -> b`,
what's up with things like `add1`, whose type is `Bool -> Bool -> Bool -> (Bool,
Bool)`?

In the same way that we can combine product types with themselves (eg. `(Bool,
((Nat, Unit), Nat))`), we can also combine function types with themselves.
However, as we will shortly see, the order in which we combine them *does*
matter. When there are no explicit parentheses in a function type, we assume
they associate from the right. This means that `Bool -> Bool -> Bool -> (Bool,
Bool)`, with parentheses added, is this:

`Bool -> (Bool -> (Bool -> (Bool, Bool)))`

Writing these parentheses out explicitly gives us some insight into how a
machine can take more than one input. Because a function type is always of the
form `a -> b`, that means any particular type can take only one input, but we
can "cheat" by nestling functions inside of one another.

If `a -> b` can be described in words as the type of "a machine which takes an
`a` as input, and returns a `b` as output", then `a -> (b -> c)` should be
described as the type of "a machine which takes an `a` as input, and *outputs a
machine* that takes a `b` as input, and outputs a `c`."

What? A machine that "outputs a machine"? That sounds sort of crazy, but it
shouldn't be too large of a stretch. So far, because of polymorphism, our
machines have already been capable of outputting arbitrary values. All we've
done here is acknowledged that *machines themselves are values*.

This is an enormously important concept, so take a few minutes to digest it. By
treating machines as values, we're doing away with our old tacit
misunderstanding that values and transformations of values were *fundamentally
different things*. Remember the lesson of parsimony: whenever we can make two
seemingly distinct things out of one simpler thing, we should do so.

Moving back to continue our look at nested function types, we can create
machines that require multiple inputs by building them something like this:

```{#currying}
circuit = atop newFrame $ labeled "And'" $ runCircuit $ void $ do
  a <- liftDia $ (\x -> wireLabel "a" ||| x # scaleX 2) <$> wire
  b <- liftDia $ (wireLabel "b" |||) <$> wire
  and <- liftDia $ (\x -> vcat [ssvspacer, x ||| inputWire ||| wireLabel "c" ||| sspacer # scaleX 2, ssvspacer]) <$> andGate
  assertSame a (Out 0) and (In 0)
  assertSame b (Out 0) and (In 1)
  return ()

newFrame = rect 2.15 1.3 # lw veryThick
```

In this diagram, `And'` is a machine which takes an `a`, and then outputs a
machine which takes a `b` and returns a `c`. Under this scheme, the `a` provided
to the outer-level machine effectively becomes "constant", and does not change
afterwards. This suggests we should be able to fill in the inputs one-at-a-time
to a machine defined in this fashion. For example, imagine we have this
function:

```
addition : Nat -> (Nat -> Nat)
addition a b = a + b
```

We can now provide these inputs one at a time. That means, in effect, we can
"specialize" this machine, so that it is less general:

```
addSeventeen : Nat -> Nat
addSeventeen b = addition 17 b
```

This trick is known as **currying**, and is named after Haskell Curry, the man
who discovered that this is both a thing we *can* do, and a thing we'd actually
*like* to do. Eventually we'll run out of nested machines, and we'll just get a
usable output value back.

> Takeaway: To *curry* a function is to provide inputs to it one-at-a-time.



## Higher Order Functions

The notion that machines are just values to be passed around at will is a very
empowering one. Not only can we *return machines as outputs*, but we can also
*take them as inputs*. If we do both at once, we can *transform machines into
other machines*, which is a very powerful trick indeed.

A simple example of this is one of "creating adapters". Maybe you have a
function that is in the "wrong shape" to be plugged in somewhere, and so you
need to get it into the right form somehow. This is the logical equivalent of,
say, taking a hacksaw to your electrical plug in order to get it to plug into
something it maybe shouldn't have. Fortunately, the logical case of doing this
is always safe, as guaranteed by our type system.

As a simple example, let's say we have a function of the form `a -> (a -> b)`.
From here on out, most of our types will be polymorphic, since we're just
manipulating the shape of the functions, and we don't really care what actual
types they take. So we have a function of type `a -> (a -> b)` but we want to
get it into the form `a -> b`. If we don't know what type `a` is (because it's
polymorphic and could be *anything*), then we can't *curry* this function to get
rid of one of the `a`s. Instead, we need another approach.

What we need, is a function to transform our function into the right "adapter"
shape. Something of this form:

```
adapter : (a -> (a -> b)) -> (a -> b)
```

It turns out that there is exactly one function value with this type. It looks
like this:

```
intoBoth : (a -> (a -> b)) -> (a -> b)
intoBoth machine = adapted
  where
    adapted : a -> b
    adapted a = machine a a
```

`intoBoth` is a **higher-order** machine, which means it is a machine that
*operates on machines*. It takes a function of type `a -> (a -> b)`, and gives
back a machine of type `a -> b`. It does this by *binding* the input machine to
`machine`, and then giving back a machine defined in the *where-block*, called
`adapted`.

Remember, anything defined in a *where-block* keeps all of the bindings
bound above it, so `adapted` knows about the `machine` given to `intoBoth`. But
`adapted` is its own machine, which takes some binding `a`, and applies it to
*both* of the inputs in `machine`. Try tracing which type every value has in
this definition, and you'll see that everything checks out. It's odd, but
kosher.



## Revisiting Composition

We have one last interesting *higher-order* function to look at before ending
this chapter. It's a machine which formalizes the concept of "composition" we've
been using so far -- that we can combine machines together to get new machines.
If you think about it, this is nothing more than a transformation over machines,
and as such, should be representable as a *higher-order* machine.

```
compose : (a -> b) -> (b -> c) -> (a -> c)
compose m1 m2 = combined
  where
    combined : a -> c
    combined a = m2 (m1 a)
```

Don't let `compose`'s type signature scare you. There are certainly a lot of
arrows, and three (3!) type variables! But it's really not so bad. The type
signature says that "`compose` is a function that takes a function of type `a ->
b`, and another function of type `b -> c`, and gives back a function of type `a
-> c`.

How does it do that? Well obviously it just hooks up the *output* of the first
machine to the *input* of the second one. `compose` defines a lemma machine,
`combined`, which takes an input of type `a`, and provides it as an input to
`m1`. It then takes the output of that, and moves it into the input of `m2`.
Because `m2` itself outputs a `c`, `combined` must also output a `c`. And so the
whole thing has the right type, and therefore it must be correct!

Composition of functions turns out to be perhaps the most powerful concept we
will visit in the course of this book -- and indeed, likely ever. However, as
we will see, this is not the only way of composing machines together, and
composition will turn out to be the secret we've been looking for in order to
make machine latches. We will investigate further in the next chapter.

---

## Exercises

1) There are exactly four machines (values) of type `Bool -> Bool`. Build all
   four of their function tables, and write them as symbolic computations.
2) Write a function that curries an `On` into the first input of an `and` gate.
3) Write a function `compose3` that composes three machines together. Its type
   should be `(a -> b) -> (b -> c) -> (c -> d) -> (a -> d)`.

