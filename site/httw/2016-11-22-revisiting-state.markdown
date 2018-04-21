---
layout: post
title: Revisiting State
date: 2016-11-22 09:00
comments: true
tags:
---

We ended last chapter by looking at what does it mean for something to be a
*Kleisli category*, and found ourselves on a cliffhanger regarding the Kleisli
nature of reality itself. We showed how choosing some type constructor `m`, and
a pair of functions `inject : a -> m a` and `composeK : (a -> m b) -> (b -> m c)
-> (a -> m c)` resulted in us saying that `m` was *Kleisli*.

This notion can be formalized into the following claim in symbolic computation:

```
class Klesili m where
  inject   : a -> m a
  composeK : (a -> m b) -> (b -> m c) -> (a -> m c)
```

which tells us exactly what we said above. It should be read as

> There is a `class` of patterns, called `Kleisli`, which binds a type
> constructor variable `m`. In order for this to be a pattern, the type
> constructor `m` *must* support two functions: `inject` and `composeK`.

We can now "prove" to the symbolic computation that `Maybe` and `Identity` are
*Kleisli* by making claims of the form:

```
instance Kleisli Maybe where
  inject a      = injectMaybe a
  composeK m1 m2 = composeMaybe m1 m2
```

```
instance Kleisli Identity where
  inject a       = injectIdentity a
  composeK m1 m2 = composeIdentity m1 m2
```

The word `instance` is short for "is an instance of the pattern". We say that,
for example, this `instance Kleisli Maybe` statement **is witness to** the fact
that `Maybe` is *Kleisli* -- meaning, that `instance Kleisli Maybe` is a
**proof** that `Maybe` is *Kleisli*. It's a proof because it lists all of the
necessary functions in one place.

Before we get started in earnest, it's helpful to see how being an instance of
the `Kleisli` pattern can be useful. If we stick to our original intuition
behind type constructors being "containers". we can use a `Kleisli` proof to
"change the thing inside a container":

```
map : Kleisli m => (a -> b) -> m a -> m b
map f ma = bind ma m1
  where
    m1 : a -> m b
    m1 = compose f inject

    bind : m a -> (a -> m b) -> m b
    bind ma f = (composeK (always ma) f) Unit

    always : x -> (y -> x)
    always x _ = x
```

As an example, we can evaluate:

```
map succ (Just 5) = Just 6
```

but

```
map succ Nothing = Nothing
```

The exact construction of `map` here isn't necessarily the point, but it shows
off some interesting things. The first of which is our new syntax: `map :
Kleisli m => (a -> b) -> m a -> m b` which means "the `map` function exists as
`(a -> b) -> m a -> m b` *whenever `m` is Kleisli*." The reason this is can be
so is that we defined `map` only using lemmas we could derive with `inject` and
`composeK`, which we know only exist if `m` is *Kleisli* (because their
existence is what makes something *Klesili*).

This fat arrow `=>` should be read as "implies that we have", and should be
taken to be a delimiter between *constraints necessary for the function to
exist*, and the actual types in the signature.

What you should takeaway from the `map` example is that we can use `class`es of
patterns to describe machinery which is polymorphic, but need not exist for
*all* types. We do this by defining our polymorphic thing in terms of features
that are provided to us by having a *witness* that our type is an `instance` of
a particular pattern.

Another way of saying that is if we can define something in terms of nothing but
the `Klesili` functions, then it *must* exist for anything which is *Kleisli*.
Makes sense, really. `map` is one such definition.



## Revisiting State

Seemingly many moons ago we discovered that the formulation behind our stateful
machine latches wasn't "pure", and thus couldn't ever be evaluated as a symbolic
computation. This was particularly upsetting, because we were capable of doing
it with machine diagrams (even if we were technically cheating), but our system
that was supposed to be the latest and greatest new hotness wasn't capable of
doing it.

That changes now. We had to jump several hoops in order to have all of the
necessary conceptual tools in order, but we're now ready to tackle stateful
computations.

The question becomes "how can we model state?", and it's not a particularly hard
thing to answer. A computation that runs in a stateful context must do two
things: it must be dependent on some state, and it produces some output which
can change depending on that state. In the process, this computation can even
change that state.

```{#simple}
circuit = labeled "Hold" $ runCircuit $ void $ do
  or <- liftDia orGate
  c <- liftDia con
  input <- liftDia wire
  done <- liftDia wire
  orOut <- liftDia wire
  orDown <- liftDia $ scale 2 <$> vwire
  assertSame or (In 0) input (Out 0)
  assertSame or (Out 0) orOut (In 0)
  assertSame orOut (Out 0) orDown (In 0)
  assertSame orOut (Out 0) done (In 0)
  assertSame c Split orOut (Out 0)
  b <- aligning bend Split (or, In 1) (orDown, Out 0)
  arr (b, Split) (or, In 1)
  arr (b, Split) (orDown, Out 0)
```

Recall our `Hold` example. Here, our state is the second input to the `or` gate
-- the resulting computation depends on it. In this case, the state is *always*
updated to be the same as the resulting computation. Really, as far as the
interface to this function is concerned, the stateful wire is an "implementation
detail", in the sense that it isn't part of either the input nor the output of
the computation.

However, it *can* *affect* the computation, and this is what made our function
impure, and thus gave us so much grief. But when phrased this way, it becomes a
little clearer that indeed this `Hold` machine is a computation *with some sort
of context* -- the context of course being "the current state of that input
wire".

Modeling state is thus a transformation from some "old" state, to a computation
and a "new" state. The word "transformation" in there should tip us off to a
*function type*, and the word "and" points us towards a *product type*. Indeed:

```
type State s a = s -> (a, s)
```

We can interpret this as "`State s a` is the type of a computation which
produces an `a`, using (and potentially updating) some state `s` in the
process."

This `State s a` type is messy, and if we had to sling this state around every
time we wanted to work with it, we'd start hating our lives and probably take up
a new hobby instead. But we have a trick up our sleeves. If we can prove that
`State s` is *Klesili*, then we can use *Kleisli composition* to rig up all the
correct handling of our state for us and spare us the gritty details.



## The Kleisli Category of State

Before we can even begin to think of using *Kleisli composition* to solve any
problems for us, we must first prove that we have an `instance` of the `Kleisli`
pattern around.

The easiest step is usually to write `inject : a -> State s a`, so we'll start
there. Technically there are a few laws that any `instance Kleisli` must follow,
but for the most part they boil down to "don't do anything arbitrarily stupid".
We'll look into them later when we look at the more general notion of
*categories*. For the time being, we'll just write the "obvious" `inject`, and
that will turn out to be what we want.

How do we write `inject`? Well, what do we have, and what do we want? We have an
`a`, and we want a `s -> (a, s)`. Expanding this out, the type of `inject` is `a
-> s -> (a, s)`, which is "given an `a` and an `s`, give back a pair of an `a`
and an `s`".

Seems easy enough.

```
injectState : a -> State s a
injectState a s = (a, s)
```

> *Point of order*: Even though we're writing `State s a` in the type signature
> here for `injectState`, it really is just a `s -> (a, s)`, which is why
> our implementation of `injectState` takes *two* inputs, rather than just one.

Great! So we have `inject`. All that's left now is `composeK`. Let's expand out
its type as well to see if anything interesting comes out of it:

```
composeState : (a -> s -> (b, s))
            -> (b -> s -> (c, s))
            -> (a -> s -> (c, s))
```

At a first glance, it seems like we should be able to use the same trick of
pulling the `s` out of the `State s` definition, but this function signature is
misleading. The first two inputs we're given into `composeState` are functions
which *require* `s`s, they don't give us anything we can use. Instead, it's
informative to drop the parentheses around the output, which if you recall, is
completely legal and fair game:

```
composeState : (a -> s -> (b, s))
            -> (b -> s -> (c, s))
            -> a
            -> s
            -> (c, s)
```

Without the parentheses, it's clear that we do in fact have an `s` to play with
-- it was just hiding in our *output*. This sounds crazy, until you recall that
this is sort of exactly why we wanted to track state in the first place -- so
that our machines could depend somehow on their output. Kleisli machinery gives
us a way of doing this, by hiding details *inside of the machine's output*. It's
wild, but it actually works, so it's hard to argue with.

And so we're ready to write a definition of `composeState`. We'll take the `a`
and the `s` we're given, pass them into our `m1 : a -> s -> (b, s)`, where the
output of `m1` is a `b` and a *new* state `s`, which we can then pass into `m2`.

```
composeState : (a -> s -> (b, s))
            -> (b -> s -> (c, s))
            -> a
            -> s
            -> (c, s)
composeState m1 m2 a state = (c, finalState)
  where
    (b, newState)   = m1 a state
    (c, finalState) = m2 b newState
```

With that, we can now prove that `State s` is *Kleisli*:

```
instance Kleisli (State s) where
  inject   = injectState
  composeK = composeState
```

Finally we're done! Well, sort of. The attentive reader will notice that we have
provided no means for machines to actually get the *value* of the state context
they're running in. Having a state isn't very useful if you're unable to
actually use it.

We therefore provide two additional functions to the *Kleisli* category of
`State s`. The first is `get : State s s`:

```
get : State s s
get state = (state, state)
```

`get` provides access to the state. Notice its strange type: `get : State s s`.
It has no inputs, and so we can consider `get` to be a constant "value" of type
`State s s`, in the same way that `41 : Nat`. Recall that `State s a = s -> (a,
s)`, and so `get` is really giving us back the internal state in the place of
"`a`", which we can then use *Kleisli composition* to do interesting things
with.

Similarly, `get`ting the current state isn't very helpful if you're unable to
change it. Behold `set`:

```
set : s -> State s Unit
set newState _ = (Unit, newState)
```

We output a value of `Unit` to indicate that we didn't have anything better to
output. Outputting a `Unit` is the least interesting thing we can possibly do --
recall that `Unit` tells us literally nothing, because we always can pull one up
from nothingness. A *machine* which outputs `Unit` is thus somewhat interesting.
It's not outputting `Unit` because that's a useful thing to tell us, so that
means that any machine which outputs `Unit` in a *Kleisli* context must have
*actually done something*. It must have somehow *modified* the context, because
that's the only other thing that *Kleisli* machines can do (other than return
values). It's a neat convention, and something to keep your eyes peeled for.

Finally, armed with all of these things, we're ready to write `Hold` from above:

```
hold : Bool -> State Bool Bool
hold val = bind get withState
  where
    bind : State Bool a -> (a -> State Bool b) -> State Bool b
    bind ma f = (composeK (always m) f) Unit

    always : x -> (y -> x)
    always x _ = x

    withState : Bool -> State Bool Bool
    withState s = bind (set (or val s)) (always get)
```

Egads. What a terrible eyesore. It's gruesome, but it turns out to actually
work, and that's the important part. Bet it makes you want to start finding a
new hobby though, am I right? Don't worry, in the next chapter, we'll expand the
syntax of our symbolic computations to something *Kleisli-aware* -- which is to
say "doesn't make you want to rip your own eyes out with a rusty spoon when
doing these kinds of things." Hold onto your eyes until the next chapter, and
we'll make everything better.

---

## Exercises

1) Work through the definition of `map : Kleisli m => (a -> b) -> m a -> m b`
   above. If you think of `always : x -> (y -> x)` as a function which always
   just ignores its second input and returns its first, it kind of looks like
   the right adapter we need in order to start working with `composeK`.
2) Work through the definition of `hold : Bool -> State Bool Bool` above. Notice
   how it uses the same `bind` lemma that `map` did.
3) Define a function `modify : (s -> s) -> State s Unit` which takes a machine
   that describes how to modify the internal state.
