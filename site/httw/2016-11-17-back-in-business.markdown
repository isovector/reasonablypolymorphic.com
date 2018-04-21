---
layout: post
title: Back in Business and Better than Ever
date: 2016-11-17 16:00
comments: true
tags:
---

In the last few chapters, we've been building something I like to call
"higher-order machinery" -- things that are not machines themselves, but are
useful for building machines. The majority of our higher-order machinery took
the form of developing our *type system* -- a framework we've built in order to
describe the interfaces to our machines, and to help us reason about how we can
connect machines together. As we saw in the last chapter, having a developed
type system also afforded us the capability to make *more semantically
meaningful* machines.

We've taken quite a detour, but it's finally time to get back to our stated task
at hand: building a computer. Before we get started in earnest, let's begin by
moving all of our existing machinery from machine diagrams to symbolic
computations. We'll quickly work our way back through the material we've already
covered. Try to follow along with each construction, and if you feel up to the
challenge, try your hand at converting one on your own.



## Simple Adding

The first interesting machine we made was `Add`, a machine which added three
wires together, and output both the "sum" and the "carry" of those three wires.

```
add1 : Bool -> Bool -> Bool -> (Bool, Bool)
add1 a b cin = (sum, carry)
  where
    sum   = xor (xor a b) cin
    carry = or (or (and a b)
                   (and a cin))
               (and b cin)
```

How much easier was that than our machine diagrams? It takes a little chasing to
keep everything in your head, but you have to admit it certainly takes up less
space.

I pulled a fast one on you there -- did you see it? I said that `add1 a b c =
(sum, carry)`, but what are `sum` and `carry`? Keep looking! They're defined
right afterwards. This convention bears a little explaining, so I'll get to it.
But I promise to keep it short.

In order to simplify our symbolic computations, we can abstract away complicated
patterns and give them a more meaningful name. The way we do this is by writing
equality definitions after the word `where`. Everything in this "where block"
has access to the function's bindings (in this case `a`, `b`, and `cin`), so all
of the `a`s (for example) refer to the *same* input value coming into the `add1`
machine.

The `carry` expression, however, is a bit of a doozy. Whenever possible, I will
attempt to line up sub-expressions so that it's clear what's going on without
needing to count parentheses. This extra spacing has absolutely no meaning in
the symbolic computation whatsoever, it's entirely to aid human comprehension.
An interesting question is a "who would be comprehending this, if not humans?"
and the answer, of course, is that before the end of this book, we will have
"closed the loop" and have written a computer program capable of "understanding"
the exact symbolic computations that make it up. But we're not there yet.



## Adding Nybbles

Let's move forwards and work on migrating our `Add4` machine to a symbolic
computation. Recall that `Add4` was four `Add` machines running in "parallel",
each one receiving the "carry" output from the previous machine.

```
type Nybble = (Bool, Bool, Bool, Bool)

add4 : Nybble -> Nybble -> Nybble
add4 (a1, a2, a3, a4) (b1, b2, b3, b4) = (s1, s2, s3, s4)
  where
    (s1, c1) = add1 a1 b1 Off
    (s2, c2) = add1 a2 b2 c1
    (s3, c3) = add1 a3 b3 c2
    (s4, c4) = add1 a4 b4 c3
```

Before we start with the analysis, let's take a look at a little more notation
first. We have this definition in our "where block": `(s1, c1) = add1 a1 b1
Off`, which uses a technique we'll call **destructuring** or **pattern
matching**. *Destructuring* makes bindings to "smaller pieces" of a large value.
Because the output of each invocation of `add1` is a *product type*, we somehow
need to pull out the individual `Bool`s inside of that type. This is exactly
what *destructuring* does.

We're also pulling apart the products of `Bool`s as our inputs to `add4`,
because we've said that `add4` takes `Nybble`s, and that `type Nybble = (Bool,
Bool, Bool, Bool)`. So the way you should read all of this is that `add4` tears
apart the individual `Bool`s it's given, pairs each of them up, moves the
"carries" between `add1` machines, and then gives you back a product of the
"sums".

Notice how closely all of this logic reflects the original machine diagram:

``` {#nybble_add}
addScale = 0.3
deWire s = mkCon s (In 0) ||| inputWire # scale addScale ||| mkCon s (Out 0)
vdeWire s = (mkCon s (In 0) ||| inputWire # scale addScale ||| mkCon s (Out 0)) # rotate (-1/4 @@ turn)
add n n1 n2 = do
  m <- liftDia $ (# scale addScale) <$> machine ["A", "B", "Cin"] ["Cout", "S"] "Add"
  cin <- liftDia $ vdeWire
  cout' <- liftDia $ deWire
  cout <- liftDia $ vdeWire
  s <- liftDia $ (scale (1 / addScale)) <$> deWire
  assertSame m (Named "Cin") cin (In 0)
  assertSame m (Named "Cout") cout' (In 0)
  assertSame cout' (Out 0) cout (Out 0)
  assertSame m (Named "S") s (In 0)
  arr (n1, (Out n)) (m, (In 0))
  arr (n2, (Out n)) (m, (In 1))
  return (m, cin, cout)
cons s = mkCon s (Out 0) === circle 0.05

circuit = runCircuit $ void $ do
  n1 <- liftDia nybble
  n2 <- liftDia nybble
  (a1, a1in, a1out) <- add 0 n1 n2
  (a2, a2in, a2out) <- add 1 n1 n2
  (a3, a3in, a3out) <- add 2 n1 n2
  (a4, a4in, a4out) <- add 3 n1 n2
  c <- liftDia cons

  arr (a1out, (In 0)) (a2in, (Out 0))
  arr (a2out, (In 0)) (a3in, (Out 0))
  arr (a3out, (In 0)) (a4in, (Out 0))

  assertSame c (Out 0) a1in (Out 0)

  spaceV 1 n1 n2
  liftCircuit $ constrainWith (hsep 2) [n1, a4]
  liftCircuit $ constrainWith (vsep 0.1) [a4, a3, a2, a1]
```

However, if you'll recall, the complexity of this diagram the first time around
gave us the willies and was the inspiration behind our developing of the
multiwire concept.

Indeed, our symbolic computation for `add4` is itself pretty hairy, and *very*
mechanical. You can imagine we might want to make an `add8`, and while there's
nothing *difficult* about constructing such a machine, it would certainly be
tedious and error-prone.


## Types to the Rescue

We solved this problem the first time around by using multiwires, and (although
we didn't know it then) using polymorphism. We said that the semantics of two
multiwires with the same annotation (ie. two values with the same type) being
expanded into a single machine would "make a copy" of the machine for each wire
in the multiwire. To refresh your memory, we drew this diagram:

```{#mw_add_four}
```

So how can we do this with a symbolic computation? Well, polymorphism is the
first thing that comes to mind. It solved our problem last time, so it's a
reasonable thing to try here.

Unfortunately, there's a problem, and that's that our new type system is
stronger than the notion of annotations on multiwires. A "polymorphic" multiwire
was a multiwire where we didn't care how many wires were in it. However, as
we've seen, there are more types than just `Bool` and products of `Bool`, so
when we say "a polymorphic type", we have *far more possibilities* than we ever
did for "polymorphic multiwires".

In other words `Maybe Nat` is a valid instance for a type variable, but `Maybe
Nat` is *not* a valid multiwire.

At the end of the day, what this means is that using any *particular* type is
too specific in order to define an `add` machine that works for any size of
inputs, but a *polymorphic* type is too general. What we really want is some
*restriction* on *which* polymorphic types we're allowed to use.

Or, maybe what we want is a polymorphic type which describes exactly what we
need. Let's take a look at what we can come up with.

```
type List a = Nil
            | Cons a (List a)
```

How should this be interpreted? Well, we can read it like so:

> `List a` is a type, polymorphic in `a`, whose values are either `Nil`
> (nothing; an empty list) or a `Cons`truction of an `a` combined with some
> other `List a`.

Similarly to `Nat`, `List a` is defined *in terms of itself*. Let's look at a
few values of type `List Bool` to get a feel for this new type of ours.

* `Nil : List Bool`
* `Cons On  Nil : List Bool`
* `Cons Off Nil : List Bool`
* `Cons On  (Cons On  Nil) : List Bool`
* `Cons On  (Cons Off Nil) : List Bool`
* `Cons Off (Cons On  Nil) : List Bool`
* `Cons Off (Cons Off Nil) : List Bool`
* ... and so on

At its essence, a `List a` is nothing but some number of `a`s glued together
into a product. The "some number" part of that description is the important
part -- this is exactly the semantic we want for our `add` machine!


## Adding Lists

We now have all the tools necessary for describing `add`. We'll start with its
type annotation:

```
add : List Bool -> List Bool -> List Bool
```

This is very reminiscent of `add1 : Bool -> Bool -> Bool` and `add4 : Nybble ->
Nybble -> Nybble`, which is a good sign. Based on syntactical evidence alone, so
far we have yet to go wrong. We'll continue. What we want is a way to "peel" off
the first element in each list, and use those values as inputs to `add1`.

```
add : List Bool -> List Bool -> List Bool
add (Cons a as) (Cons b bs) = something
```

We use pattern matching (aka. destructuring) to pull off the *head* (first
thing) of each of our lists. However, once we have taken off the heads, we are
left with the "tails" -- the remainder of the things in the list, although this
might be `Nil` if the list only had one element in it to begin with. We bind the
*heads* of the lists to `a` and `b`, and the *tails* of the lists to `as` and
`bs`, which should be pronounced like the plurals of "a" and "b".

We'd like to pass `a` an `b` directly into `add1`, but there's a problem, and
that's that we don't yet have a `cin`. Unfortunately, we don't have an obvious
place to pull one in from, so we cheat and make a lemma machine, one that takes
a `cin` as input:

```
add' : List Bool -> List Bool -> Bool -> List Bool
add' (Cons a as) (Cons b bs) cin = something
  where
    (sum, carry) = add1 a b cin
```

We'd now like to output `add1 a b cin`, but we can't! Why not? Because it
doesn't have the correct type! We want to output a `List Bool`, but the only
`List Bool`s that we have are `as` and `bs`, and we haven't *actually done
anything* with those, so they are unlikely to be the "correct" thing to give
back.

Looking at our old machine diagram again provides a clue for what to do:

```{#mw_add_four}
wireLabel s = topLeftText s # scale textSize # translate (r2 (-0.2, 0.3))
mw l a = mkCon a (In 0) ||| text "}" # scale 0.5 # translateY (-0.003) ||| inputWire ||| wireLabel l ||| inputWire ||| mkCon a (Out 0)
mw' l a = (mkCon a (In 0) <> text "}" # scale 0.5 # translateY (-0.003) # translateX 0.1) ||| inputWire ||| wireLabel l ||| inputWire
deWire s = mkCon s (In 0) ||| inputWire ||| mkCon s (Out 0)
vdeWire s = (mkCon s (In 0) ||| inputWire ||| mkCon s (Out 0)) # rotate (-1/4 @@ turn)

circuit = labeled "AddN" $ runCircuit $ void $ do
  n1 <- liftDia $ mw ":n"
  n2 <- liftDia $ mw ":n"
  m <- liftDia $ machine' [outputMulti, outputMulti, inputWire] [ "A", "B", "Cin" ] [ "S", "Cout" ] "Add"
  assertSame n1 (Out 0) m (In 0)
  assertSame n2 (Out 0) m (In 1)
  cin <- liftDia vdeWire
  cout <- liftDia deWire
  cout' <- liftDia $ scale 1.5 <$> vdeWire
  s <- liftDia $ mw' ":n"
  assertSame m (In 2) cin (In 0)
  assertSame m (Out 1) cout (In 0)
  assertSame m (Out 0) s (In 0)
  assertSame cout (Out 0) cout' (In 0)
  arr (cin, Out 0) (cout', Out 0)
```

You'll notice that there is a wire connecting the *output* of `Add` to the
*input* of `Add`. If we look back at the tools we have available to us in `add'`
to produce a `List Bool`, we notice that `add'` *itself* outputs a `List Bool`.
And so that's where we're going to get ours from.

```
add' : List Bool -> List Bool -> Bool -> List Bool
add' (Cons a as) (Cons b bs) cin = Cons sum (add' as bs carry)
  where
    (sum, carry) = add1 a b cin
```

*Hold on. **What?*** Well, we compute `add1 a b cin`, and then take the `sum` of
that, and `Cons`truct it with the result of calling `add' as bs carry`. This has
the effect of "peeling off" one `Bool` at a time from our `List Bool`s. It
computes the `sum` and `carry` of adding them together, uses the `sum` as a part
of the output `List Bool`, and uses the `carry` as the `cin` for the next time
around.

The clever reader will be wondering "how does this thing ever stop?" The answer
of course is "when we run out of inputs", but the clever reader is correct --
our solution so far doesn't yet cover that. Recall that when we make a function
table, we need to describe the output *for every possible input*. But we haven't
yet described what happens if you have an empty list. In that case, obviously
we won't have one of the wires we need to compute an `add1`, so the only
meaningful `List Bool` we can give back is `Nil`. Capiche?

Our final solution, then is:

```
add' : List Bool -> List Bool -> Bool -> List Bool
add' (Cons a as) (Cons b bs) cin = Cons sum (add' as bs carry)
  where
    (sum, carry) = add1 a b cin
add' _ _ _ = Nil
```

This final line full of underscore says "for any other input, we just want to
give back `Nil`." Remember that our original `Add4` machine simply "dropped" the
final carry, and we decide to do that here as well. It's probably poor
mathematics, but we're worried more about consistency right now.

To now tie a pretty bow around the whole thing, we remember that this `add'`
machine is a lemma, and in fact what we wanted was in fact `add`. We can define
`add` in terms of `add'`:

```
add : List Bool -> List Bool -> List Bool
add as bs = add' as bs Off
```

where we just supply the initial `cin` binding for `add'`.

It's crazy to believe, but all of this stuff we've made actually works! `add` is
now a *general purpose* adder -- capable of computing sums of numbers
arbitrarily large.

In the next chapter, we'll do a few more examples of moving our machine diagram
circuitry into symbolic computations.

---

## Exercises

1) Evaluate the expression `add (Cons On (Cons Off Nil)) (Cons On (Cons On Nil))`
   by hand to get a feel for how this construction actually works.

