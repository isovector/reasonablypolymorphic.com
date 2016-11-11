---
layout: post
title: Constructions on Annotations
date: 2016-11-10 23:00
comments: true
tags:
---

In the last chapter, we built the `Snap*` machine -- a memory cell which
"captures" some polymorphic input, and continuously outputs it until a signal
comes in telling it to capture something new. This is exactly how your computer
remembers the contents of a file when you save it, albeit our `Snap*` machinery
is at a smaller scale. The goal of the next chapter is to fix that and build
real memory blocks for ourselves. The goal for *this* chapter, however, is to
build some abstractions *on top of our multiwire annotations* in order to do
that.

Conceptually, the way we will do this is by putting a bunch of `Snap*` machines
side by side, routing the same polymorphic input into them, and then use the
value of a nybble to help "route" our `S`napshot wire into "the correct
machine." This should somewhat remind you of the work we did on `Demux2`, where
we fed the same input into our `and` games, and used a `Split` machine to route
a switching signal to the correct `and` gate that we wanted. If the details of
this construction aren't fresh in your memory, it might be helpful to review
[Chapter 7 on Multiplexing][multiplexing] again before continuing.

[multiplexing]: /book/multiplexing

In effect, what we want is a demuxer that is *polymorphic* in its `D`estination
wire as well as its value wire. If this were the case, we'd be able to route an
input between $2^n$ destinations (where `:n` is our wire annotation), rather
than just the two ($2^1=2$ when our `D` *isn't* polymorphic) that `Demux2` gives
us.

The black-box machine diagram we want is this:

```{#bb_demux}
circuit = runCircuit $ void $ do
  nIn <- liftDia $ multiIn ":n"
  dIn <- liftDia $ multiIn ":d"
  out <- liftDia $ (\x -> x ||| wireLabel ":(2^d,n)" ||| outputMulti) <$> wire
  -- liftDia $ (\x -> x ||| sspacer # scale 0.5 ||| inputMulti ||| wireLabel ":n") <$> orGate' outputMulti outputMulti
  m <- liftDia $ machine ["A", "D"] [""] "Demux"
  assertSame nIn (Out 0) m (In 0)
  assertSame dIn (Out 0) m (In 1)
  assertSame out (In 0) m (Out 0)
```

Black-box machine diagrams do little more than to tell us the *interface* we
want our machine to have. More specifically, they are useful primarily to give
annotations to any multiwires in our diagram. Here, `Demux` takes an input `A:n`
and another input `D:d`. The output has this weird `:(2^d,n)` annotation, which
we'll discuss shortly.


## Constructions on Annotations

Annotations are interesting beasts -- they describe the general "shape" of what
a multiwire must look like. Of course, at the end of the day, multiwires are
nothing but lots of wires side-by-side, with no real structure for them. These
annotations describe a pattern that exists mostly in our brains.

Whenever you see the word "pattern" in this book (and more generally, whenever
you see patterns in real life), you should immediately begin asking yourself
"how can we abstract this pattern?" How can we describe the same-ness or
different-ness of one pattern compared to another? What are the defining
characteristics of this pattern, that we could use to spot another one?

Once these questions are answered, you begin to be capable of describing all the
*specific instances* of a pattern (eg. train, car, boat, plane, dog sled) as
*instances of the pattern itself* (eg. vehicles). In doing so, you have lost
some specificity, but gained the ability to manipulate and think larger thoughts
about the specific instances that this pattern represents.

And so we find ourselves looking at multiwire annotations as a pattern, because
we'd like to manipulate them. We want to find a means of describing one
annotation in terms of some other one.

The simplest way to do this is to acknowledge that our annotations can be
interpreted as *numbers*, and indeed, this is what they have been so far. Our
nybbles are annotated as `:4`, for example. This suggests we should be able to
perform *algebra* on our annotations. A nybble with an extra wire to store some
auxiliary information might have the annotation `:4+1`, which of course is just
`:5`. More interestingly, our *polymorphic* wire annotated as `:n` might go
through a machine which equips it with a similar auxiliary wire -- the output to
such a machine might be `:n+1`.

If we can add wires, we can probably multiply them too. And indeed, we can.
However, there are two interpretations of what it means to multiply annotations
together. The first is in terms of *numbers*, so `:2*3` is just the annotation
`:6`. The other interpretation is more *structural*. Consider this table:

| | | |
|-|-|-|
| &nbsp; | &nbsp; | &nbsp; |
| &nbsp; | &nbsp; | &nbsp; |

While this table has $6$ cells, it equivalently has $2$ rows of $3$ columns. In
an annotation context, this interpretation would be labeled `:(2,3)`. It's an
interesting construction to think about, because this table metaphor generalizes
pretty well. Instead of thinking of *multiplication*, we can instead think of
*replacement*. `:(2,3)` can be thought of an annotation where each of the
*single wires* in `:2` are replaced with *multiwires* with annotation `:3`.

In short, this diagram, the expanded form of a multiwire `:2`:

```{#two}
circuit = vsep 0.3 [inputWire, inputWire]
```

becomes this diagram, where we've replaced each of the single wires with
multiwires:

```{#twomulti}
circuit = vsep 0.3 [labeledWire ":3", labeledWire ":3"]
```

which, of course, is the same as this *expanded* multiwire:


```{#twothree}
circuit = vsep 0.3 $ replicate 2 $ vsep 0.1 $ replicate 3 inputWire
```

While `:(2,3)` is *syntactically* equivalent to `:6`, they have very different
*semantics* when viewed under this light. `:6` has no structure to it, while
`:(2,3)` indicates a structure of two multiwires, each with annotation `:3`.

Therefore, these structural `:(x,y)` annotations can be thought of as
*multi-multiwires*. We will refer to this structure as a **product annotation**.

> Takeaway: A product annotation `:(x,y)` is a replacement of each of the
> individual wires in a multiwire `:x` themselves with a multiwire `:y`.

In this sense, multiwire annotations are *algebraic*, because we can perform
*algebra* on them. Don't worry, just because we're doing algebra on multiwire
annotations doesn't mean we ever need to actually *solve* that algebra. We leave
that work to the plebes responsible for actually implementing these wonderful
designs of ours.



## Back to Sanity

Returning to our `Demux` black-box, we see that it has inputs `A:n` and `D:d`,
and an output `:(2^d,n)`. Here `2^d` is a barbaric rendering of $2^d$, which as
we remember, is equivalent to the count of the unique numbers we can describe in
a multiwire with `d` bits. `Demux` is thus creating a multiwire for every
possible number we can describe in `d` bits, and each of them is of size `:n`.
This is the big bubba great granddaddy of our old `Demux2` machine.

Notice that the annotations on our inputs and outputs tell us a huge amount of
what this machine must do, despite the fact that we don't actually know what's
inside of it.

We'll start with a simple example to help drive the point home. Consider the
following machine:

```{#expand}
circuit = runCircuit $ void $ do
  m <- liftDia $ machine [""] [""] ""
  ina <- liftDia $ (||| wireLabel ":x") <$> bend
  out <- liftDia $ (||| wireLabel ":2^x") <$> wire
  assertSame ina Split m (In 0)
  assertSame out (In 0) m (Out 0)
```

There's really only one "honest" implementation for this machine, in the sense
that these are the true (most parsimonious) annotations for the inputs and
outputs. The only *obvious* implementation of this machine is to output a 1
on the wire equivalent to the value of input multiwire. Why? Well the only
relationship that we know between `:x` and `:2^x` is that we can represent $2^x$
different numbers with `x` bits. This implies we are probably expanding out the
number we've encoded in the input multiwire. This expansion is only ever going
to be *one* of the $2^x$ possibilities, implying we should probably put a 1 on
that line.

Note that this isn't the only implementation we could have made, but it's the
most likely based on what we know.

Back to `Demux`, due to our previous argument, it's almost certainly evaluating
the number stored in our `:d` multiwire, since our output is a product of `2^d`
and `n`. Recall that a product is the replacement of the single wires in a
multiwire each with a multiwire, so `:(2^d,n)` is, by the same argument, some
way of moving `n` into the number described by `d`.

That's as far as our analysis can get, since we don't know what that means of
moving `n` into `2^n` is, but we've already come quite some distance,
analytically.

Enough chatting. Let's build the dang thing. But first, a lemma from above:

```{#eval}
circuit = labeled "Eval" $ runCircuit $ void $ do
  m <- liftDia $ machine [""] [""] ""
  ina <- liftDia $ (||| wireLabel ":x") <$> bend
  out <- liftDia $ (||| wireLabel ":2^x") <$> wire
  assertSame ina Split m (In 0)
  assertSame out (In 0) m (Out 0)
```

We leave the implementation of this machine as an exercise to the reader, but as
our analysis showed earlier, the annotations here are powerful enough for us to
reason about this machine without knowing exactly how it might work. Of course,
that might not be satisfactory to you, and you are welcome to work out the
function table for this as a first step to implementing it. It's really not that
hard!

Anyway, we now present `Demux`:

```{#demux}
multiIn n s = mkCon s (In 0) ||| inputMulti ||| wireLabel n ||| mkCon s (Out 0)
multiIn' n s = mkCon s (In 0) ||| sspacer # scale 0.5 ||| inputMulti ||| wireLabel n ||| mkCon s (Out 0)

circuit = (||| sspacer) . labeled "Demux" $ runCircuit $ void $ do
  dIn <- liftDia $ multiIn ":d"
  eval <- liftDia $ machine ["*"] [""] "Eval"
  evalOut <- liftDia $ multiIn' ":2^d"
  assertSame dIn (Out 0) eval (In 0)
  assertSame eval (Out 0) evalOut (In 0)
  x <- liftDia multiOut
  and <- liftDia $ (\x -> x ||| inputWire ||| wireLabel ":(2^d,n)") <$> andGate' inputWire outputMulti
  assertSame evalOut (Out 0) x (In 0)
  assertSame x (Out 0) and (In 0)
  nIn <- aligning (multiIn ":n") (In 0) (dIn, In 0) (and, In 1)
  arr (nIn, Out 0) (and, In 1)

  return ()
```

The jankiness at the first input to the `and` gate is unfortunate, but
necessary. It's to indicate we're expanding all of the `:2^d` multiwire and
piping each of them into a copy of the `and` gate. We need that extra single
wire going directly into the `and` gate to distinguish from the syntax we
established earlier where we wanted to "zip" the wires in two multiwires
together. See the implementation for `Add4` if you don't remember this
concession.

There's a growing trend that our machine diagrams get simpler and simpler as our
diagram language becomes more and more powerful, and as we build more powerful
machines to harness. `Demux` would have been literally impossible to build
without polymorphic multiwires (although you could build `Demux` for any
*particular* annotation).

Given `Demux`, we're now set to build that memory block we've been discussing
seemingly *ad infinitum*, but we'll have to do it in the next chapter.

---

## Exercises

1) Flesh out the implementation for the `Eval` machine.
2) What's the difference between "zipping" two multiwires like we did in `Add4`,
   vs multiplying them like we are in our `and` gate in `Demux`? When are you
   capable of zipping multiwires? How about multiplying?

