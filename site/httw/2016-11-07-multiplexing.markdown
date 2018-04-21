---
layout: post
title: Multiplexing
date: 2016-11-07 20:00
comments: true
tags:
---

In the last chapter we implemented a machine, `Add4`, which added two nybbles
together. We then realized that dealing directly with wires was a pretty
terrible experience, so we invented the concept of a *multiwire* -- a group of
wires that acts as one. We made up some semantics for how these things interface
with machines -- either directly inputting all of their wires, or by making a
copy of every machine they touch.

The last few chapters have been a long stretch of working with numbers, and
you're probably sick of them. Let's take a break in this chapter, and without
further ado, build some tools to help us work with multiwires.


## A New Machine

The first machine we'll build is called `Split`, and it divides a (single) wire
into its value and the `not` of its value.

```{#split}
circuit = labeled "Split" $ runCircuit $ void $ do
  out0 <- liftDia $ (||| wireLabel "+") <$> wire
  out1 <- liftDia $ (||| wireLabel "-") <$> wire
  not <- liftDia notGate
  input <- liftDia wire

  b0 <- liftDia con
  b1 <- liftDia bend

  liftCircuit $ constrainWith (vsep 1) [b0, b1]
  assertSame not (Out 0) out1 (In 0)
  assertSame not (In 0) b1 Split
  assertSame input (Out 0) b0 Split
  sameY b0 out0
  arr (b0, Split) (b1, Split)
  arr (b0, Split) (out0, In 0)
```

`Split` is super simple -- a nice break from what we've been doing lately, no?
But why is it useful? As usual, it's not useful in-and-of-itself, but just a
stepping stone in the implementation of something more useful. We call these
"less-than-useful" machines **lemma machines**, because a **lemma** is something
you make solely to be used to make something else.

> Takeaway: A **lemma** is something you make in order to use it to make
> something else.



## Demultiplexing

What, you might be wondering, will we use this *lemma machine* for? Well, it's
called `Demux2`, and it looks like this:

```{#Demux2}
circuit = labeled "Demux2" $ runCircuit $ void $ do
  split <- liftDia $ (labeledWire "D" ||| inputWire |||) <$> machine [""] ["+", "-"] "Split"
  split1out <- liftDia $ scale 2 <$> wire
  split2out <- liftDia wire
  c <- liftDia con
  b <- liftDia bend
  down <- liftDia vwire
  and1 <- liftDia $ (\x -> x ||| sspacer # scale 0.5 ||| inputMulti ||| wireLabel ":n") <$> andGate' outputMulti inputWire
  and2 <- liftDia $ (\x -> x ||| sspacer # scale 0.5 ||| inputMulti ||| wireLabel ":n") <$> andGate' inputWire outputMulti
  input <- liftDia $ multiIn "A:n"
  liftCircuit $ constrainWith (vsep 0.5) [and1, and2]
  liftCircuit $ constrainWith hcat [input, c]
  assertSame split (Out 0) split1out (In 0)
  assertSame split (Out 1) split2out (In 0)
  assertSame split2out (Out 0) down (In 0)
  assertSame split1out (Out 0) and1 (In 1)
  sameX input split
  getPort input (Out 0) >>= \p0 ->
    getPort and1 (In 0) >>= \p1 -> do
      leftOf p0 p1
      arr (input, Out 0) (and1, In 0)
  getPort c Split >>= \p0 -> do
    getPort b Split >>= \p1 -> do
      above p0 p1
      getPort and2 (In 1) >>= \p2 -> leftOf p1 p2
  port <- getPort input (Out 0)
  arr (down, Out 0) (and2, (In 0))
  arr (c, Split) (b, Split)
  arr (b, Split) (and2, In 1)
```

Spend a minute or two convincing yourself that you know what this machine does
before reading on.

`Demux2` takes a multiwire input `A`, annotated as `n`. What is this `n`? Well,
it's not anything *specific*. It's a placeholder for any particular multiwire;
this machine doesn't care what multiwire is coming into it, so we use the
placeholder `n` to say "give me anything you got". We say that a multiwire with
such a placeholder annotation is **polymorphic**.

> Takeaway: A multiwire without a specific annotation is called **polymorphic**,
> which means it can take *any* annotation. Any machine which takes such a
> multiwire is also said to be *polymorphic*.

Note that there is nothing special about the annotation `n` -- it could just as
well be `a`, or `x`. We will treat any annotation that is one-letter long and
all lowercase as a *polymorphic* annotation. When you make this machine, you can
substitute `n` with any annotation you please, so long as you change *all of the
`n`s* at the same time. That means the output wires, because they're also
labeled `n`, must *always* have the same annotation as the input wire. If we
wanted the outputs to have a different annotation than the input, we'd need to
use a different letter to annotate them -- maybe `j` or something like that.

Back to `Demux2`. The other input to this machine is a (single) wire `D` (short
for "destination"), which `Split`s and then is `and`ed against the contents of
multiwire. Whenever a wire is `and`ed against value 1, its value passes through
untouched; likewise, `and`ing against value 0 will always output a 0. As a
result, pushing our multiwire through these `Split`ed `and` gates, acts like a
"filter" -- a copy of the multiwire input will be made *either* on the top
multiwire, *or* on the bottom one. The other multiwire will have 0s on all of
its wires.

> Takeaway: Any wire `and`ed against a 1 moves its value through the gate.

So `Demux2` allows us to take a signal and move it to one of two wires, depending
on an input signal. You can think of this like a traffic fork -- either your car
goes one way, or it goes the other. It can't go down both lanes simultaneously
(unless you are particularly unlucky that day). This metaphor is enticing,
because it suggests another machine, namely a traffic *merge*. Let's build that
next.



## Multiplexing

```{#Mux2}
polyOut a = mkCon a (In 0) ||| sspacer # scale 0.5 ||| inputMulti ||| mkCon a (Out 0)

circuit = labeled "Mux2" $ runCircuit $ void $ do
  switch <- liftDia $ (wireLabel "W" |||) <$> wire
  split <- liftDia $ machine [""] ["+", "-"] "Split"
  assertSame switch (Out 0) split (In 0)
  split1out <- liftDia $ scale 2 <$> wire
  split2out <- liftDia wire
  down <- liftDia vwire
  and1 <- liftDia $ andGate' outputMulti inputWire
  and1out <- liftDia polyOut
  and2 <- liftDia $ andGate' inputWire outputMulti
  and2out <- liftDia polyOut
  liftCircuit $ constrainWith hcat [and1, and1out]
  liftCircuit $ constrainWith hcat [and2, and2out]
  or <- liftDia $ (\x -> x ||| sspacer # scale 0.5 ||| inputMulti ||| wireLabel ":n") <$> orGate' outputMulti outputMulti
  input1 <- liftDia $ multiIn "A:n"
  input2 <- liftDia $ multiIn "B:n"
  liftCircuit $ constrainWith (vsep 0.5) [and1, and2]
  assertSame split (Out 0) split1out (In 0)
  assertSame split (Out 1) split2out (In 0)
  assertSame split2out (Out 0) down (In 0)
  assertSame split1out (Out 0) and1 (In 1)
  sameX input1 input2
  spaceH 1 and1 or
  getPort input1 (Out 0) >>= \p0 ->
    getPort and1 (In 0) >>= \p1 -> do
      leftOf p0 p1
      arr (input1, Out 0) (and1, In 0)
  getPort input2 (Out 0) >>= \p0 ->
    getPort and2 (In 1) >>= \p1 -> do
      leftOf p0 p1
      arr (input2, Out 0) (and2, In 1)
  port <- getPort input1 (Out 0)
  arr (down, Out 0) (and2, (In 0))
  arr (and1out, Out 0) (or, In 0)
  arr (and2out, Out 0) (or, In 1)
  return ()
```

`Mux2`, as you might expect, is the opposite of `Demux2`. It takes two
polymorphic (but annotated the same) multiwires `A` and `B`, choses *one* of
them via the value of `S` (short for "source"), and moves it to the output.
Whenever a wire is `or`ed against a 0, its value moves through the `or` gate, so
because we've filtered one of our multiwires all the way to 0, the other
successfully passes through the `or` gate.

> Takeaway: Any wire `or`ed against a 0 moves its value through the gate.

While a `Demux2` allows us to move a multiwire to one of two locations, based on
a `D`estination, `Mux2` lets us choose a `S`ource multiwire and move it to a
single output. `Demux2` can selectively *send* information somewhere, while
`Mux2` can selectively *read* information.

Study these two gates well, because we'll get lots of mileage out of them as we
move forward into the actual implementation of a computer. It might not feel
like it, but we've already built most of the pieces we'll need in order to
*actually get some real work done*. Exciting, no?

In the next chapter, we'll investigate how to make machines that *change over
time*, which will be the basis for us to *store information*. From there it's
just a short hop to actual computers!

---

## Exercises

1) Design `Mux4` and `Demux4`, which take a multiwire annotated as `2` (ie. two
   wires) and uses it to switch from/to four different multiwires.

