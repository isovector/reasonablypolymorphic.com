---
layout: post
title: Machine Diagrams
date: 2016-11-01 20:00
comments: true
tags: foo, bar
---

## Machine Diagrams

To start off our journey into the depths of abstraction, we first need to learn
a few fundamentals. *Literally* everything we build in the remainder of the book
will be nothing more than interesting combinations of these few building blocks.
It will probably feel slow and obvious, but it's an unfortunate fact of
difficult things (and of life) that we must walk before we can run.



### Wires

This is a **wire**.

``` {#wire}
circuit = ru$ void $
  anon bend $ \(in', inp) ->
  anon bend $ \(out, outp) -> do
    leftOf inp outp
    spaceH 1 in' out
    arr (in', Split) (out, Split)
```

A wire can be either `hot` or `cold`. A hot wire is hot along its entire length.
Imagine this wire is electrified -- regardless of where you touch it, you're
going to get a shock. Likewise, a cold wire is cold along its entire length.

A wire doesn't need to be a straight line. It can bend, and it can fork:

``` {#fork}
circuit = ru$ void $
  anon con  $ \(split, splitp) ->
  anon bend $ \(d, dp) ->
  anon bend $ \(r, rp) ->
  anon bend $ \(in', inp) ->
  anon bend $ \(out, outp) -> do
    leftOf inp outp
    leftOf inp splitp
    spaceH 0.5 in' split
    spaceH 0.5 split out
    spaceV 0.25 split d
    spaceH 0.5 d r
    spaceV 0.25 out r
    arr (in', Split) (out, Split)
    arr (split, Split) (d, Split)
    arr (d, Split) (r, Split)
```

Whenever a wire forks, we draw a little circle to indicate that the wires are
still touching. For example, despite how it looks, there is still only one wire
in the above diagram.

However, the following diagram is **two** wires crossing one another (imagine
one is higher than the other, or something). They are not touching, because
there is no little circle marking their intersection. Because they are separate
wires, they can carry different values.

``` {#cross}
circuit = ru$ void $
  anon bend $ \(in', inp) ->
  anon bend $ \(out, outp) ->
  anon bend $ \(in'2, inp2) ->
  anon bend $ \(out2, outp2) -> do
    leftOf inp outp
    spaceH 1 in' out
    above inp2 outp2
    spaceV 1 in'2 out2
    spaceV 0.5 in'2 in'
    spaceH 0.5 in' in'2
    arr (in', Split) (out, Split)
    arr (in'2, Split) (out2, Split)
```

We sometimes call a hot wire `on` or `high` or having value `1`. A cold wire is
also known as `off`, `low` or having value `0`. All of these terms will be used
interchangeably, and there is absolutely no distinction between the variations.
It's important to also stress that these labels are just that -- nothing more
than some way of referring to the potential states of these wires. A wire that's
on isn't physically hot, nor does the altitude differ between wires with values
of 0 and 1.

Regrettably, the literature also uses the terms `true` and `false` to describe
the two possible values of a wire. This book will strongly avoid this
nomenclature, since it will get us all tangled up in the future when we discuss
logic.

Of course, wires by themselves aren't very interesting. Because a wire is
required to have the same value everywhere, the question is begged: what good is
it? The tongue in cheek answer is that it isn't useful. The only things we use
wires for are to move values between **machines**.

> Takeaway: Wires move values between machines.



### Machines

Machines are little bit more interesting, but only just. They look like this:

``` {#machine}
circuit = blackBox "M" undefined ||| inputWire
```

A machine has some number of **inputs** and some number of **outputs**. As a
matter of contention, we will draw our inputs on the left of the machine, and
our outputs on the right.

As you might expect, a machine transforms its inputs into outputs. This
transformation is often described in the form of a **function table**[^1] -- thus
named because it describes how the machine *functions*.

[^1]: The literature unfortunately also refers to these as "truth tables." We
will continue to eschew any mention of "truth" here.



### The Not Machine

One of the simplest machines is the **not machine**, which has this function
table:

| Input | Output |
|:-----:|:------:|
| 0     | 1      |
| 1     | 0      |

But how should we interpret this? As you can probably guess, the *not machine*
flips incoming hot wires to be output as cold, and likewise changes off wires to
be output as on.

Consider the following diagram:

``` {#not_box}
circuit = wireLabel "a=1" ||| blackBox "Not" undefined
                          ||| inputWire
                          ||| wireLabel "b"
```

In this diagram, the wire labeled `a` has value 1. The wire labeled `b` doesn't
have a specified value, but we *know* from the not machine's *function table*
that `b`'s value must be the opposite of `a`'s -- and so `b=0`. It's a fact that
the wires on either side of a *not machine* have opposite values. If your friend
gave you this same diagram with both `a` and `b` specified to be equal to `1`,
you should stop being friends with that person because they are lying to you.
Function tables never lie.

> Takeaway: Function tables never lie.

Because *not* is such a popular machine, we will give it a special symbol,
called a **not gate**. There's no rhyme or reason behind why, but it's what
other people call them, and I wouldn't want people to look at you like you're
crazy when you're discussing these things around the water-cooler. Redrawing
the last diagram with a *not gate*:

``` {#not_gate}
circuit = notGate undefined ||| inputWire
```

This concludes our discussion of machine diagrams. Next we will look at more
complicated machines (those with more than one input), and that will lead us to
the discovery of the so-called universal machines.

## Exercises

1) Determine the function table for one *not gate* feeding into another *not
   gate*. Is it interesting? Why?

2) Besides the *not gate*, there are 3 other possible machines with 1 input and
   1 output. Figure out what their function tables must look like. Remember, a
   function table *must* have an output for every possible input.

