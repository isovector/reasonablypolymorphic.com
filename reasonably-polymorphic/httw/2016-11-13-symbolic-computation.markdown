---
layout: post
title: Symbolic Computation
date: 2016-11-11 14:00
comments: On
tags:
---

In the last chapter -- the introduction to part 2 of this book -- we set the
stage for a new, more powerful foundation for our language of reasoning. We're
officially giving up on machine diagrams, because although they can help
understanding of simple concepts, they lack the precision necessary to describe
things at the level of abstraction we are just beginning to uncover.

We will call our new "version" of machine diagrams **symbolic computation**.
It's an apt name, since what it provides us is a mechanism for describing the
*computation* of *symbols*. We don't have anything more than a loose intuition
behind what it means to "compute" something, but we'll ignore that for a while.
As a good bet, anything the universe is capable of doing is probably computable
(if it weren't, how does the *universe* figure out what the answer is?).

There are reasonable objections to this claim, but we will try not to spill ink
on defending or refuting them. All I'm asking is to keep an open mind; it seemed
unlikely beforehand that we could have built a device capable of *remembering
information* when we started in chapter 1 with machines and wires, but as we
built more and more tools, eventually we managed to get there. I'm not saying
that everything the universe does is *easy* to compute, merely that it does
indeed "compute" it somehow -- for some definition of "compute", at least. I
offer no promises that we'll be able to compute morality, for example, but I
promise it will seem less daunting by the time we're finished.

To make good on a previous promise of mine, in this chapter we'll look at how we
can migrate the notion of "wires" from our machine diagram foundations to our
new symbolic computation framework.

Before we do that, however, the first question we should ask is "what purpose
did wires serve before?" Our original answer to that question was that they
served no purpose other than to connect one machine to another. This is true,
but we also subtly in another way -- we conflated the connections between
machines with the values that they held. This wasn't intentional, but it was
just that our machine diagrams lacked the expressiveness to describe "values at
rest".

Moving forwards, we'll differentiate between these two notions. This means that
we can discuss information at rest (values of a type), as well as means of
connecting machines (machine composition). Because we've already discussed types
and values, we move on to look at machine composition.



## Symbolic Computation

Symbolic computation is named thus because it defines computation in terms of
opaque symbols. This means that our values, in their most basic incarnation,
have no internal structure. Values are nothing more than labels that we humans
put on distinct things. The only thing we know about these *distinct things* is
that they are different from one another, and that we can differentiate them at
will. We know that `On` is different than `Off`, but the labels we have chosen
for them are nothing more than convention. We could have called them `Flubbix`
and `Rathcold`, and the theory would be none-the-wiser.

A point we should make explicit here is that because values are distinct, there
must never be an ambiguity in determining which symbol we are discussing. That
means while `zee` might be another label for `On`, it *cannot* be a label for
both `On` *and* `Off`. This was the rule we were implicitly enforcing when we
said of machine diagrams that their "function tables never lie". To reiterate,
that means that every machine's output must be defined for every possible input
it might receive. We say of such a machine that it is **total**.

> Takeaway: A total function is one that has output defined for each and every
> possible input it might accept.

But enough philosophizing. I promised to talk about how to compose machines
together. As a beginning exercise, let's define one machine in terms of another.
We want to construct this machine in our new system:

```{#compose}
```

Let's say we have the symbolic definition of `Blah`:

```
blah : Bool -> n -> Bool
blah On  _ = On
Blah Off _ = Off
```

which corresponds with this function table:

| Input A | Input B | Output |
|:-------:|:-------:|:------:|
| 0       | _       | 0      |
| 1       | _       | 1      |

`blah` is obviously just a machine that ignores its second wire. We use an
underscore `_` to indicate that we don't care which value that wire holds.

But notice here that we're doing more work than is strictly necessary. We could
instead have written a semantic symbol table:

| Output |
|:------:|
| **A**  |

which says that the output is always just the input `A`. We can rewrite `blah`
in this manner, too:

```
blah : Bool -> n -> Bool
blah a _ = a
```

Here, we've used the *symbol* `a` to refer to the value coming in on the `A`
input, regardless of what it might be. We call this `a` a **binding**, because
it *binds* to the value coming in on the input wire. If that value is `On`, then
`a` would currently act as a synonym for the value `On`. There's nothing new
here, it's just a new framing to wrap your head around.

Getting back to our diagram:

```{#compose}
circuit = labeled "Boring" $ (machine' [inputWire # scaleX 2.2, multiIn ":n" undefined] ["A", "B"] ["Q"] "Blah" undefined ||| inputWire # scale 2.2) === svspacer # scale 0.5
```

As this diagram shows, `Boring` is nothing more than a `Blah` hidden inside of a
box. `Boring` is thus a (very boring) composition of `Blah`. If we had `Blah`'s
function table, we could arduously and painstakingly copy it to define
`Boring`'s, but this breaks our desired abstraction semantics. In our machine
diagrams, we didn't *need* to know what `Blah`'s function table was, and that
was kind of the whole point.

We can instead describe `boring` as a symbolic computation like this:

```
boring : Bool -> n -> Bool
boring a b = blah a b
```

This definition should be read like this:

> `boring` is a machine which takes two inputs: one a `Bool` and the other some
> polymorphic `n`. This machine then outputs a `Bool`.
>
> It is defined as binding `a` to the first input (the `Bool`), and `b` to the
> second (the polymorphic `n`), and passing them as the first and second inputs
> to the `blah` machine, respectively.

Quite a mouthful, isn't it? That's why we use the more terse symbolic
computation definition. It saves a lot of time, and after you get good at
reading it, you'll appreciate the level of precision it affords us.

Looking at the definition `boring a b = blah a b` is quite telling, in its own
right. If you read that in your most exciting "math" voice, it says that
`boring` is simply equal to `blah`. Which is exactly what our machine diagram
said, too! Kinda neat, isn't it?

Let's try a more sophisticated example. Recall our definition of a `nand` gate:

``` {#and_not_labeled}
circuit = labeled "Nand" $ runCircuit $ void $ do
  and <- liftDia andGate
  not <- liftDia notGate
  spaceH 0.5 and not
  arr (and, (Out 0)) (not, (In 0))
  afterwards (||| inputWire)
```

We can express this symbolically:

```
nand : Bool -> Bool -> Bool
nand a b = not (and a b)
```

This reads a little backwards from what you might expect, but it makes some
sense if you think about it. Remember that `nand a b =` means we are binding `a`
and `b` to the inputs of `nand`, so it seems fair enough that we should put the
input to `not` *after* it. We use parenthesis to indicate that it is the entire
`and a b` (the output of the `and` gate, with `a` and `b` as inputs) that we
would like to give as an input to our `not` gate. Make sense?

Let's do another.

``` {#not_and_not}
circuit = labeled "Nandn" $ runCircuit $ void $ do
  notA <- liftDia $ fmap (\x -> (inputWire ||| x) # scale 0.5) notGate
  and <- liftDia andGate
  and1i <- getPort and (In 1)
  not <- liftDia $ fmap (||| inputWire) notGate
  notAi <- getPort notA (In 0)
  assertSame and (Out 0) not (In 0)
  assertSame notA (Out 0) and (In 0)
  c <- liftDia $ fmap (\x -> (inputWire ||| x) # scale 0.5) bend
  cp <- getPort c Split

  leftOf cp and1i
  above notAi cp
  arr (c, Split) (and, In 1)
```

would be described like this:

```
nandn a b = not (and (not a) b)
```

Reading these things is a bit of an art, but the trick is to always start from
the innermost set of parenthesis and work your way outwards. Here, we're passing
the `not` of `a` as the first input to our `and`, with `b` being the second
input. Then we're taking the output of the entire `and` gate, and giving it as
an input to `not`.

In the next chapter, we'll discuss the *evaluation semantics* of this symbolic
computation -- which is to say that we'll see how we can actually perform
"computation" with this method.

---

## Exercises

1) Give two symbolic definitions for `xor` -- one in terms of its function
   table, and one as a composition of `not`, `or` and `and` gates (recall the
   composition [from chapter 6](/book/arithmetic)).
2) Give a compositional symbolic definition for the `Cout` machine (recall the
   implementation [from chapter 6](/book/arithmetic)).

