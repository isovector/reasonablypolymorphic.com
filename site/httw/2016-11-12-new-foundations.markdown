---
layout: post
title: A New Foundation
date: 2016-11-12 14:00
comments: On
tags:
---


## Interlude

Wow! We've come a long way over the last eleven chapters. Seemingly ages ago, we
started with some key fundamentals: wires and machines. We touched on function
tables for describing how machines work, before moving to universal machines. We
used our knowledge of symbol manipulation to come up with a representation of
numbers, and then used those to learn how to add numbers. We set our sights on
bigger things, and learned about multiwires and their annotations. With these
more-powerful tools, we constructed polymorphic machines that operated on
multiwires, and saw how polymorphic annotations could be manipulated with
algebra. Most recently, we built a memory block, capable of selectively storing
and retrieving information.

Throughout our journey, there has been a slow-but-steady trend: we've
continuously been building bigger tools out of patterns of smaller ones. As we
build these bigger and bigger tools, we're capable of in turn using them to
build bigger ones -- tools that are too big to even consider building with
less-sophisticated tools.

My friends, this is the process of abstraction. We've built amazingly capable
things, having started from only two concepts -- that we have wires and machines
-- and some rules how for piecing them together works. We defended this choice
of an initial simplicity by way of *parsimony*, and today that choice is going
to pay off in spades for us.

However, as we've seen, our notation of drawing these machines in terms of
*machine diagrams* is clunky, and feels rather ham-fisted. Machine diagrams were
amazingly helpful when we started, and it was easy to see exactly how everything
fit together. However, now that multiwires are in the picture (if you'll forgive
the pun), and now that our diagrams are getting quite large, it's hard to keep
everything in our mind at once. It seems desirable that we come up with a new
representation for these logical systems we have been building, so that we can
continue abstracting (our semantics) without worrying too much about the form it
comes in (our syntax).

And so, today, we're going to look at an alternative representation of wires and
machines, one that will fit our purposes better. We'll build in a notion of
multiwires from the get-go, so that things end up looking "prettier" when we
need to use them later. But before we do any of these things, we need to discuss
types.



## Types

Types are a powerful abstraction on top of what we've been calling multiwire
annotations. Types are what multiwire annotations secretly strive to become --
what they stay up at night researching how to get a promotion. Or something like
that.

Quick! Pop quiz! Name as many colors as you can. Maybe you came up with things
like red, orange, and mauve, among others. It might not feel like it, but this
exercise you just performed highlights an interesting phenomenon.

Ok, now name four things you might purchase at McDonalds. Done? Great.

This is one of those "obvious-not-obvious" Mr. Bruce questions I mentioned
earlier. What is it, you might ask? It's "how can we perform such an exercise?"
How come "french fries" might have been an answer to "what can you buy at
McDonalds", but "hiking boots" assuredly wasn't.

An even deeper question is: "what kinds of distinctions are we drawing in order
to answer this?"

The answer to this Mr. Bruce question is that the distinctions we're drawing is
one between *groups* and *members*. The groups are the "categories" of things
we're looking for, and the members are the things that belong in that group.
While we might not be able to *name* all of the things in the group, it's
usually pretty easy to come up with a few examples. And because the universe
only has so many atoms in it, there *must* be a limit on the total number of
things in these groups.

And if there is a total number, then we can count to it if we were really
dedicated. And if we can count to something, it must be *countable*.

In order to determine whether something is a member of a group or not, we need a
notion of being able to distinguish that thing. We need to be able to *identify*
it. This sounds obvious, but it's worth stating, lest we dive off into crazy
territory.

We call these groups **types**, and we call their members **values**. We add an
additional constraint, that any value has *exactly one* type it is a member of.
This sounds unnecessarily restrictive at first blush, but, as we'll see, it
doesn't stop us from doing anything we'd like, and it makes the reasoning much
easier.

Before you dive in and start conjuring up types and values like there's no
tomorrow, let's slow down and pretend like types don't exist until we've defined
them together.

The most obvious type given our history is the type of a wire, with values 0 and
1. We even *called* them values to begin with, so that's a good sign. This type
is strictly more interesting than just being for wires, so we'll call it `Bool`.
This silly sounding name is actually short for a sillier sounding one:
"Boolean," which means "of or pertaining to George Boole." Mr. Boole was the guy
who came up with the idea of a type with only two values in it, so we name it
in his honor.

Our notation for defining types is thusly:

```
type Bool = On | Off
```

which should be read as "the `type Bool` *is defined as* being either `On` or
`Off`", the vertical bar meaning "or."

This definition tell us something, not only a relationship about what `Bool` is,
but also it tells us that `On` is a `Bool`, and `Off` is also a `Bool`. Obvious
stuff really, but, again, worth stating explicitly. We write these facts as `On
: Bool` and `Off : Bool`, where the `:` symbol should be read as "is a value and
has the type of."

You should be reminded by this notation of our multiwire annotations. And
indeed, our multiwire annotations in the form of `A:n` can be interpreted in the
same way: `A` is a value and has the type of `n`.

Values describe things that *are*, while types describe *things that could be.*
If I tell you to give me an `On`, there is exactly one value which that might
be. On the other hand, if I tell you to give me a `Bool`, you're free to pick
any value of type `Bool`.

> Takeaway: Values are things that *are*. Types are *things that could be.*

If we think of a wire being equivalent to type `Bool`, then it would make sense
that the possible values of a wire are `On` and `Off`. Our old annotation `:2`
was equivalent to having two wires side-by-side, and when interpreted as a type,
it must then be a combination of two `Bool`s.

The annotation `:2` corresponds to the type `(Bool, Bool)`, which you can think
of as a pair of two `Bool`s, sitting side-by-side exactly like their wire
counterparts were. But what are the values of this type `(Bool, Bool)`? As you
might expect, it's all of the combination of two wires. We'll list them here:

* `(Off, Off) : (Bool, Bool)`
* `(Off, On ) : (Bool, Bool)`
* `(On,  On ) : (Bool, Bool)`
* `(On,  Off) : (Bool, Bool)`

Notice that we have four values, not three as some might expect. `(On, Off)` is
distinct from `(Off, On)`, because it *actually matters* which wire is on and
which is off.

For the time being, however, we'll restrict ourselves to primarily thinking
about the `Bool` type.



## A New Foundation

With types under our belt, we can now look at our new representation of machine
"diagrams". Recall that the simple `and` gate could equivalently be described as
a picture:

```{#andgate}
```

or, alternatively, as a function table:

| Input A | Input B | Output |
|:-------:|:-------:|:------:|
| 0       | 0       | 0      |
| 0       | 1       | 0      |
| 1       | 1       | 1      |
| 1       | 0       | 0      |

We chose to use the picture more often than not, because it was easy to keep
track of how the inputs and outputs connected. Well, it was easy at first, at
least!

Our new representation of machines instead celebrates the function table. Here's
how we'd represent the `and` gate in our new formalization:

```
and : Bool -> Bool -> Bool

and Off Off = Off
and Off On  = Off
and On On   = On
and On Off  = Off
```

As you can see, this closely mirrors the function table. Except for the first
line, which is obviously something else. But what is it? Well, that first line
describes the *interface* of the machine!

The trick to reading the interface line is to look at the very last type (after
all of the arrows), and say "aha! This is the output of the machine!" All the
other types should be considered as inputs.

`and : Bool -> Bool -> Bool` should thus be interpreted as a machine which takes
two `Bool`s and outputs one `Bool`. Exactly like our old `and` gate showed:

```{#andgate}
circuit = andGate undefined ||| inputWire
```

The syntax for describing these machine interfaces initially seems... well,
let's admit it: suspicious at best. However, there is a *really really* good
explanation for why, which we'll discuss in a few chapters. It looks a lot like
how we describe the type of a value, so as a good rule of thumb "if there are
any arrows after the `:`, then it is a machine we're discussing." Otherwise,
it's a value with a type annotation.

Now that we know how to make machines in our new foundation, the only thing left
is to connect machines to one another, but that's a discussion for the next
chapter.

---

## Exercises

1) Define the machine in our new notation with the interface `nand : Bool ->
Bool -> Bool`. Given the fact that we can make this machine, how much of the
thing we've built so far with machine diagrams can we safely assume will
transfer over to the new representation?
2) List five values of the type `Number`.
3) List five values of the type `(Bool, Number)`.

