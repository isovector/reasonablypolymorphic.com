---
layout: post
title: More Types
date: 2016-11-15 20:00
comments: true
tags:
---

In the last chapter, we looked at the evaluation semantics of symbolic
computation -- how to evaluate expressions down to values. We saw that we could
go in either direction -- replacing values with expressions that evaluated to
them, and simplifying expressions closer to their values. Now that we are armed
with the basics of working with symbolic computation, we'll look at moving our
*constructions on annotations* into *constructions on types*.

Recall that we decided to use values and types as "primitives" in our new system
of symbolic computation. What this means is that values and types are
fundamental, not just some janky thing tacked on as we went with machine
diagrams to express more power as we needed it. The idea is that the rules
behind our types (collectively know as our **type system**) are powerful enough
for anything we'd *ever possibly want* to do with them. In fact, we'll show a
little later that our type system is just as powerful (what does this mean?) as
the values and computations they annotate.

It is for this reason that we are spending so much effort on developing our type
system. While it is hard to believe right now, our type system will eventually
be where we'll be doing the majority of our reasoning. Our type system will be
so powerful that for the most part, there will only ever be a single (easily
found) machine that can possibly have that type.

The idea is that the more powerful our type system is, the more nuanced things
we can say with it. In the same way that there's only one person you think of
given a description of a "jolly old man, who wears red, gives presents away once
a year, and lives in the northern hemisphere", with a little practice you'll
only be able to see a single machine whose type is `: a -> b -> a`.

As a little inspiration, if you, gentle reader, have managed to get this far in
the book, and still consider yourself to be a "non-technical" type, take heart!
Reasoning by way of the type system is indeed a powerful art, and one that most
professional computer scientists have yet to come across, let alone master.
Unfortunately for them, this is a skill that would make their day-to-day jobs
tremendously easier, if only they knew it. I tell you this not to belittle them,
but to inspire you. It's not a particularly difficult topic, and if you can
manage to hold on just a little longer, you'll have the tools under your belt in
order to compete with the best of them I tell you this not to belittle them, but
to inspire you. It's not a particularly difficult topic, and if you can manage
to hold on just a little longer, you'll have the tools under your belt in order
to compete with the best of them. This is absolutely not hyperbole.



## Product Types

The first construction on types we'll revisit is the **product type**. A
*product type* is what you get if you are audacious enough to "glue" two types
together. We've already seen an example of a product type, `:2` in our
multiwire annotations, which corresponded to the type `(Bool, Bool)`. We used
the same notation when describing annotations, so none of this should be
revelationary new material to you,

Conceptually, `(Bool, Bool)` is two booleans glued together, but allowing either
of them to vary independently of the other. The product of `Bool` with `Bool`,
as we have seen, has four values:

* `(Off, Off) : (Bool, Bool)`
* `(Off, On ) : (Bool, Bool)`
* `(On,  On ) : (Bool, Bool)`
* `(On,  Off) : (Bool, Bool)`

A neat fact is that a product is formed by gluing two types together, and that a
product of two types *is itself* a type. This means that we can glue products
together indiscriminately. For example, we can make `((Bool, Bool), Bool)`, by
gluing a `(Bool, Bool)` together with a `Bool`. There are exactly eight values
with this type:

* `((Off, Off), Off) : ((Bool, Bool), Bool)`
* `((Off, On ), Off) : ((Bool, Bool), Bool)`
* `((On,  On ), Off) : ((Bool, Bool), Bool)`
* `((On,  Off), Off) : ((Bool, Bool), Bool)`
* `((Off, Off), On ) : ((Bool, Bool), Bool)`
* `((Off, On ), On ) : ((Bool, Bool), Bool)`
* `((On,  On ), On ) : ((Bool, Bool), Bool)`
* `((On,  Off), On ) : ((Bool, Bool), Bool)`

In general, a product of `(m, n)` (for any types `m` and `n` you choose), has a
number of values equal to the number of values `m` has, times the number of
values that `n` has. That's why when we take the product of `Bool` (two values)
with itself, we get four values. In some sense, then, the product of two types
can be considered a form of "multiplication" between two types. In fact
mathematicians sometimes use the word "product" to mean "multiplication".

This is just the first in a long string of spooky coincidences between
grade-school arithmetic and the dark mysteries behind computation.

As a good rule of thumb, you should associate a product type with the idea of
"and", as in, if you need one type *and* another, what you really are looking
for is a product of the two. Or three. Or four.

Speaking of taking products of more than two types, it's informative to note
that it doesn't matter in which order you multiply the numbers from left to
right or from right to left -- $2\times (3\times 4) = (2\times 3)\times 4 = 24$.
Because of this fact, we're allowed to drop the parentheses when multiplying
several numbers together: $2\times 3\times 4 = 2\times (3\times 4) = (2\times
3)\times 4 = 24$, and because of *that* fact, we can safely conclude that
parentheses don't matter when writing out product types. That is to say that
`((Bool, Bool), Bool)` is the same type as `(Bool, (Bool, Bool))`, which then
must be the same as `(Bool, Bool, Bool)` for exactly the same argument as in our
multiplication example.



## The Unit Type

Are you as tired of reading about `Bool`s as I am writing about them? Let's
spice up our type ecosystem a little, even if it's with an unbelievably dull
type. Say "hello" to what might be the silliest type:

`type Unit = Unit`

This should be read as "`Unit` is a type with one value, also called `Unit`".
Naming the type and its value both `Unit` seems like an odd choice -- like it's
prone to lead to misunderstandings. When I say `Unit`, how do you know whether
I'm talking about the type or the value?

Good news! It doesn't matter. Because `Unit` is a type with only value, and all
values must uniquely belong to a single type, this means whenever we have a
`Unit` value, its type *must* be `Unit`, and whenever we have the type `Unit`,
we know what its value must be. There's no room for error, because there's no
room for choice. It's kind of zen if you think about it.

So what's `Unit` good for, if it presents no choices? Well, nothing really.
`Unit` represents knowledge you already know. It'll come into play in a second,
but only in the sense that it allows us to build things that *aren't* `Unit`s.

Note that because multiplying anything by 1 results in the thing you started
with, taking a product with `Unit` doesn't do anything. You can take products
with `Unit` until the cows come home -- `(Bool, Unit, Unit, Unit, Unit, Unit,
Unit, Unit, Unit, Unit, Unit, Unit, Unit, Unit, Unit, Unit)` is literally
exactly the same thing as just a lonely `Bool`.



## Sum Types

If product types should remind us of *and*, the curious reader will wonder what
kinds of types reminds us of *or*. **Sum types** are the answer to that
question.

Intuitively, a *sum type* is asking "do I have something of type `a`, *or*
something of type `b`?" Let's take a look at an example to help drive the point
home.

```
type Strange = CouldBe   Bool
             | Otherwise Unit
```

Such a strange thing should be read as so: "`Strange` is a type whose values
might be `Bool`s, or they might be `Unit`. If they're `Bool`, we'll prefix them
with `CouldBe`, and if they're `Unit` we'll prefix them with `Otherwise`".

We'll dig into this in a second, but sometimes a list of values is worth a
thousand words.

* `CouldBe   On   : Strange`
* `CouldBe   Off  : Strange`
* `Otherwise Unit : Strange`

This list comprises *all* of the values of type `Strange`. We need to use the
prefixes to distinguish values inside a sum type from their counterparts outside
of them. For example `On` is of type `Bool`, but `CouldBe On` is of type
`Strange`. Remember, all values must be of a single, unique type. And so without
these prefixes, we'd be unable to distinguish between a `Bool` and a `Strange`
when talking about values.

Going forward, we will call these prefixes as **value constructors**, because
they *construct values* of the sum type out of values from the type being
summed.

If you're quick, you've probably noticed that `Strange` has three values, and is
a sum of a type with two values, and a type with one value. Indeed, calling such
a thing a "sum type" is particularly telling. As an exercise, determine if sum
types always add together the values of their underlying types.

An interesting thing to note is that *sum types* and `Unit` are somehow more
*parsimonious* than `Bool`s. Consider this alternative definition of `Bool`:

```
type AlternateBool = SumOn  Unit
                   | SumOff Unit
```

Because we've shown earlier how knowing something is `Unit` tells you no more
than you knew before, so this definition is equivalent to having dropped the
`Unit`s altogether. As such, we can reason that `Bool` is nothing more than a
sum of `Unit` with itself, where all of the information being stored about
values comes from the *value constructors* themselves.



## Void

We have one more "interesting-not-interesting" type to look at today. Notice
that there is nothing that stops me from making a "group" containing all of the
federal holidays on which there is a tradition to give me billions of dollars
worth of gifts. This doesn't mean that such a group contains any *actual
holidays*

Likewise, we can declare a type which has no values. Such a thing is usually
called `Void`, and is declared like this:

```
type Void
```

Notice how there is no equals sign after this. We're saying that there is such a
thing as a `Void` type, but haven't listed any values for it.

*A quick aside to programmers:* if you're familiar with the `void` "type" in
languages like C, Java or similar languages, the thing you call `void` is *not*
the same as this `Void` type we have just declared. What you call `void` is in
fact the `Unit` type. There is no such thing as a real `Void` in most
programming languages. *End aside.*

Maybe you can squint and see how `Unit` is a useful type, but even then, it's
certainly going to be a strain to see how `Void` could possibly be useful. It's
not really.

`Void`'s main purpose is for filling out our roster of "interesting" types. In
many ways, it's a counterpart to `Unit`. Because `Void` has zero values, it has
some interesting properties. The first is that any type summed against `Void` is
equivalent to the type itself, since there is no way to ever get into the other
value constructor. This is consistent with our understanding that sum is
addition -- adding 0 to any number is still the number you started with.

Additionally (no pun intended), `Void` interacts strangely with product types.
Because product types multiply values, taking a product with `Void` is always
just `Void`. Why is this? Well in order to construct a product value, you need a
value from *each* of the component types. But there are no values of `Void`, so
you can't get one, so you can't construct any values of the product type.

And so we can say that the relationship between `Void` and `Sum` is the same as
that between `Unit` and `Product`, which is that "nothing happens when you
combine them".

But you might persevere -- "what good is this `Void` thing?" It's not really,
for our purposes, but it will be in a few chapters when we decide to look at
*why* our type system is powerful. As something to whet your appetite, try to
find a machine that has this interface:

```{#absurd}
circuit = machine' [multiIn "Void" undefined] [""] [""] "" undefined ||| inputWire
```

Hint: don't look very hard.

In the next chapter we'll look at how to represent *polymorphism* in our type
system, and then get back to practical matters at hand and continue working
towards building a computer.

---

## Exercises

1) Work a few examples of sum types to prove to yourself that they add together
   the number of values in their component types.
