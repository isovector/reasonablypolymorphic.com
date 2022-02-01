---
layout: post
title: Polymorphism
date: 2016-11-16 20:00
comments: true
tags:
---

In the last chapter, we discussed some constructions on types, namely the
*product*, *sum*, as well as two particular types `Unit` and `Void`. A *product*
type was equivalent for asking for *both* types, while a *sum* type was
equivalent to asking for *either* type. We saw that `Unit`, when combined with a
*product* did nothing (because you always have one if you need it), and we saw
the same thing when combining `Void` in a *sum* type (because you can never have
one, by definition).

Today, we want to cover the last thing we'll need in our typesystem for quite
some time, and that's a more general notion of what it means for something to be
*polymorphic*. Recall that when we were discussing multiwires, our annotations
could be *polymorphic*, which was understood to mean, "we don't really care what
shape wire you try to plug into here."

Such a thing proved to be a useful notion -- it allowed us to build machines
like `Snap*` and `Demux` -- machines which performed a "semantic" operation in
the sense of "doing something useful for our purposes". They were abstract
enough that we didn't really *care* what the low-level inputs and outputs were,
because we were using these machines to serve a particular purpose we had in
mind. Because we knew how to create a device which would take a snapshot of 2
wires, and one which would take a snapshot of 3 wires, and one which would take
a snapshot of 4 wires, and so on and so forth, we could bundle all of that
knowledge up into one "schema" diagram and give you instructions for building a
machine that would take a snapshot of however many wires you so desired. Instead
of giving you machines for building circuits directly, we were giving you
blueprints to build machines to build circuits.

By discussing a *less* specific (polymorphic) machine, we found that we actually
had a *more* useful tool to work with. Because it was less specific, it worked
in more situations, at the expense of making us think a little harder about what
it all means. This strikes me as being a fantastic trade-off, because it's sort
of the definition of "work smarter, not harder". We spent some time looking at
patterns in the things we were painstakingly building, and we came up with a
better way of doing it. It saved us effort in the long run, which saved us time,
which not only is money, but also time that you now have to reinvest in making
smarter tools to save more time to make more money to invest harder in all of
this stuff.

Deliciously vicious!



## Value Polymorphism

There are two (related) kinds of polymorphism we need to discuss in this
chapter. The first, for lack of a better term, we will call *value-level
polymorphism*, which is the kind of polymorphism we are familiar with from our
experiences with multiwires.

An example of this was in our `Snap*` machine, which you might remember looked
like this:

```{#snap_nybble}
circuit = labeled "Snap*" $ runCircuit $ void $ do
  snap <- liftDia $ (\x -> x ||| sspacer # scale 0.5 ||| inputMulti ||| wireLabel ":n") <$> machine' [inputWire, outputMulti] ["S", "V"] ["Q"] "Snap"
  d <- liftDia $ const $ vspacer # scale 0.6
  spaceV 0.1 snap d
  input1 <- liftDia $ scale 2.2 <$> wire
  input2 <- liftDia $ multiIn ":n"
  assertSame input1 (Out 0) snap (In 0)
  assertSame input2 (Out 0) snap (In 1)
  return ()
```

An earnest (if naive) attempt to encode this machine as a symbolic computation
might look something like this:

```
snap* : Bool -> n -> n
```

Here, `snap*` has no opinion on what type `n` must be, other than that the input
to this machine *sure as hell* better be the same as the output of this machine.

How do we know that `n` is polymorphic, here? Well, we decide by fiat (and a
matter of convention) that *any "type" which starts with a lowercase letter is
polymorphic*. That means `n`, `z`, `cat`, `machinery` and `zzyzxyz` are all
polymorphic types, and moreover, if we had a machine:

```
silly : n -> z -> cat -> machinery -> zzyzxyz
```

we'd know that all of these polymorphic types *could* (but *need not*) be
different types. Recall that if a single machine refers to the same polymorphic
type more than once, we must use the *same* type to fill in all of the "holes"
for that polymorphic type.

With that one rule in mind, we can substitute types at will into `silly`. The
following are both valid type signatures for `silly`:

* `silly : Void -> Unit -> Bool -> Strange -> Something`
* `silly : Unit -> Unit -> Unit -> Unit -> Unit`

Of course, there are infinity different ways you could fill in these polymorphic
types, so this is not an exhaustive list. Go nuts!

These things we've been referring to as "polymorphic types" are more often known
as **type variables**. `t` is a type variable, and it is distinct from `x`.
Furthermore the type variable `t` is distinct from *all other* type variables
that are not named `t`. This argument holds in generality, for any name you can
think of to call your type variable.

Just so we really and truly drive the point home, given a machine with
polymorphic type variables:

```
odd : a -> a
```

then it's perfectly fine to "instantiate" `odd` with the following signatures:

* `odd : Bool -> Bool`
* `odd : Void -> Void`
* `odd : (Unit, Bool) -> (Unit, Bool)`

but the following are **not** well-typed instantiations of `odd`:

* `odd : Bool -> Void`
* `odd : Unit -> (Unit, Bool)`

because we *must* replace all `a`s in `odd` *with the same type*.

Sorry for stressing that point *so so much*, but it really and truly is very
important.



## Type Polymorphism

The other sort of polymorphism we need to discuss is "type polymorphism", which
is really just the same idea as value polymorphism, except in a different place.
Behold:

```
type Either a b = Left  a
                | Right b
```

This should be read as "`Either` is a **type constructor** which takes two
types, `a` and `b`, both polymorphic. The values of `Either a b` are either
tagged with a `Left` if they are an `a`, or with a `Right` if they are a `b`."

Quite a mouthful, but this is still just the same idea. We call `Either` a *type
constructor* because it must be *given* types before it "gives you back" a type.
What does that mean? That means that `Either` *is not* a type by itself, but
`Either Unit Bool` *is* a type.

You can thin of each type variable on the left of a type equality as being a
"hole", which need to be plugged before you can do anything useful with the type
constructor. Type constructors follow the same rules as value-polymorphism --
you have to replace a type variable with the same type everywhere. You get the
spiel by now, so I'll stop lecturing you on it.

A point to notice is that anything after the type name, but to the left of the
equals sign in a type definition *must be* a type variable. What does that mean?
It means that it's meaningless to say things like `type Bad Unit = What`. `Unit`
is a *type*, not a *type variable*, so it has no meaning to be put on the left
side of the equals sign. Again, common-sense stuff, but it bears mentioning.

We'll keep this `Either a b` thing around from here on out, it turns out that
all sum types can be generated by nesting `Either a b` inside of itself and
instantiating the type variables with whatever you please. In a sense, `Either a
b` is the "universal" sum type, because it allows us to do this.

**Point of order:** If you're filling out an `Either a b`, and you want to fill
the first type variable itself with `Either a b`, now you have something of the
form `Either (Either a b) c`, **not** `Either (Either a b) b`. The two eithers
get *different* type variables. You can avoid this problem if you replace all of
the type variables in a type constructor at the same time, or by just
remembering this fact. Type variables only need to be consistent *within a
single instance of looking at a type constructor*, not when composing types
together.

You might be wondering now if there's a "universal" product type, and indeed,
there is. We call it `(a, b)`, where -- you guessed it -- `a` and `b` are both
type variables.



## Doing Some Type-Foo

Now that we're equipped with polymorphic types, we are capable of defining a few
types which will make our lives much easier. The only one we'll look at today is
the `Maybe a` type, defined like this:

```
type Maybe a = Just a
             | Nothing
```

"*What* is this crazy thing?" you are probably asking yourself. What indeed?
`Maybe a` can be thought of as "an `a` which *may or may not* be there."
Consider the following values of `Maybe Bool`:

* `Just On  : Maybe Bool`
* `Just Off : Maybe Bool`
* `Nothing  : Maybe Bool`

The `Just` tag tells us that we do, in fact, have a `Bool` hiding inside of our
`Maybe Bool`. However, if instead we have a `Nothing` we know that we do *not*
have a `Bool` (because there is nowhere to put it, all we have is `Nothing`!).

But, why is this thing useful? And finally, for the first time in this book, I
can say "it actually is!" Finally! Remember, when we were defining our `Mem`
machine:

```{#mem}
circuit = machine' [inputWire # scaleX 2.2, inputWire # scaleX 2.2, multiIn ":n" undefined, multiIn ":d" undefined] ["RW", "G", "A", "D"] [""] "Mem" undefined ||| inputWire ||| wireLabel ":n"
```

we wanted to be able to choose between `R`eading and `W`riting, so we needed a
wire for that. But we also only wanted this machine to output the value at its
`D`estination if we wanted to read things. We solved this problem by adding a
`G`o wire, whose only job it was to tell us when to actually do something.

If we had `Maybe a` available to us back then, we could have gotten rid of `G`
entirely, and instead just made `RW : Maybe Bool`, where a value of `Nothing`
represented the fact that we didn't want to *read or write*. That's exactly the
semantics we wanted, but we didn't have a great way to do it, so we did
something inelegant and cheated by adding that `G` wire in.

```{#maybemem}
circuit = machine' [multiIn ":Maybe 1" undefined, multiIn ":n" undefined, multiIn ":d" undefined] ["RW", "A", "D"] [""] "Mem" undefined ||| inputWire ||| wireLabel ":n"
```

(where, of course, `:1` is the multiwire annotation for a single wire -- ie. it
is just `Bool` in disguise.)

Perhaps now you see why all of this type stuff might be useful -- it allows us
to specify *more exact* and, perhaps more importantly, *more elegant* semantics
for the tools we're trying to build.



## Something More Natural

Before we conclude this chapter, there's one more interesting type we should
look at before getting back to our humdrum task of building a device capable of
computing for us.

One type that is conspicuously missing from our pantheon is that of *numbers*.
Sure, we can kind of cheat by representing a binary number in terms of a product
type with lots of `Bool`s, but that is inelegant, and worse, has a "largest
number" representable (eg. the largest number you can represent with `(Bool,
Bool)` is 3).

No, we want something that is closer to the numbers that we work with everyday,
not some well-argued thing that "a bunch of wires beside one another is just as
good as having numbers." We want real numbers, if for no other reason than to
feel impressed with ourselves for having done it. As an added bonus, the
construction of numbers is actually quite interesting. Without further ado:

```
type Nat = Zero
         | S Nat
```

Such a type is called `Nat` because it is equivalent to the **natural numbers**,
which is to say, the numbers that you can count with. 0, 1, 2, 3, and so on.
Notably, there are no "negative" natural numbers, nor are there any "fractional"
natural numbers. That means $-5$, $0.3$ and $\frac{8}{7}$ are all out. Anything
else though, anything else is fair game.

But how does this `Nat` thing work? Well, a natural number is either `Zero`, or
it is the `S`uccessor to some other `Nat`ural number. Let's look at a few values
of `Nat` so you get the hang of out:

* $0 = $ `        Zero   : Nat`
* $1 = $ `S       Zero   : Nat`
* $2 = $ `S    (S Zero)  : Nat`
* $3 = $ `S (S (S Zero)) : Nat`

In general, if you want to represent a number as a `Nat`, you just need to stick
that many `S`s in front of a `Zero`, and make sure you wrap your parentheses
properly. If you want to decipher what number a value of type `Nat` actually
refers to, you just need to count how many `S`s make it up.

As a matter of fact, this `Nat` type is *exactly equivalent* to how counting
works. Such a fact was noticed by a guy named Giuseppe Peano, and so sometimes
you'll see `Nat` referred to as **peano arithmetic**. Neat, right?

However, needing to count a potentially huge number of `S`s in order to
determine what number we're describing sounds like it would get pretty tedious
pretty quickly. And so, as a convention, we allow ourselves to write a number in
its natural decimal form, and just say that that numeral is just a short-hand
for the *peano* construction of the same number.

All of this boils down to the fact that we can say `7 : Nat` as being completely
equivalent to `S (S (S (S (S (S (S Zero)))))) : Nat`. It's a good convention,
and one that we should all celebrate.

In the next chapter, we'll *actually* get back to business towards building our
computer. And we'll bring our fancy new types along to help.

---

## Exercises

1) How many values are there of type `Maybe (Bool, Either Bool Bool)`?
2) Is `x : Bool -> Bool -> Bool -> Unit` a valid instance of the polymorphic
   machine `x : a -> b -> a -> c`?
3) Write out the peano representation of `Just 4 : Maybe Nat`. Don't forget the
   `Maybe` part!
4) Define your own type that has exactly 5 values. Use only `Bool`, `Either a b`
   and `Maybe a`.

