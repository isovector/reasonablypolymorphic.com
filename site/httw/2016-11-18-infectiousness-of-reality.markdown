---
layout: post
title: The Infectiousness of Reality
date: 2016-11-18 23:59
comments: true
tags:
---

In the last chapter, we worked on porting some of our old machine diagrams into
symbolic computations. We rather tediously moved over `add4`, balked at trying
to write `add8`, and instead decided to work smarter, rather than harder. We saw
that there was a highly-repetitive pattern inherent in the work necessary to
connect adders together, and we used a new type `List a` to allow us to exploit
that pattern.

Today, we will look at moving across more of our machinery. In the machine
diagram world, the next thing we did was multiplexing and demultiplexing, but we
will not do much with them as a symbolic computation. Naturally the question
comes up: why not? The answer is that these concepts are in a way too "low
level" for our concerns now. Because symbolic computations and the type system
backing them are so expressive, we'll find that we just don't really have a use
for multiplexing and demultiplexing. Recall that their primary use was for
moving complicated multiwires around, but now that our type system manages that
for us in a more elegant fashion, we're good to go.

That being said, if you feel like you'd enjoy some more practice moving machine
diagrams into symbolic computations, go right ahead! It's always nice to get a
little more exercise.

If you'll take my word for it, neither of us will be very upset should we skip
de/multiplexing -- no sense in making something we won't use. And so we move
right along to "latches", which as you recall, are machines that somehow
"remember" the past. The first one we looked at was this:

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

While `Hold` is easy conceptually, it has a lot to teach us about how latches
might work as a symbolic computation. We'll naively convert `Hold`, in the
obvious way.

```
hold : Bool -> Bool
hold a = or a (hold a)
```

Looks promising, right? This is a straightforward transformation from the
diagram to a computation. Something goes terribly wrong if we ever try to
actually evaluate this.

* `hold Off`
* `or Off (hold Off)`
* `or Off (or Off (hold Off))`
* `or Off (or Off (or Off (hold Off)))`
* ... and so on and so forth...
* `or Off (or Off (or Off (... forever)))`

Uh oh. Something's obviously gone wrong! You might spend some time scratching
your head; the problem is subtle. In defining the `Hold` machine originally, it
turns out we "cheated" and did something *bad*.



## Lying to Ourselves

Remember our first rule: *function tables never lie*. And our second rule: *a
machine's output must be fully determined by its inputs*. Herein lies the
problem -- `Hold`'s output *wasn't* fully determined by its inputs. It was also
determined by it's *previous* inputs, which is obviously a clear violation of
the second rule. In our haste to define these things, we broke the laws, and now
we find ourselves unable to continue, because symbolic computations are somehow
keeping us more "honest" than the machine diagrams ever were.

This is a good thing, even if it is rather annoying.

So what can do about it? Obviously machines that can remember the past are
desirable -- it would be the pits if our computers were incapable of saving
files, for example. We can reconcile all of these problems by noticing exactly
what equivocations we were performing with our machine diagrams, even if we
didn't realize we were doing it.

The problems were twofold, if related:

* We assumed some notion of "the real world" in our machine diagrams.
* Because we assumed we had "the real world" at our disposal, we assumed that we
  also had "time" at our disposal.

By "assuming the real world" what I mean is that we expected our machine
diagrams to, in some sense, behave in the way we know real electronics work.
That means we can expect them to exist in time, and so the meaning of
"remembering the past", while it doesn't actually exist inside of the system,
exists in our *minds*, and that makes it feel like we're reasoning inside of the
system.

This phenomenon, in my opinion, is the greatest flaw in human psychology.
Unfortunately, our brains don't have the evolutionary hardware to deal with
reasoning about complicated logical puzzles. Instead we kinda "cheat" and use
our generalized reasoning parts of the brain, but these are evolutionary quite
new, and not particularly well suited for the task at hand. It is exactly for
this reason that I think having such dry and formal tools for describing these
computations, and mathematics in general, is so helpful. Only through immaculate
formality can we be convinced that we have been absolutely precise in our
reasoning.

As we have seen, this is no small feat. What felt like solidly-argued reasoning
when we defined `Hold` turned out to have lead us astray. The only true defense
I know of is to continually go back to the original rules we've laid down, and
to consult them for guidance. If the fundamental rules aren't satisfied, the
only way our reasoning can possibly be correct is by accident.



## The Nasty Real World

Back to the problem at hand. The real issue we're facing is that we have no
means of tracking which parts of our computation are good and pure (those which
behave well and follow our rule about outputs coming directly from inputs) and
those which are nasty and need to exist in "the real world", somehow.

As is so often the solution to our problems, we will solve this by strengthening
our type system. Not only will our type system be used to describe inputs and
outputs, but we will power it up so that it can talk about the *contexts* in
which computations must be run.

We will annotate contexts of computations like this. For example, the `Clock`
machine:

```{#clock}
circuit = labeled "Clock" $ runCircuit $ void $ do
  or <- liftDia $ (spacer |||) <$> notGate
  c <- liftDia con
  done <- liftDia wire
  orOut <- liftDia wire
  orDown <- liftDia $ scale 2 <$> vwire
  assertSame or (Out 0) orOut (In 0)
  assertSame orOut (Out 0) orDown (In 0)
  assertSame orOut (Out 0) done (In 0)
  assertSame c Split orOut (Out 0)
  b <- aligning bend Split (or, In 0) (orDown, Out 0)
  arr (b, Split) (or, In 0)
  arr (b, Split) (orDown, Out 0)
```

obviously needs some sort of "real world" context, since it has *no inputs*, but
a changing output. We give `Clock` this type signature:

```
clock : RealWorld Bool
```

where `RealWorld Bool` is taken to mean "a `Bool` which we are unable to reason
about".

The first thing to notice is that this `RealWorld`-ness is somehow "infectious".
Think about it -- any machine which contains a `clock` somewhere inside of it is
no longer subject to being reasoned about. If any part of the whole can't be
reasoned about, the whole itself must have some degree of unknown-ness. That
means that any machine which contains a `RealWorld` component must itself be
tagged as `RealWorld`.

When most people hear about this, their first reaction is to start moving all of
their machines into the `RealWorld`, but despite their good intentions, those
people are fools. In actual real life, when something is infectious, we don't
celebrate by infecting everyone. What we actually do is set up quarantines --
barriers through which the infection can't pass. We'd like to instate such a
quarantine procedure here in our symbolic computations. While it's an
unfortunately fact of the real world that there must indeed be some components
that run in the `RealWorld`, we don't need to embrace it.

Our must obvious tool for dealing with the infectiousness of the `RealWorld` is
in composition. Just because the *output* of a machine can't be reasoned about,
doesn't mean that we can't give it as an *input* to a pure machine (a machine
whose function table behaves nicely). The vast majority of the pieces in our
large contraption can be pure and well-reasoned, and only the eventual
composition of all of these pieces together need live in the `RealWorld`. This
will be our primary means of quarantine, and it will serve us well.

The other tool we will learn is that just because a computation isn't *pure*
doesn't mean that it requires the full "unknowability" of `RealWorld`. The
`RealWorld` represents things that our system fundamentally has no way of
reasoning about, but often there are clever tricks we can use to allow us to
reason "inside of the system". This will turn out to be the case when we start
thinking about past-history in earnest, as well as the majority of things we
actually want to do.

Unfortunately, it's clear that we are still under-prepared to deal with the
actualities of making a computer. Our concepts *just aren't powerful enough,
yet*. Remember, we took on an ambitious project, but that's not to say we're not
making progress. We find ourselves with a new subgoal: "how can we represent
time and history in a purely logical way?", which we will need to answer before
we can implement our memory blocks as a symbolic computation. To this end, in
the next chapter we will look further into what it means to be a machine.

