---
layout: post
title: Musical Signals
date: 2026-11-03 05:01
comments: true
tags: music, functional programming
---

The [last blog][overview] post served as an overview of my music project --- what it is,
why it is, and roughly what success will look like. Today we'll get into some of
the nitty gritty details that will help put the project onto a firm footing.

In order to have any chance of [not confusing ourselves][deno], we must first be
precise about what exactly it is we're talking about. That means we'll have to
model out some types, and, importantly *what those types mean.* Recall that one
of our [desiderata][overview] is that whatever it is we're building must be
capable of expressing any music from any culture from any time period, including
those times and cultures which do not yet exist.

[deno]: https://www.youtube.com/watch?v=rlyqoYoUumc

The trick then is to make a series of *extensible* types, each one providing
some aspect of functionality, and letting people compose them together for
themselves. Future users can add their own types with their own functionality,
and reuse as much of the system that is meaningful to reuse.

By my reckoning, music is made up of some combination of the following:

1. *some notion of time,* generally considered to be rhythmic content, or
   "horizontal structures."
2. *some notion of simultaneity,* generally considered to be chords, polyphony,
   or "vertical structures."
3. *things that can happen,* generally considered to be musical content of some
   sort. Perhaps this is pitches (as in musical scores), or waveforms (as in
   musical playback.)

As a placeholder to get our bearings, let's imagine the first two elements as
types:

```haskell
type Horizontal a
type Vertical a
```

and postulate both a `Pitch` and `Waveform` type for item three:

```haskell
type Pitch
type Waveform
```

By composing these types in different ways, different ideas of music fall out.
Several examples:

1. `Horizontal ()` describes purely time-based structures; eg. rhythmic ideas
2. `Horizontal Pitch` is a simple tune, the sort you can whistle
3. `Vertical Pitch` is a single chord.
4. `Horizontal (Vertical Pitch)` is what you get at a campfire from someone who
   only knows how to play chords on the guitar. In the jargon, this is
   "polyphonic" music.
5. `Vertical (Horizontal Pitch)` is multiple independent tunes happening
   simultaneously. In the jargon, this is ["contrapuntal" music][counterpoint].
6. `Vertical (Horizontal Waveform)` is what you get in a [DAW][daw] --- independent
   tracks, each of which lets you move recorded samples along its own timeline.

[counterpoint]: https://en.wikipedia.org/wiki/Counterpoint
[daw]: https://en.wikipedia.org/wiki/Digital_audio_workstation

Of course, this is all vibes right now, since we haven't discussed what exactly
any of these types *actually are.* But this should be enough to wet your
whistle; if we can deliver types that match these vibes, we clearly have an
amazing starting point.

As a point of note, this first step is where I went wrong in my [last public
attempt][blog1]. There I postulated that *all* music is what here would be
described as `Vertical (Horizontal a)`. And I gave unsatisfying answers for what
`Vertical` and `Horizontal` are, to boot!

[blog1]: /blog/more-algebraic-music/

Shame. Sorrow.

Anyway. Let's leave `Vertical` alone for now, and focus our attention on
`Horizontal`, since it seems to be the crux of the interesting stuff here.
However, rather than using up the musically-relevant name `Horizontal`, let's go
with `Signal`, since we're going to be building up this idea in several pieces.

By our vibes, a `Signal` is a time-based structure. Which is
to say, it ought to describe two things: 1) what happens, and 2) when it
happens. That's a pretty big constraint on the search space; the only other
question is whether it ought to be continuous or discrete. In the continuous
case, we have:

```haskell
μ (Signal a) = Time -> a
```

and in the discrete:

```haskell
μ (Signal a) = [(Time, a)]  -- ordered by monotonically ascending Time
```

where `μ` should be read as "the meaning of." That is to say, we're trying to
pin down the *semantics* of `Signal` without saying anything about *how
we're actually going to implement this thing.*

**This is my first point of confusion.** Composition (in the programming sense)
is significantly better with the `Time -> a` denotation, but when I *listen to
music* I "hear" it "discretely." I think. Maybe. Like I said, I am confused.

Rather than choose between these two options, I am **cheating** and choosing
BOTH. HA HA HA. This is intellectually dishonest, but it's a decision that needs
to be made early on, and making progress seems to be dependent on choosing
*something.* Hopefully when everything has clarified down the road, we can
return to this decision and make a better choice.

Sorry, let me back up. What the hell am I talking about? I have the advantage
of knowing where I'm going, so I imagine it's pretty disjointed without that.
Concretely, I am torn between a few things:

1. The discrete choice *vibes better* with my classical piano training, where
   "music" is rendered as a score with discrete symbols on a page
2. I have a strong bias towards being able to generate these symbols on a page
   with this system I'm making
3. But the discrete choice doesn't admit nearly as much algebraic structure. For
   example, it seems very desirable to have an applicative structure on
   `Signal`. The usual list applicative is seems musically meaningless
   (taking the cartesian product of all the notes in a piece? yeah ok). What
   seems more likely is a pointwise "zippy" applicative. But in a discrete
   framing, *there isn't enough data* to combine two `Signal` structures
   that are out of phase with one another.

So, the unsatisfying solution here is to just do both. Rather than picking
between a discrete and a continuous representation, just keep both around:

```haskell
μ (Signal a) = (Time -> a, Set Time)
```

That is, represent the `Signal` structure as a continuous function out of
time, *but also keep track of a set of interesting times!*

We get quite a lot of nice algebraic structure on top of this thing:

```haskell
μ (Signal a) = (Time -> a, Set Time)

instance Functor Signal where
  μ (fmap f a) = first (fmap f) (μ a)

instance Applicative Signal where
  μ (pure a) = (const a, mempty)
  μ (liftA2 f a b) = (liftA2 f *** (<>)) (μ a) (μ b)

instance Semigroup a => Semigroup (Signal a) where
  μ (a <> b) = μ a <> μ b

instance Monoid a => Monoid (Signal a) where
  μ mempty = mempty

instance Foldable Signal where
  μ (foldMap f a) = uncurry foldMap (μ a)
```

which I always take as a sign that I'm on the right track.

Armed with `Signal`, we can give some rudimentary combinators on it. For
example, we can lift functions:

```haskell
lift :: (Time -> a) -> Signal a
μ (lift f) = (f, mempty)
```

and we can generate stepwise signals:

```haskell
stepwise :: a -> [(Time, a)] -> Signal a
μ (stepwise a0 []) = pure a0
μ (stepwise a0 ((t0, a) : as)) = \t ->
  case t < t0 of
    True -> a0
    False -> μ (stepwise a as)
```

Attentive readers will notice that nothing yet ever actually introduces any
times-of-interest into a `Signal`. Here is where my earlier belly-aching comes
back to bite. I'd LIKE VERY MUCH to be able to say "discrete `Signal`s have a
different type than continuous ones." So maybe we add an `Event` type:

```haskell
μ (Event a) = Maybe a
```

and then say we can make *discrete* signals:

```haskell
discrete :: [(Time, a)] -> Signal (Event a)
μ (discrete as) = (\t -> lookup t as, Set.fromList $ fmap fst as)
```

with the implicit promise that if you have a `Signal (Event a)` *then it must be
a discrete `Signal`!* Unfortunately, this is not the sort of promise we can
keep; it's trivial to construct a densely packed `Signal` of `Event`s:

```haskell
notActuallyDiscrete :: Signal a -> Signal (Event a)
μ notActuallyDiscrete = fmap Just . μ
```

Alas. Shame. Sorrow.

Nevertheless, we are just going to **ignore** this issue, and **pretend** like
any `Signal (Event a)` must be discrete and sparse! I am eminently aware of how
disappointed [Conal][conal] would be by my motivated reasoning here. I'm
disappointed in myself! Unfortunately I don't have a better answer other than to
split up the continuous and discrete cases, but that throws away a bunch of the
compositionality that I want. **I am confident there is a better solution here**
but damned if I know what it is.[^no-constructors]

[conal]: http://conal.net/

[^no-constructors]: One titillating idea is to simply not expose any
    introductory forms for `Event`. I haven't explored this much, since it would
    mean we don't get an applicative functor over `Event`. Thinking about it
    now, it'd still be fine to expose the `Nothing`-analogous constructor, so we
    could still give `mempty`. And perhaps this is the first motivating case
    I've ever found for giving only a [`Apply`][apply] instance instead of a
    full `Applicative`.

[apply]: https://hackage-content.haskell.org/package/semigroupoids-6.0.2/docs/Data-Functor-Apply.html#g:2

Anyway, I'm writing this in the darkness at 5am before my family awakens, but I
hear stirring so it's probably time to stop. If you have any lovely ideas about
how to solve this discrete/continuous discrepancy, I'd love to hear them.

Next we'll look at signal functions, and give to-my-knowledge a novel
application of `Arrow`s for music.

