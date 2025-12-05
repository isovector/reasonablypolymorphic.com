---
layout: post
title: Struggling Towards an Algebraic Theory of Music
date: 2025-12-04 20:15
comments: true
tags: music, haskell, denotational design, functional programming, types
---

For the last few months, I've been trying to come up with a nice, denotational
basis for what music *is.* But I'm running out of steam on the project, so
I thought I'd write what I've figured out, and what I've tried but doesn't work.
Hopefully this will inspire someone to come tell me what I'm being stupid about
and help get the whole process unstuck.


## What Music Is Not

It's tempting to gesticulate wildly, saying that music is merely a function from
time to wave amplitudes, eg something of the form:

```haskell
μ Music = Time -> Amplitude
```

While I think it's fair to say that this is indeed the underlying denotation of
*sound,* this is clearly not the denotation of *music.* For example, we can
transpose a song up a semitone without changing the speed---something that's
very challenging without a great deal of in the waveform representation. And we
can play a musical phrase backwards, which is probably impossible in a waveform
for any timbral envelope.

Since we have now two examples of "reasonable to want to do" with musical
objects, which cannot be expressed in terms of a function `Time -> Amplitude`,
we must conceed that waveforms-over-time cannot be the denotation of music.


## What Music Might Be

Music is obviously temporal, so keeping the "function from time" part seems
relevant. But a function from time to what? As a first attempt:

```haskell
data Note = Note Pitch Timbre Volume

μ Music = Time -> Set (Duration, Note)
```

which, for a given time, returns a set of notes starting at that time, and how
long they ought to be played for. An immediate improvement would be to
parameterize the above over notes:

```haskell
μ (Music a) = Time -> Set (Duration, a)
```

It's tempting to try to eliminate more of the structure here with our
parametricity, but I was unable to do so. In contrapuntal music, we will want to
be able to express two notes starting at the same moment, but ending at
different times.

One alluring path here could to write monophonic voices, and combine them
together for polyphony:

```haskell
μ (Voice a) = {- something like -} Time -> (Duration, a)
μ (Music a) = Time -> Set (Voice a)
```

Such an encoding has many unfavorable traits. First, it just feels yucky. Why
are there two layers of `Time`? Second, now I-as-a-composer need to make
a choice of which voice I put each note in, despite the fact that this is merely
an encoding quirk. So no, I don't think this is a viable path forward.

So let's return to our best contender:

```haskell
μ (Music a) = Time -> Set (Duration, a)
```

This definition is trivially a monoid, pointwise over the time structure:

```haskell
μ (Music a <> Music b) = Music (μ a <> μ b)
μ mempty = Music mempty
```

If we think about abstract sets here, rather than `Data.Set.Set`, such an object
is clearly a functor. There are many possible applicatives here, but the
pointwise zipper seems most compelling to me. Pictorally:

```
pure a
=
  |----- a ----forever...


liftA2 f
  |---- a ----|-- b --|
  |-- x --|---- y ----|
=
  |- fax -|fay|- fby -|
```

Such an applicative structure is quite nice! It would allow us to "stamp"
a rhythm on top of a pure representation of a melody.

However, the desirability of this instance is a point *against* `μ (Music a)
= Time -> Set (Duration, a)`, since by [Conal Elliott's typeclass morphism
rule](http://conal.net/papers/type-class-morphisms/), the meaning of the
applicative here ought to be the applicative of the meaning. Nevertheless, any
other applicative structure would be effecitvely useless, since it would require
the notes on one side to begin at the same time as the notes on the other. To
sketch:

```haskell
-- bad instance!
liftA2 f (Music a) (Music b) =
    Music (liftA2 (\(d1, m) (d2, n) -> (d1 <> d2, f m n)) a b)
```

Good luck finding a musically meaningful `pure` for such a thing!

Ok, so let's say we commit to the pointwise zippy instance as our applicative
instance. Is there a corresponding monad? Such a thing would substitute notes
with more music. My first idea of what to do with such a thing would be to
replace chords with texture. For example, we could replace chords with broken
chords, or with basslines that target the same notes.

Anyway, the answer is yes, there is such a monad. But it's musically kinda
troublesome. Assume we have the following function:

```haskell
notes :: Music a -> [(Maybe Interval, a)]
```

which will convert a `Music a` into its notes and an optional temporal interval
(optional because `pure` goes on forever.) Then, we can write our bind as:

```haskell
m >>= f = flip foldMap (notes m) \case
  (Nothing, a) -> f a
  (Just (start, duration), a) ->
    offset start $ _ duration $ f a
```

where `offset` changes when a piece of music occurs. We are left with a hole of
type:

```haskell
Duration -> Music a -> Music a
```

whose semantics sure better be that it forces the given `Music` to fit in the
alotted time. There are two reasonable candidates here:

```haskell
scaleTo  :: Duration -> Music a -> Music a
truncate :: Duration -> Music a -> Music a
```

where `scaleTo` changes the local interpretation of time such that the entire
musical argument is played within the given duration, and `truncate` just takes
the first `Duration`'s worth of time. Truncate is too obviously unhelpful here,
since the `>>=` continuation doesn't know how much time it's been given, and
thus most binds will drop almost all of their resulting music.

Therefore we will go with `scaleTo`. Which satisfies all of the algebraic
(monad) laws, but results in some truly mystifying tunes. The problem here is
that this is not an operation which respects musical meter. Each subsequent bind
results in a correspondingly smaller share of the pie. Thus by using only bind
and mconcat, it's easy to get a bar full of quarter notes, followed by a bar of
sixty-fourth notes, followed by two bars full of of 13-tuplets. If you want to
get a steady rhythm out of the whole thing, you need a global view on how many
binds deep you're ever going to go, and you need to ensure locally that you only
produce a small powers-of-two number of notes, or else you will accidentally
introduce tuplets.

It's a mess. But algebraically it's fine.


## What Music Seems Like It Should Be

The above foray into monads seems tentatively promising for amateur would-be
algorithmic composers (read: people like me.) But I have been reading
[several](https://www.goodreads.com/book/show/36288013-musical-composition)
[books](https://www.goodreads.com/book/show/890009.Twentieth_Century_Harmony) on
musical composition lately, and my big takeaway from them is *just how damn
contextual notes are.*

So maybe this means we want more of a comonadic interface. One in which you can
`extend` every note, by taking into account all of the notes in its local
vicinity. This feels just as right as the monadic approach does, albeit in
a completely different way. Being able to give a comonad instance for `Music`
would require us to somehow reckon with having only a single `a` at any given
time. Which appeals to my functional programmer soul, but again, I don't know
how to do it.

But imagine if we did have a comonadic instance. We could perform voice leading
by inspecting what the next note was, and by futzing around with our pitch. We
could do some sort of reharmonization by shifting notes around according to
what else is happening.

But maybe all of this is just folly.

Music as it's actually practiced doesn't seem to have much of the
functionaly-compositional properties we like---ie, that we can abstract and
encapsulate. But music doesn't appear to be like that! Instead, a happy melody
takes a different character when played on major vs minor chords. Adding
a dissonant interval can completely reconceptualize other notes.

It feels like a bit of a bummer to end like this, but I don't really know where
to go from here. I've worked something like six completely-different approaches
over the last few months, and what's documented here is the most promising bits
and pieces. My next thought is that maybe music actually forms
a [sheaf](https://reasonablypolymorphic.com/blog/review-sheafs/), which is to
say that it is a global solution that respects many local constraints.

All of this research into music has given me much more thoughts about *music qua
music* which I will try to articulate the next time I have an evening to myself.
Until then.

