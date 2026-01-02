---
layout: post
title: An Algebraic Theory of Music
date: 2026-01-02 14:27
comments: true
tags: music, haskell, denotational design, functional programming, types
---


In my last post, I was [struggling towards an algebraic theory of
music.](/blog/algebraic-music/) This idea has been burning in my mind ever
since, and I wanted to give some updates with where I've landed.


## Differentiating Voices from Music

We begin by modeling a [musical
voice](https://en.wikipedia.org/wiki/Part_(music)#Polyphony_and_part-writing),
which is, roughly speaking, the abstract version of a human voice. The voice can
be doing one thing at a time, or can choose to not be doing anything.

Voices are modeled by [step
functions](https://hackage.haskell.org/package/step-function), which are
divisions of the real line into discrete chunks. We interpret each discrete
chunk as a note being played by the voice for the duration of the chunk.

This gives rise to a nice applicative structure that I alluded to in my previous
post:

```
liftA2 f
  |---- a ----|-- b --|
  |-- x --|---- y ----|
=
  |- fax -|fay|- fby -|
```

where we take the union of the note boundaries in order to form the
applicative. If either voice is resting, so too is the applicative. There is
also an `Alternative` instance here, which chooses the first non-rest.

There is a similar monoidal structure here, where multiplication is given by
"play these two things simultaneously," relying on an underlying `Semigroup`
instance for the meaning of "play these two things:"

```haskell
instance Semigroup a => Semigroup (Voice a)
instance Semigroup a => Monoid (Voice a)
```

If either voice is resting, we treat its value as `mempty`, and can happily
combine the two parts in parallel.

All of this gives rise to the following rich structure:

```haskell
newtype Voice a = Voice { unVoice :: SF Time (Maybe a) }
  deriving stock
    (Eq, Ord, Show, Functor, Foldable, Traversable, Generic, Generic1)
  deriving newtype
    (Semigroup, Monoid)
  deriving
    Applicative
    via Compose (SF Time) Maybe

instance Filterable Voice
instance Witherable Voice
instance Alternative Voice

-- | Delay a voice by some amount of time.
delayV :: Time -> Voice a -> Voice a
```


## From Voices to Music

Voices, therefore, give us our primitive notion of monophony. But real music
usually has many voices doing many things, independently. This was a point in
which I got stuck in my previous post.

The solution here, is surprisingly easy. Assign a `Voice` to each voice name:

```haskell
newtype Music v a = Music
  { getVoices :: v -> Voice a
  }
  deriving stock
    (Functor, Generic, Functor)
  deriving newtype
    (Semigroup, Monoid)
  deriving (Applicative, Alternative)
    via Compose ((->) v) Voice

instance Profunctor Music

instance Finite v => Foldable (Music v)
instance Finite v => Traversable (Music v)
instance Filterable (Music v)
instance Finite v => Witherable (Music v)
```

We get an extremely rich structure here completely for free. Our monoid combines
all voices in parallel; our applicative combines voices pointwise; etc. However,
we also have a new `Profunctor Music` instance, whose characteristic `lmap :: (b
-> c) -> Music c a -> Music b a` method allows us to trade lines between voices.

In addition to the *in-parallel* monoid instance, we can also define a [tile
product](https://dl.acm.org/doi/10.1145/2633638.2633649) operator over `Music
v a`, which composes things sequentially[^also-otherwise]:

```haskell
duration :: Music v a -> Time

(##) :: Semigroup a => Music v a -> Music v a -> Music v a
m@(Music m1) ## Music m2 =
    Music $ liftA2 (<>) m1 $ fmap (delayV $ duration m) m2
```

[^also-otherwise]: Strictly speaking, the tile product can also do parallel
    composition, as well as sychronizing composition, but that's not super
    important right now.

The `Semigroup a` constraint on `(##)` arises from the fact that the pieces of
music might extend off to infinity in either direction (which `pure @Voice` must
do), and we need to deal with that.

There are a few other combinators we care about. First, we can lift anonymous
voices (colloquially "tunes") into multi-part `Music`:

```haskell
voice :: Eq v => v -> Music () a -> Music v a
voice v (Music sf) = Music $
  \case
    ((== v) -> True) -> sf ()
    _ -> mempty
```

and we can assign the same line to everyone:

```haskell
everyone :: Music () a -> Music v a
everyone (Music m) = Music $ const $ m ()
```

## Writing Lines

The primitives for building little tunes are

```haskell
note :: Time -> a -> Music () a
rest :: Time -> Music () a
```

which you can then compose sequentially via `(##)`, and assign to voices via
`voice`.


## Harmonic Constraints

One of the better responses to my last blog post was a link to [Dmitri
Tymoczko](https://dmitri.mycpanel.princeton.edu/index.html)'s [FARM 2024
talk](https://www.youtube.com/watch?v=yp5Eys2L_04).

There's much more in this video than I can possibly due justice to here, but my
big takeaway was that this guy is thinking about the same sorts of things that
I am. So I dove into his work, and that lead to his [quadruple
hierarchy](https://www.madmusicalscience.com/quadruple.mp4):

> Voices move within chords, which move within scales, which move within
> macro-harmonies.

Tymoczko presents a `T` algebra which is a geometric space for reasoning about
voice leadings. He's got a lot of fun websites for exploring the ideas, but
I couldn't find an actual implementation of the idea anywhere, so I [cooked one
up](https://github.com/isovector/denomusic/blob/6a313a546cc376bb22f37cec55d76518bff40acd/src/DenoMusic/Harmony.hs)
myself.

The idea here is that we have some `T :: [Nat] -> Type` which describes
a hierarchy of abstract scales moving with respect to one another. For example,
the Western traditional of having triads move within the diatonic scale, which
moves within the chromatic scale, would be represented as `T '[3, 7, 12]`. `T`
forms a monoid, and has some simple generators that give rise to smooth voice
leadings (chord changes.)

Having a model for smooth harmonic transformations means we can use it
constructively. I am still working out the exact details here, but the rough
shape of the idea is to build an underlying field of key changes (represented as
smooth voice leadings in `T '[7, 12]`):

```haskell
keyChanges :: Music () (T '[7, 12])
```

We can then make an underlying field of functional harmonic changes (chord
changes), modeled as smooth voice leadings in `T '[3, 7]`:

```haskell
chordChanges :: Music () (T '[3, 7])
```

Our voices responsible for harmony can now be written as values of type

```haskell
harmonicVoices :: Music h (Set (T '[3]))
```

and we can use the applicative musical structure to combine the elements
together:

```haskell
{-# LANGUAGE ApplicativeDo #-}

extend :: T ns -> T (ns ++ ms)
sink   :: T ns -> T (n ': ns)

harmony :: Music h (Set (T '[3, 7, 12]))
harmony = do
  k <- everyone keyChanges
  c <- everyone chordChanges
  m <- harmonicVoices
  pure $ extend m <> extend c <> sink k
```

which we can later `fmap` out into concrete pitches. The result is that we can
completely isolate the following pieces:

- key changes
- chord changes
- how voices express the current harmony
- the rhythms of all of the above

and the result is guaranteed to compose in a way that the ear can interpret as
music. Not necessarily *good music,* but undeniably as *music.*

The type indices on `T` are purely for my book-keeping, and nothing requires
them to be there. Which means we could also use the applicative structure to
modulate over different sorts of harmony (eg, move from triads to seventh
chords.)


## Melody: Still an Open Question

I haven't quite gotten a feel for melody yet; I think it's probably in `T
'[7, 12]`, but it would be nice to be able to target chord tones as well. Please
let me know in the comments if you have any insight here.

However, I have been thinking about contouring, which is the overall "shape" of
a musical line. Does it go up, and peak in the middle, and then come down again?
Or maybe it smoothly descends down.

We can use the discrete intervals intrinsic inside of `Voice`s to find
"reasonable" times to sample them. In essence this assigns a `Time` to each
segment:

```haskell
timed :: Music v a -> Music v (Time, a)
```

and we can then use these times to then sample a function `Time -> b`. This then
allows us to apply contours (given as regular `Real -> Real` functions) to
arbitrary rhythms. I currently have this typed as

```haskell
contour :: Group a => a -> (Real -> Real) -> Music v () -> Music v a
```

where `a ~ T something`, and the outputted `Real`s get rounded to their nearest
integer values. I'm not deeply in love with this type, but the rough idea is
great---turn arbitrary real-valued functions into musical lines. This
generalizes contouring, as well as scale runs.


## Next Steps?

I'm writing all of this up because I go back to work on Monday and life is going
to get very busy soon. I'm afraid I won't be able to finish all of this!

The types above I'm pretty certain are relatively close to perfect. They seem to
capture everything I could possibly want, and nothing I don't want. Assuming I'm
right about that, they must make up the basis of musical composition.

The next step therefore is to build musical combinators on top. One particular
combinator I've got my eye on is some sort of general `~>` "get from here to
there" operator:

```haskell
(~>) :: (Semigroup a, ???) => Music v a -> Music v a -> Music v a
```

which I imagine would bridge a gap between the end of one piece of music with
beginning of another. I think this would be roughly as easy as moving each voice
linearly in `T` space from where it was to where it needs to be. This might need
to be a ternary operation in order to also associate a rhythmic pattern to use
for the bridge.

But I imagine `(~>)` would be great for lots of dumb little musical things. Like
when applied over the chord dimension, it would generate arpeggios. Over the
scale dimension, it would generate runs. And it would make chromatic moves in
the chroma dimension.

Choosing exactly what moves to make for `T`s consisting of components in
multiple axes might just be some bespoke order, or could do something more
intelligent. I think the right approach would be to steal `diagrams`' idea of an
`Envelope`, and attach some relevant metadata to each `Music`. We could then
write `(~>)` as a function of those envelopes, but I must admit I don't quite
know what this would look like.

As usual, I'd love any insight you have! Please leave it in the comments.
Although I must admit I appreciate comments of the form "have you tried $X" much
more than of the form "music is sublime and you're an idiot for even trying
this."

Happy new year!

