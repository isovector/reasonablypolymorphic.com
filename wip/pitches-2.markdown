---
layout: post
title: Voice Leadings on Abstract Musical Pitches
date: TO_BE_DETERMINED
comments: true
tags: haskell, music, scales
---

In the last post, we discussed the notion of [abstract musical
pitches][pitches-1]. I was writing that under a haze of covid-inspired
single-parenting, so we're going to take a few more minutes to try to clarify
some of the claims made in that one, before moving on to doing more interesting
things with the concept.

[pitches-1]: /blog/pitches-1

In Haskell we have this function `quotRem :: Integral a => a -> a -> (a, a)`,
which computes the quotient and remainder of one number divided by another. For
example, `quotRem 25 5 == (5, 0)`, `quotRem 25 6 == (4, 1)`, `quotRem 25 7 ==
(3, 4)`. You get the picture.

Our `Deg n` type from yesterday operates over `quotRem _ n`. That is, any degree
we might have, say `k :: Deg n`, we compute its `quotRem k n` to get `(octave,
pitchClass)`. This motivates why we were using functions `Fin n -> Fin m` to
model "scales" mapping from `Deg n` into `Deg m` --- we want to map *only* the
`pitchClass` part of the `quotRem`.

To be more precise, if we want to map a `Deg n` into `Deg m`, we run this
function:

```haskell
scale :: (Fin n -> Fin m) -> Deg n -> Deg m
scale f (Deg dn) =
  let (oct, pc) = quotRem dn n
   in Deg $ fromEnum (f (toEnum pc)) + oct * m
```

This mapping only of pitch classes ensures we maintain the quotienting structure
of `Deg n` that requires `k + n` to be the same pitch class as `k`.

Musically, none of this should be unfamiliar. In a diatonic scale, you have 7
distinct notes --- let's label them "do, re, mi, fa, sol, la, ti." These
correspond to `0, 1, 2, 3, 4, 5, 6 :: Deg 7`. If you start at any of these notes
and go up (or down) 7 times, you will get back to the same pitch class an octave
higher (or lower.)

The same argument works for the chromatic scale, where we have 12 notes, labeled
"A, A#, B, C, C#, D, D#, E, F, F#, G, G#". Express these as `0, 1, ..., 11 ::
Deg 12`, and then go up or down 12 spots and you end up back where you were,
modulo an octave.

Similarly, if we want to map from the diatonic scale (`Deg 7`) to the chromatic
scale (`Deg 12`), we choose 7 pitch classes from the 12 available, and respect
the octave equivalence (this mapping is given implicitly by a *key signature*
and, in notated music, a *clef.*)

If none of these music words make any sense to you, don't worry. It doesn't
matter.


## Intrinsic Scales

Check this out: nothing says we need to have a statically-known-at-compile-time
`n` for our `Deg n`. As an illustration, here's the beginning of the Star Wars
theme:

![Star Wars Theme](/images/music6/out1.cropped.svg)

Out of the 7 diatonic pitch classes, this segment of the theme uses only five:
**do**, **re**, mi, fa, **sol**, **la**, **ti**. So we can project the Star Wars
theme down to a 5-note clef:

![Intrinsic Star Wars Theme](/images/music6/out2.cropped.svg)

<!--
threeClef = {
  \override Staff.Clef.stencil = #ly:text-interface::print

  \override Staff.Clef.text = \markup {
    \vcenter \fontsize #6 \bold "5"
  }

  \set Staff.clefPosition = 0

  \set Staff.middleCPosition = 0
}
-->




and give a mapping:

```haskell
starWarsScale :: Deg 5 -> Deg 7
starWarsScale 0 = 0
starWarsScale 1 = 1
starWarsScale 2 = 4
starWarsScale 3 = 5
starWarsScale 4 = 6
```

which, of course, when we apply that mapping back to the 5-note version, gives
us back the song we started with. But before transforming it back, we can do
funny things, like `fmap (+ 1)` in the 5-note scale:

![(+1) Intrinsic Star Wars Theme](/images/music6/out3.cropped.svg)

Mapping this back to `Deg 7` (and then all the way to concrete pitches) gives us
this neat little take on Star Wars:

!["Developed" Star Wars Theme](/images/music6/out4.cropped.svg)

<audio controls>
  <source src="/images/music6/starwars2.mp3" type="audio/mpeg">
  Your browser does not support the audio element.
</audio>

Not as good as John Williams' to be sure, but it's interesting that we can do
this transformation!

All of this is to say that for *any* `Foldable` and `Functor` collection of
notes, we can get its intrinsic scale via `intrinsic`:

```haskell
intrinsic
  :: (Foldable f, Functor f)
  => f (Deg n)
  -> (forall i. (Fin i -> Fin n) -> f (Deg i) -> r)
  -> r
```

which is "you give me some collection of `Deg n`s, and I'll give you back a
collection of `Deg i`s, as well as a scale from `Fin i -> Fin n`". Where `i` is
some unknown-at-compile-time number corresponding to however many unique
pitch-classes were in your collection.

As we have seen with the Star Wars example, we can find the `intrinsic` scale
for horizontal structures.[^sorta] But of course, this is parameterized over any
`Functor`/`Foldable` type constructor `f`. So we can find lots of intrinsic
scales --- think chords and vertical structures. But probably also more things
if I were more imaginative!

[^sorta]: With some finagling, granted. Those `Event`s end up being pretty
    annoying to have to work around! This is a pretty good indication that
    everyone emailing me saying "you don't need to model discreteness" are
    probably right, but I don't actually know how to make that happen.


## Efficient Voice Leadings

We are going to need a few "scales" to work with in this section. We'll take
two common mappings from Western tonal music, namely the 3-in-7 mapping
("triads"), and the 7-in-12 mapping ("the diatonic scale".)


```haskell
triad :: Fin 3 -> Fin 7
triad 0 = 0
triad 1 = 2
triad 2 = 4

diatonic :: Fin 7 -> Fin 12
diatonic 0 = 0
diatonic 1 = 2
diatonic 2 = 4
diatonic 3 = 5
diatonic 4 = 7
diatonic 5 = 9
diatonic 6 = 11
```

If you are not classically-trained in music, don't worry very much about this.
You'd recognize these sounds if you heard them. For example, the triad mapping
sounds like any of the examples from the Wikipedia page on
[arpeggios][arpeggiation]. The diatonic mapping sounds like [this][diatonic].
We're just arbitrarily choosing some ways of mapping between our abstract
degrees (in a way that happens to line up with the arbitrariness of Western
musical tradition.)

[arpeggiation]: https://en.wikipedia.org/wiki/Arpeggio
[diatonic]: https://youtu.be/vTJhpjIA0Fc?t=10

In [Tonality][tonality] Tymoczko points out that these mappings happen to pretty
evenly divide the octave. To illustrate what this means, look at `triad`: it
maps `0..6 :: Deg 3` to `0, 2, 4, 7, 9, 11 :: Deg 7`, which if you take the
difference between any two subsequent degrees in the image is `2, 2, 3, 2, 2`.
That's about as evenly as you *could* map these things! There's a tiny little
bump in the pattern going from 4 to 7.

[tonality]: https://dmitri.mycpanel.princeton.edu/tonality-an-owners-manual.html

The same thing happens in `diatonic`. We map `0..8 :: Deg 7` to `0, 2, 4, 5, 7,
9, 11, 12, 14 :: Deg 12`, which again, taking the difference between subsequent
numbers is `2, 2, 1, 2, 2, 2, 1, 2`. Very evenly spaced!

Note that this doesn't actually need to have been the case! This is a property
of `triad` and `diatonic`, not of `Deg {3,7,12}`. And Tymoczko makes a pretty
compelling argument that this property is *why* Western music has historically
been organized around `triad` and `diatonic`.

So why is this important? It's to do with the *slight non-regularity* in scale
degrees. A big theme of [Tonality][tonality] is that we can very-nearly
offset movement in `Deg m` with an opposite movement in `Deg n`, and that this
is musically interesting (and ubiquitous!)

For example, when working with `triad`, it happens that moving *up* by two steps
in the intrinsic scale (`Deg 3`) is almost exactly cancelled out by moving
*down* five steps in the containing scale (`Deg 7`):

![Up by 2, down by 5](/images/music6/out5.cropped.svg)

The second chord (black note-heads) here is the first one moved up by `2 :: Deg
3`, while the third chord is the second one moved down by `5 :: Deg 7`. As you
can see, we end up *almost exactly* where we started, except that the bottom
pitch has moved one step down.

In fact, this phenomenon happens again and again if we continue performing these
moves. As before, the movement in the intrinsic scale is shown with black
note-heads, while the movement in the containing scale is shown with white ones.

![Again and again](/images/music6/out6.cropped.svg)

Sure enough, this makes pretty pictures. And if you can read the musical
notation, you'll know that what we happen to be computing here are *efficient
voice leadings* from a root note to the diatonic third above it.

In fact, if we remove the in-between black notes, we end up with this:

![Efficient Voice Leadings](/images/music6/out7.cropped.svg)

which sounds like this:

<audio controls>
  <source src="/images/music6/voiceleading.mp3" type="audio/mpeg">
  Your browser does not support the audio element.
</audio>

This is likely the sort of thing which is pretty exciting if you're a musician,
and "who cares" if you're not. It doesn't really *sound* like music, but this is
in a very real sense *a fundamental building block* of (Western) music. It's a
way of smoothly getting from one place to another in a musical space. Any time
you *don't* notice a jarring chord change, this is likely the mechanism by which
the music is moving.


## Modal Modulations

We can do the same move with 7-in-12 modulations. If we look at the notes of the
diatonic (C major) scale as a vertical chord:

![C Major](/images/music6/out8.cropped.svg)

<!-- \header { tagline = "" } -->
<!-- \absolute -->
<!--   \new Staff = "up" -->
<!--   << -->
<!--     \accidentalStyle forget -->
<!--     \new Voice -->
<!--     { -->
<!--       \omit Staff.TimeSignature -->
<!--       \cadenzaOn -->

<!--       \fixed c { <c' d' e' f' g' a' b'>2 -->
<!--                  } } -->
<!--   >> -->
<!-- \paper { -->
<!-- ragged-last = ##t -->
<!-- } -->



Now if we map it up by 4 scale degrees, and down by 7 chromatic degrees we end
up here:

![C Mixolydian](/images/music6/out9.cropped.svg)

<!-- \header { tagline = "" } -->
<!-- \absolute -->
<!--   \new Staff = "up" -->
<!--   << -->
<!--     \accidentalStyle forget -->
<!--     \new Voice -->
<!--     { -->
<!--       \omit Staff.TimeSignature -->
<!--       \cadenzaOn -->

<!--       \fixed c { <c' d' e' f' g' a' b'>2 -->
<!--                  <g' a' b' c'' d'' e'' f''>4 -->
<!--                  <c' d' e' f' g' a' bes'>2 -->
<!--                  } } -->
<!--   >> -->
<!-- \paper { -->
<!-- ragged-last = ##t -->
<!-- } -->

which is either [C mixolydian][mixo], or a smooth voice-leading into F major,
depending on how you look at it.

[mixo]: https://en.wikipedia.org/wiki/Mixolydian_mode

Making the same up 4 down 7 move again now moves us into [C dorian][dorian], or
Bb major, again, depending on your perspective.

[dorian]: https://en.wikipedia.org/wiki/Dorian_mode

![C Dorian](/images/music6/out10.cropped.svg)

Of course, I didn't just pick the +4-7 thing out of my brain. Tymoczko has a
[great tool][cs] for computing the moves involved here, and it works for any
sized chord inside of any sized scale.

[cs]: https://www.madmusicalscience.com/cs.html


## Wrapping Up

A weird one today. Not much in the way of Haskell, and either *fascinating* or
dead boring (depending on how much imagination you have) if you're into the
music theory. In the next post we'll see about how to formalize all of this into
first-class objects. And then we might be getting somewhat close to actually
making some music. Maybe?

