---
layout: post
title: New Notation for Abstract Scales
date: 2026-11-21 16:33
comments: true
tags: music, notation
---

HA HA HA I SNUCK OUT AND DID SOME MUSIC!!! (after some encouragement from my
wife!)

Anyway, just a quick little update on some new notation I've been working on.
Hopefully this will more clearly elucidate the points I'm trying to make with
these [abstract scales][scales] and [generalized accidentals][accs].

[scales]: /blog/notes-scales/
[accs]: /blog/accidentals/

Here's what the new notation looks like:

![3 Octaves of a 4-Note Scale](/images/music8_2/out8.cropped.svg)

This is a 3-octave run in a 4-note scale. How can you tell it's in a 4-note
scale? Because the clef is a big "4".

In the first bar, we have an `-4` ottava bracket, which means we ought to read
this bar to be one octave lower than it's notated. The second bar is missing
this bracket, and is therefore one octave up. And the third bar is an octave
higher again.

As a couple of landmarks: the bottom staff line is always a "root" or a "tonic"
in this scale. That's why both the first and second bars start on the bottom
staff line. There is always a second octave notated, as indicated by the line
straddled by the `}:` symbol in the clef. If you look, this line is where the
third measure starts.

What exactly does this scale "sound" like, you might be wondering? It doesn't
sound like anything; it's just twelve steps in some arbitrary 4-note scale. We'd
have to pin down exactly what that scale was in order to be able to realize it
into something audible.

Let's take another example. This next one is a 5-octave run in a 3-note scale:

![5 Octaves of a 3-Note Scale](/images/music8_2/out5.cropped.svg)

The conventions are exactly the same here. Each measure spans an octave, and
each measure is an octave above the previous one. The bottom staff line is still
the tonic, but here, the *second staff space* is the one straddled by the `}:`.
Again, this acts as a little landmark for where the next octave lands. Notice
that bar 3 begins on this space.

The only other thing to notice here is we have a +6 ottava in the last two bars.
This is indicate it's *two octaves* above what's notated. It's +6 because we're
two octaves above in a 3-note scale, and you shouldn't be surprised to learn
that `3 * 2 = 6`.

Let's take this same 5-octave in a 3-note scale and *transform* it into a 7-note
scale. The way we're going to do that is via this mapping:

```haskell
triad :: Note 3 -> Note 7
triad 0 = 0
triad 1 = 2
triad 2 = 4
```

Here you should read `0` is the root of the scale, `1` as the next note above
that, `2` as the next note again, etc. In our 3-note scale, we only have three
notes, so giving a mapping for each of `0`, `1`, and `2` is sufficient to map
every pitch class out of the scale. Here we're mapping to *every other* note in
a 7-note scale, which when you look at it, is exactly how we build diatonic
triads. Take every second note in the 7-note scale, and that gives you a triad!

So when we apply this mapping over our 3-note scale example, we end up with
*arpeggiation of a triad* over 5 octaves:

![5 Arpeggiations in a 7-Note Scale](/images/music8_2/out6.cropped.svg)

Technically this is an *abstract* 7-note scale, but we can choose to interpret
it as the usual diatonic scale. As a matter of convention, we will map the tonic
of our abstract 7-note to C in the diatonic scale. This brings us back to
everyday musical notation that should be familiar to practitioners:

![5 Arpeggiations in the Diatonic Scale](/images/music8_2/out7.cropped.svg)

Notice that this diagram carries *exactly the same information* as the previous
one, so it can be useful as a sort-of Rosetta Stone to help get an intuition for
what the abstract notation is trying to articulate.


## A More Musical Example

So that's a quick little primer on the notation. But now let's try something a
little more musical. We can bring in the same motif that we [used
previously][accs]:

![Motif in a 3-Note Scale](/images/music8_2/out1.cropped.svg)

You'll notice the familiar "abstract 3 clef". The only new thing in this example
are the accidentals. Unlike in a previous post, they are now using standard
sharps/flats/natural symbols. But they also have little subscripts --- the third
note has a subscript 7 and the fourth note has a subscript 12.

These subscripts express *which scale* we want to apply the accidental to. The
`#/7` means "move up one scale degree in a 7-note (diatonic) scale". The "b/12"
means "move down one scale degree in a 12-note (chromatic) scale."

We'll expand this out momentarily to get some intuition as to what this means
musically.

Let's repeat the motif 3 times, each time up a single scale degree:

![Repeated Motif in a 3-Note Scale](/images/music8_2/out2.cropped.svg)

Using the same `triad` mapping as before, we can move this repeated motif into
an abstract 7-note scale:

![Repeated Motif in a 7-Note Scale](/images/music8_2/out3.cropped.svg)

There are two things to notice here. The first is that this thing looks much
less like an arpeggiation than our first example. And the second is that the
`#/7`s are gone! These two facts are related to one another.

Recall that `#/7` was notation for "move up one note in a 7-note scale". And so
now that we're *in* a 7-note scale, we can drop the notation and *just move up
one note.* But since we haven't yet moved into a 12-note scale, we can't do the
same procedure to the `b/12`s, and so those accidentals remain.

Let's now reinterpret this abstract 7-note scale as the usual diatonic scale:

![Repeated Motif in the Diatonic Scale](/images/music8_2/out4.cropped.svg)

which again should be familiar ground to musicians. You'll notice that the
`b/12` have been replaced by simple flats, because standard music notation
actually expresses the diatonic scale, and uses accidentals to express chromatic
moves.

Check out this music we've composed! What was once a very simple pattern in
`Note 3` now has some character!


## By Way Of Some Other Mappings

Of course, nobody says we need to interpret our 3-note scale as *triads*. We
could instead take our same repeated motif and map it into a 5-note scale. To
pick a mapping at random, let's go with:

```haskell
toFive :: Note 3 -> Note 5
toFive 0 = 0
toFive 1 = 3
toFive 2 = 4
```

Applying this mapping gives us the "same motif" but now in a 5-note scale:

![Repeated Motif in a 5-Note Scale](/images/music8_2/out9.cropped.svg)

We can interpret this 5-note scale as a major pentatonic, which then gives us

![Repeated Motif in Major Pentatonic](/images/music8_2/out10.cropped.svg)

Or we could interpret it as the minor pentatonic:

![Repeated Motif in Minor Pentatonic](/images/music8_2/out11.cropped.svg)

We keep using that same 3-note scale motif, but we keep getting different
results because we keep taking it through different paths on its way up to the
diatonic scale.


## Using a Chord as a Scale

Let's try another trick. Let's take our repeated motif and this time map it into
a 4-note scale. So far all of our transformations have preserved octave
relationships (that is to say, if two notes are one octave apart before we
map them, they are one octave apart after we map them.) But music is supposed to
be *free, man.* There are no rules here. So let's just reinterpret the motif as
a 4-note scale:

![Reinterpreted Motif in a 4-Note Scale](/images/music8_2/out12.cropped.svg)

Now instead of giving a constant mapping from our 4-note scale into something
playable, let's instead give a dynamic mapping. For example, here's a nice chord
progression:

![A Nice Chord Progression](/images/music8_2/out13.cropped.svg)

You'll notice that each of these chords has four notes. And we have a motif that
is in a 4-note scale... so what if we to map our motif to the notes of the
progression?

The details here are pretty finicky, so I've notated this one as a grand staff.
The first system is the chord progression, the second is the 4-note scale motif.
The third system is the chord tones that get targeted by each note in the motif,
and the final system is after we have applied all the accidentals from the motif
to the targeted chord tones.

![Derivation of Our Motif Over Chords](/images/music8_2/out14.cropped.svg)

Remember that the bottom line on the 4-note staff represents the "tonic" note,
which is the lowest note of each chord. So because the first note of the motif
is on the tonic, and the lowest note of the first chord is F, the resulting note
is F.

The note in our motif is just the next 4-note above the tonic, which is the
second note in our chord, thus we get an Ab.

But the third note of the motif is a `#/7` above the second note in the chord.
So since the second note in our chord is Ab (third system), one diatonic step
above that is Bb (fourth system).

The fourth note of the motif is a `b/12` below the next note in the chord. The
next note of the chord is C, so we lower it by a flat and get Cb. And then the
last note of the motif is just the same note of the chord, but this time without
the flat --- thus C.

That's the derivation of the first bar. So far, so good. The second bar makes
things a little trickier. This time the motif starts on the first space, which
is to say it begins on the *second* note up the chord. Since the motif only
touches three notes of the chord, in the second bar we will be ignoring the root
note of the chord (the low F).

It's worth tracing through the details on this example. It's finicky, but really
makes you appreciate why we might want to use computers to calculate this stuff
on our behalf.

As one final step, we might want to take the last system of our derivation and
"renormalize" it --- changing the spelling of the notes so they feel a little
more natural:

![Renormalized Results](/images/music8_2/out15.cropped.svg)

Whew! We made it to the end!

If you're been paying attention to the [whole series][all] of blog posts, there's
nothing *new* here, but perhaps having a few more worked examples might help
some of the ideas land. And again, none of these are *my* ideas --- they all
come from [Tonality][tonality].

[all]: /tags/music.html
[tonality]: https://www.foyles.co.uk/book/tonality/dmitri-tymoczko/9780197577103

What is mine is the notation, which I think can help with understanding. Of
course, you'd never actually *want* to do any of these transformations by hand,
but seeing them illustrated in full might perhaps pull back the curtains on
composition.

Perhaps what set apart the great composers of yore was not their musical genius,
but their patience to work through the details of all these fiddly
transformations.


<!-- \new GrandStaff -->
<!-- { -->
<!-- << -->
<!-- \new Staff -->
<!-- { -->
<!--   { \clef treble \accidentalStyle modern-cautionary -->
<!--     \fixed c { <f' aes' c'' des''>1 -->
<!--                | -->
<!--                <f' ges' b' des''>1 -->
<!--                | -->
<!--                <d' ges' a' cis''>1 } } -->
<!-- } -->


<!-- \new Staff -->
<!--   { \finStaff #4 -->
<!--     \finClef #4 -->
<!--     \accidentalStyle modern-cautionary -->
<!--     \fixed c { c'4 -->
<!--                d'4 -->
<!--                \acc #'((7 . 1)) d'8 -->
<!--                \acc #'((12 . -1)) e'8 -->
<!--                e'4 -->
<!--                | -->
<!--                d'4 -->
<!--                e'4 -->
<!--                \acc #'((7 . 1)) e'8 -->
<!--                \acc #'((12 . -1)) f'8 -->
<!--                f'4 -->
<!--                | -->
<!--                e'4 -->
<!--                f'4 -->
<!--                \acc #'((7 . 1)) f'8 -->
<!--                \acc #'((12 . -1)) g'8 -->
<!--                g'4 } -->
<!--   } -->


<!-- \new Staff -->
<!-- { -->
<!--   { \clef treble \accidentalStyle modern-cautionary -->
<!--     \fixed c { f'4 -->
<!--                aes' -->
<!--                aes'8 -->
<!--                c''8 -->
<!--                c''4 -->
<!--                | -->
<!--                ges' -->
<!--                b' -->
<!--                b'8 -->
<!--                des''8 -->
<!--                des''4 -->
<!--                | -->
<!--                a' -->
<!--                cis'' -->
<!--                cis''8 -->
<!--                d'' -->
<!--                d''4 -->
<!--                } } -->
<!-- } -->



<!-- \new Staff -->
<!--   { \clef treble \accidentalStyle modern-cautionary -->
<!--     \fixed c { f'4 -->
<!--                aes'4 -->
<!--                bes'8 -->
<!--                ces''8 -->
<!--                c''4 -->
<!--                | -->
<!--                ges'4 -->
<!--                b'4 -->
<!--                c''8 -->
<!--                deses''8 -->
<!--                des''4 -->
<!--                | -->
<!--                a'4 -->
<!--                cis''4 -->
<!--                dis''8 -->
<!--                des''8 -->
<!--                d''4 } } -->

<!-- >> -->
<!-- } -->


<!-- \paper { -->
<!-- ragged-last = ##t -->
<!-- } -->

