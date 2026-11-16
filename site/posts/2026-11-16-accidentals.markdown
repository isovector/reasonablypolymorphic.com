---
layout: post
title: Generalized Accidentals
date: 2026-11-16 11:09
comments: true
tags: music
---

Just a little note on yesterday's [ornamental offsets][offsets]. I realized
overnight that this idea is way less weird to musicians than originally thought.
The offset idea is really just *generalized accidentals.*

[offsets]: /blog/notes-scales/#some-failed-attempts-at-pinnning-down-scales

Check it out: standard music notation, without ever saying so, assumes a `Fin 7`
scale. The notation maps these degrees alternatingly between lines and
spaces-between-lines. Thus `0..6 :: Deg 7` look like this:

![The Diatonic Scale](/images/music8/out3.cropped.svg)

which correspond to seven contiguous white keys on the piano. But the piano also
has five black keys between any seven contiguous white keys. Adding in the
black keys gets us an additional five pitch classes, which brings us up to the
`Fin 12` scale that Western music is based around.

Modulo some technicalities, there's no way to notate these black keys directly.
The black key between C and D is known either as "C sharp" or "D flat" ---
sharps moving one offset up in `Deg 12`, and flats moving one offset down. Thus
the twelve pitch classes of the chromatic scale are notated either as sharps:

![Chromatic Sharps](/images/music8/out4.cropped.svg)

or equivalently, as flats:

![Chromatic Flats](/images/music8/out2.cropped.svg)

Although it is usually omitted, there is also a "natural" symbol, to indicate
the *absence* of a sharp or a flat. If we include these symbols into our sharps
example, we get this:

![Chromatic Naturals and Sharps](/images/music8/out5.cropped.svg)

which represents exactly the same thing as the "Chromatic Sharps" figure. We're
just being a little more pedantic here.

To drive everything home, these accidental symbols are *exactly* the `Deg 12`
ornaments on a `Note 7` that we were investigating last time. If we change the
`♮` symbol to `0`, the `♯` to `+1` and the `♭` to `-1`, our chromatic scales
look like this:

![Explicit Accidental Sharps](/images/music8/out6.cropped.svg)

![Explicit Accidental Flats](/images/music9/out8.cropped.svg)

Both examples now have "obvious" encodings as `Note 7`s: use the notated pitch
as the `Deg 7`, and the offset as a `stepIn @12`. Thus "Explicit Accidental
Sharps" is encoded as:

```haskell
[ 0
, stepIn @12 1 0
, 1
, stepIn @12 1 1
, 2
, 3
, stepIn @12 1 3
, 4
, stepIn @12 1 4
, 5
, stepIn @12 1 5
, 6
] :: [Note 7]
```

Rather unsurprisingly, when we `applyScale diatonic` over this collection, we
get `[0..11] :: Note 12`, which is just to say that this enumerates all of the
pitch classes in the chromatic scale. And of course it does, because we designed
it that way in the first place!

So this all brings us back to yesterday's `Ornaments` type, which allows us to
express offsets at *any* scale degree --- not just `Deg 12` like sharps and
flats in standard musical notation allow us to target. So let's broaden our
visualization a little more, making it explicit that our chromatic offsets are
in `Deg 12`:

![Deg 12 Explicit Accidentals](/images/music8/out9.cropped.svg)

Now that this has been made explicit, there's no reason why we can't add
*multiple* accidentals to any given note. For example, we could make put a
`stepIn @10 2` on the second note, *in addition to* a `stepsIn @12 (-1)`!

![Mixing Accidentals](/images/music8/out10.cropped.svg)

This one says that if we were to map our `Note 7` into `Note 10`, we'd move the
second note up by `2 :: Deg 10`. Then when we mapped the resulting `Note 10`s
into `Note 12`, we'd move that note again --- this time down by `-1 :: Deg 12`.

<!-- \version "2.24.0" -->

<!-- #(define (parenthesize-naturals grob) -->
<!--    (if (equal? (ly:grob-property grob 'alteration) 0) -->
<!--        (ly:grob-set-property! grob 'parenthesized #t))) -->

<!-- #(define (edo12-accidental-stencil grob) -->
<!--    (let ((alt (ly:grob-property grob 'alteration))) -->
<!--      (cond -->
<!--       ((equal? alt 1/2) -->
<!--        (grob-interpret-markup grob -->
<!--          #{ -->
<!--            \markup \whiteout \pad-markup #0.15 -->
<!--            \sans \bold \fontsize #-6 -->
<!--            \vcenter \override #'(baseline-skip . 0.85) -->
<!--            \center-column { "+1" "12"} -->
<!--          #})) -->
<!--       ((equal? alt -1/2) -->
<!--        (grob-interpret-markup grob -->
<!--          #{ -->
<!--            \markup \whiteout \pad-markup #0.15 -->
<!--            \sans \bold \fontsize #-6 -->
<!--            \vcenter \override #'(baseline-skip . 0.85) -->
<!--            \center-column { "-1" "12"} -->
<!--          #})) -->
<!--       ((equal? alt 0) -->
<!--        (grob-interpret-markup grob -->
<!--          #{ -->
<!--            \markup \whiteout \pad-markup #0.15 -->
<!--            \sans \bold \fontsize #-6 -->
<!--            \vcenter \override #'(baseline-skip . 0.85) -->
<!--            \center-column { "0" "12" } -->
<!--          #})) -->
<!--       (else -->
<!--        (ly:accidental-interface::print grob))))) -->

<!-- \relative c' { -->
<!--   \cadenzaOn -->
<!--   \omit Staff.TimeSignature -->

<!-- % \accidentalStyle dodecaphonic -->
<!-- \override Staff.Accidental.stencil = #edo12-accidental-stencil -->


<!-- c4 -->
<!--   \once \override Accidental.stencil = #ly:text-interface::print -->
<!--   \once \override Accidental.text = \markup { -->
<!--     \concat { -->
<!--         \whiteout \pad-markup #0.15 -->
<!--         \sans \bold \fontsize #-6 -->
<!--         \vcenter \override #'(baseline-skip . 0.85) -->
<!--         \center-column { "+2" "10"} -->

<!--       \hspace #0.2 -->

<!--         \whiteout \pad-markup #0.15 -->
<!--         \sans \bold \fontsize #-6 -->
<!--         \vcenter \override #'(baseline-skip . 0.85) -->
<!--         \center-column { "-1" "12"} -->
<!--     } -->
<!--   } -->

<!-- cis d dis -->
<!-- e f fis g -->
<!-- gis a ais b -->

<!--  % c' b bes a -->
<!--  % aes g ges f -->
<!--  % e es d des -->
<!-- } -->

So the ideas here really *are* familiar to musicians --- the standard notation
just makes it hard to see what it is we're talking about.

To give a bit more of a musical example, we can give a little triadic motif:

![Triadic Motif](/images/music8/out11.cropped.svg)

Notice that the third note here is one `Deg 7` above the `Note 3`, while the
fourth note is one `Deg 12` *below* the `Note 3`. In musical terms, we're
arpeggiating a triad, but inserting a diatonic note above the "third" and a
chromatic note below the "fifth" (scare quotes because the thirds and fifths
move!)

If we then repeat this motif twice more, each time one `Deg 3` up, we get this:

![Triadic Motif Sequence](/images/music8/out12.cropped.svg)


<!-- \version "2.24.0" -->

<!-- intrinsicClef = { -->
<!--   \override Staff.Clef.stencil = #ly:text-interface::print -->
<!--   \override Staff.Clef.text = \markup { -->
<!--     \vcenter \fontsize #6 \bold "3" -->
<!--   } -->
<!--   \set Staff.clefPosition = 0 -->
<!--   \set Staff.middleCPosition = 0 -->
<!-- } -->

<!-- #(define (parenthesize-naturals grob) -->
<!--    (if (equal? (ly:grob-property grob 'alteration) 0) -->
<!--        (ly:grob-set-property! grob 'parenthesized #t))) -->

<!-- #(define (edo7-accidental-stencil grob) -->
<!--    (let* ((alt (ly:grob-property grob 'alteration)) -->
<!--           (markup -->
<!--            (cond -->
<!--             ((equal? alt 1/2) #{ -->
<!--               \markup \whiteout \pad-markup #0.15 -->
<!--               \sans \bold \fontsize #-6 -->
<!--               \vcenter \override #'(baseline-skip . 0.85) -->
<!--               \center-column { "+1" "7"} -->
<!--             #}) -->
<!--             ((equal? alt -1/2) #{ -->
<!--               \markup \whiteout \pad-markup #0.15 -->
<!--               \sans \bold \fontsize #-6 -->
<!--               \vcenter \override #'(baseline-skip . 0.85) -->
<!--               \center-column { "-1" "12"} -->
<!--             #}) -->
<!--             ((equal? alt 0) #{ -->
<!--               \markup \whiteout \pad-markup #0.15 -->
<!--               \sans \bold \fontsize #-6 -->
<!--               \vcenter \override #'(baseline-skip . 0.85) -->
<!--               \center-column { "0"} -->
<!--             #}) -->
<!--             (else #f)))) -->
<!--      (if markup -->
<!--          (grob-interpret-markup grob -->
<!--            (if (ly:grob-property grob 'parenthesized #f) -->
<!--                (make-parenthesize-markup markup) -->
<!--                markup)) -->
<!--          (ly:accidental-interface::print grob)))) -->

<!-- \relative c' { -->
<!--   \intrinsicClef -->
<!--   \omit Staff.TimeSignature -->
<!-- \override Staff.Accidental.stencil = #edo7-accidental-stencil -->
<!-- \override Staff.AccidentalCautionary.stencil = #edo7-accidental-stencil -->
<!-- \accidentalStyle neo-modern-cautionary -->

<!-- c4 d dis8 ees8 e4 -->
<!-- d4 e eis8 fes8 f4 -->
<!-- e4 f fis8 ges8 g4 -->
<!-- } -->

Finally, mapping this sequence into standard notation (assuming we map via
`triad` and `diatonic`) produces this rather pleasing melody:

![Melody](/images/music8/out13.cropped.svg)

<!-- \version "2.24.0" -->

<!-- \relative c' { -->
<!--   \omit Staff.TimeSignature -->
<!-- \accidentalStyle neo-modern-cautionary -->

<!-- c4 e f8 ges8 g4 -->
<!-- e g a8 b8 c4 -->
<!-- g c d8 ees e4 -->
<!-- } -->

<audio controls>
<source src="/images/music8/melody.mp3" type="audio/mpeg">
</audio>

Notice how what was a completely regular pattern in `Note 3` expands out
unevenly each time around, producing interesting motific development.

Hopefully this gives a taste of what all that `Note` and `Ornaments` nonsense
from yesterday is all about. Not only are these ideas already familiar to
musicians, they also immediately produce musically interesting results!

