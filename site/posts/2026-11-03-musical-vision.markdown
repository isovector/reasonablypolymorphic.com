---
layout: post
title: What Composing Music Could Look Like
date: 2026-11-03 15:30
comments: true
tags: music, vision
---

In the last post, we discussed the [algebraic structure of horizontal
structures][last]. But I realized I haven't actually communicated the argument
behind *why we might care* about that algebraic structure. So rather than diving
directly into the technical stuff I had planned for today, let's hash that out
first.

[last]: /blog/music-signals/

If you recall, where we ended up was an abstract type `Signal a` which I claim
is a precursor to horizontal musical structures, with the following common
algebras:

```haskell
type Signal a
instance Functor Signal
instance Applicative Signal
instance Foldable Signal
instance Semigroup a => Semigroup (Signal a)
instance Semigroup a => Monoid (Signal a)
```

It's worth considering what each of these ideas means, musically. And once we've
sorted that out, it's worth thinking about what other musical structure we might
want on top.

We can think about a `Signal a` as being a continuous function of `a`s over
time, combined with a set of times that we're *actually interested in.* So what
exactly does that mean? The continuous function part is just there to fill in
the details when we change our minds about what times we want to look at.

With our `Functor` instance, we can do per-note (or per-whatever is held in the
horizontal structure) transformations. For example, `fmap (+ 1)` transforms

![C-D-E-F](/images/music1/out1.cropped.png)

into

![D-E-F-G](/images/music1/out2.cropped.png)

But it also does more interesting things; `fmap (!! 1)` (where `!! n` selects
voice `n`) transforms

![Inversions of C](/images/music1/out3.cropped.png)

into

![E-G-C-E](/images/music1/out4.cropped.png)

Furthermore, nobody says the `a` in `Signal a` need be something that is
musically meaningful. A `Signal` is just a function from time to something; so
we could do something crazy like building a `Signal DayName` that is a week-long
signal moving from `Monday` to `Sunday` at a rate of one a day. We could then
use the `Functor` instance to transform these labels into something more
musically meaningful --- perhaps into motifs or numbers of repeats, or something
like that.

Our `Semigroup` instance gives us a `<>` operation, which combines things that
happen at the same time. What it means to "combine things" depends on the
things being combined. But as a little vibe check, we can use `<>` to smush
together two little motifs:

![C-x-E-x](/images/music1/out5.cropped.png)

![C-F-G-x](/images/music1/out6.cropped.png)

into

![C-F-EG-x](/images/music1/out7.cropped.png)

This example one is very vibes, so don't read TOO much into it. The important
part is that "things that happen at the same time get smushed together." We'll
discuss in MUCH MORE DETAIL sometime in the future what sorts of smushing might
be musically meaningful.

The `Applicative` structure is very similar to the `Semigroup`, except that
instead of smushing things together, we can run a function that depends on the
values in both things. This one is unfortunately impossible to show in standard
musical notation, and wiring up some custom visualization isn't a good use of my
nanowrimo time.

But let's use our IMAGINATION instead. Imagine a voice-leading that looks like
this (realized over a C-major triad):

![Abstract voice leading](/images/music1/out8.cropped.png)

We can use our applicative instance to retarget the voice leading over any other
chord. For example, given this one:

![C-D-B](/images/music1/out9.cropped.png)

Invoking `liftA2 applyVoiceLeading` over these two musical pieces gives us this
remarkable chord progression:

![Something odd](/images/music1/out10.cropped.png)

If you're familiar with lots of harmony, you can see that both progressions are
structurally equivalent --- a [neo-Riemannian P transform][riemannian], followed
by an efficient voice leading from CM to E#M, followed by the outer two voices
switching pitch classes by moving in opposite directions.[^tonality]

[riemannian]: https://en.wikipedia.org/wiki/Neo-Riemannian_theory#Triadic_transformations_and_voice_leading

[^tonality]: I extracted all the moves here from Tymoczko's masterpiece [Tonality: An Owner's Manual][tonality].

[tonality]: https://dmitri.mycpanel.princeton.edu/tonality-an-owners-manual.html

Of course, nothing requires us to use the _same_ chord throughout. We can apply
our same voice leading pattern to a series of changing chords, for example:

![Changing chords](/images/music1/out11.cropped.png)

which results in

![Voice leading over changing chords](/images/music1/out12.cropped.png)

You'll notice we're getting *very interesting* results without doing much work
at all. I picked some random voice leadings and some random chords, and the
computer did all of the work of figuring out what notes I'm gesturing at.

Some other things you could do with this: instead of voice leadings, put scalar
modulations. Or note durations! Or put voice numberings and project chords down
to individual voices (which is different than the functor case, because here we
can _change_ which voice gets to sound.) Better yet, do all of the above,
continuously, at different time scales.

What I think this ends up looking like in practice is something akin to a
modular synthesizer. You can plug the outputs of different signals into the
inputs of others. But unlike any modular synthesizer you've ever played with,
here our signals are allowed to carry macroharmonies, voice leadings,
modulations, tension, motifs, rhythm, registral expansion, dynamics, timbre, or
even just arbitrary mathematical functions.

That's probably enough for now. In the next post we'll actually get around to
looking at the implementation of `Signal` and then giving better composable
semantics around it.

