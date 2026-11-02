---
layout: post
title: An Overview of an Ambitious Music Project
date: 2026-11-02 15:23
comments: true
tags: music, music theory
---

It's November. And you know what that means. [National Novel Writing
Month][nanowrimo]. Rather than writing a novel, I thought it'd be fun to do
something like in 2016 when I wrote [my first textbook][httw]. But this time
around, I'm going to bash out all of the ideas about a constructive theory of
music that have been banging around in my head for a few years.

[nanowrimo]: https://nano2.org/
[httw]: https://reasonablypolymorphic.com/book/preface

Many years ago, I read [Composing Contracts: an adventure in financial
engineering][contracts], in which Haskell King Simon Peyton Jones descends
unwittingly into the world of financial instruments. And being a "red-blooded
functional programmer," he designs a bunch of combinators which model the
entire complexity of dozens of financial instruments, as well as an infinitely
many that nobody had ever thought to ask for.

[contracts]: https://www.microsoft.com/en-us/research/publication/composing-contracts-an-adventure-in-financial-engineering/

This paper has always been wildly inspirational to me, and alongside [Compiling
to Categories][concat], is the clearest example of the power of pure,
strongly-typed, functional programming, and its ability to model the wider,
messier world.

[concat]: https://conal.net/papers/compiling-to-categories/compiling-to-categories.pdf

So, wanting to learn how to flex these muscles for myself, I set off many years
ago on a quest to try to tackle the hardest problem I could think of, that I
felt like I had any chance whatsoever of succeeding at --- music. After all,
["so much of life's failure consists in holding yourself to too low a
standard."][lw]

[lw]: https://www.lesswrong.com/posts/WLJwTJ7uGPA5Qphbp/trying-to-try

The goal is, and has always been, to develop something equivalent to [Brent
Yorgey's][byorgey] amazing [diagrams][diagrams] library. Diagrams is a
combinator library in Haskell which abstracts away the "how" of drawing a
picture from the "what picture do you want to draw?" For example, here's how you
draw a [Sierpinski triangle](triangle):

[byorgey]: https://byorgey.github.io/blog/
[diagrams]: https://diagrams.github.io/gallery.html
[triangle]: https://en.wikipedia.org/wiki/Sierpi%C5%84ski_triangle

```haskell
sierpinski 1 = triangle 1
sierpinski n =     s
                 ===
              (s ||| s) # centerX
  where s = sierpinski (n-1)
```

which you might notice *is exactly the obvious definition of what a Sierpinski
triangle is* --- recursive copies of itself arranged in a triangle.

So the question I've been chasing for years is "what is an equivalently elegant
approach to composing music?" I spent a [good][music1] [chunk][music2] of my
holiday season last year struggling to find a good starting point here. With the
benefit of hindsight, and of being a year older and wiser, I've made a great
deal of progress since then.

[music1]: /blog/algebraic-music/
[music2]: /more-algebraic-music/

But before diving into exactly what that progress means, I think it's worth
discussing what explicitly the goals here are (and what they are *not.*) Some
desiderata:

1. The system must be capable of expressing any music, from any culture, from
   any time (this includes *music and styles that do not yet exist.*)
2. It must be easy to get good results out of the system.
3. Understanding the system should teach you something about music.

These three desiderata are an extreme set of constraints on the solution space.
Desideratum 1 means that we can't take *anything* for granted. For example, we
cannot assume that there are 12 pitch classes, since this would immediately
eliminate microtonal music. Nor can we privilege [harmonic function][function],
since this isn't an idea that seems to be shared by non-Western traditional
music.

[function]: https://en.wikipedia.org/wiki/Function_(music)

Desideratum 2 means that we can't be happy with only a mathematical model. Yes,
to a first approximation, set theory can describe anything, but lots of things
are pretty egregious to articulate in set theory! This gives rise to the need
for *musically-meaningful combinators.* I think the [kaleidoscope diagram] is a
striking visual example of this idea. It's a piece of code that *given any image
whatsoever* can produce a new image *which is a kaleidoscope of that thing.*
With a little hand waving here, you can imagine a set of musical combinators
which approach a given motif, which ramp up the tension, which introduce
syncopation, which produce senses of resolution. This also means we must put a
great deal of thought into how musical ideas are represented, and how they can
be combined.

[kaleidoscope]: https://diagrams.github.io/gallery/Kaleidoscope.html

Desideratum 3 means we can't just hand the problem off to some LLM or some other
probabilistic mechanism.

Under these constraints, it's immediately evident that almost no existing music
theory is up to the task. As best I can tell, the field of music theory is
primarily focused on *analysis of existing music* rather than on *general
techniques for creating new music.* Perhaps an argument can be made that you
must be able to spot greatness in order to produce it for yourself, but this is
relatively unconvincing to me. Attempting to perform post-hoc analysis of music
without a constructive theory seems analogous to decompiling computer code
*without a language to decompile it into.* At best you might find some
statistical patterns (V chords often go to I), but this doesn't seem like it
ought to lend itself much to *actually writing good music.* Will it out-compete
a [Markov chain][markov] trained on the same probabilities?

[markov]: https://en.wikipedia.org/wiki/Markov_chain

The best we can do with most existing music theory is (to the extent that it is
constructive [which is extremely few and far between]) relegate it to combinator
status. A grammar of functional harmony can exist as a DSL on top of the core
music structures. [Voice leading spaces][tonality] ala [Tymoczko][tymoczko][^1]
can be expressed by their own notions of pitch, alongside operations and
elimination forms.

[tonality]: https://dmitri.mycpanel.princeton.edu/tonality-an-owners-manual.html
[tymoczko]: https://dmitri.mycpanel.princeton.edu/index.html

[^1]: Dmitri Tymoczko has the distinction of being the only music theorist I've
      found who is precise enough to be more than [not even wrong][wrong].
      Rather amazingly, he also seems to be *right!* Coincidence?

[wrong]: https://en.wikipedia.org/wiki/Not_even_wrong

So that's the overview. All in all, it's a very ambitious project. I am not
interested in hearing from you if you think this cannot be done. If you're
right, I'll end up with egg on my face, but that's my problem. However, if this
is the sort of thing that piques your interest as much as it has mine, please do
get in touch.

In the next post we'll discuss the denotative elements of music.

