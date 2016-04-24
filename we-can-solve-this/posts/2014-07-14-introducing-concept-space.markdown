---
layout: post
title: Introduction to Concept Space
date: 2014-07-14 20:17
comments: true
tags: science, philosophy
---

## Maps and Metaphors

I'm currently reading a book called [Metaphors we Live By][mwlb] by Lakoff and
Johnson, and it's probably one of my favorite things I've read
[all year][books]. I've been working through it for a few weeks now, and while
it's not a hard book, I find myself needing to go *really slowly*, namely
because it has a super-high insight-density and I need to keep stopping and
*actually thinking about the things it says*. Seriously, this book has literally
changed the (figurative) way I see the world, and if you're looking for such
a book, I would *highly* recommend it.

While the authors don't necessarily come out and say it in so many words, one of
the book's concepts is an axiomatic yet reducible set of theorems as the basis
of human understanding. The theorems are axiomatic in the sense that they can be
used to derive all other concepts -- that every possible idea we can think of is
(arguably) made up of some combination of these -- but reducible in the sense
that we can perform introspection on them and break them down.

"Well," you might be starting to ask, "aren't the things they decompose to then
the axioms, not this set?" And indeed, you would be correct on that front in
most cases, except here, because the ideas they reduce to are other ideas in the
set of axioms.

<!--more-->

If this seems counterintuitive to you, think about it like this: each of the
axioms is defined in terms of the other axioms. The notion will probably make
more sense if we stop thinking of the axioms as theorem-components and instead
as the basis of a vector space. If you've forgotten, a vector space (very
loosely) generalizes coordinates.

As a quick example, imagine a map of the world. It's obvious that we have only
two dimensions on this map -- the X and the Y coordinates. Furthermore, we also
have the notion of distance between any two places on the map. If you're not
a mathematician, this is (hopefully) a good enough approximation of
a [vector space][vspace] to follow along with the remainder of my argument. That
being said, remember that vector spaces can have *as many dimensions as they
want*.  Our map has 2, but we will shortly see an example of a 7-dimensional
space, and we could have infinite dimensions if we really wanted.

Keeping our map example in mind, a basis is any convention for measuring
locations in the space. By historical convention, we generally use a basis of
**[latitude, longitude]** for expressing locations on the planet, which roughly
corresponds to **[North, West]**. We use North and West (or South and/or East),
because they are vectors (mathematical objects with the notion of a direction)
which happen to be orthogonal -- which is to say, point in directions that are
90 degrees away from one another. It is *completely impossible* to point North
if you are only able to point East or West.

However, **[N, W]** is not the only basis we can choose for our map. You can
come up with some trivial other bases to choose from, but one you almost
certainly didn't think of is the basis **[NE, NEN]** -- northeast and
northeast-north. It's not as easy as using **[N, W]**, since moving in the
**NE** direction also moves you in the **NEN** direction, but if you try, you
actually can describe any location with a unique set of coordinates. On a map,
you can pick any two separate cardinal directions to form a basis, so long as
they don't point in *completley opposite* directions.

This idea indeed generalizes to vector spaces at large, with a few small
changes: in order to describe an N-dimensional vector space, we are going to
need a basis with N different vectors, and none of those vectors must be
entirely constructable as a combination of any of the others.

The intuition here is that for any vector space, our choice of basis is
arbitrary, and serves to describe any location in the entire space. If you get
to choose, pick an orthogonal basis (where *every* vector in the basis is
orthogonal to *every other* vector in the basis), because it makes your life
easier, though this isn't strictly necessary to actually do anything cool.

All of a sudden, the notion that concept-space be made up of reducible axioms
need not seem so strange anymore. If we look at concept-space as a vector space,
all we are expressing is that it have a basis which is non-unique.

[mwlb]: http://theliterarylink.com/metaphors.html
[books]: https://www.goodreads.com/user_challenges/1183394
[vspace]: http://en.wikipedia.org/wiki/Vector_space#Examples



## Metric-Space is a Metric Space

To better hammer-in what concept-space might look like, let's take a simpler toy
example to knock out some of the more subtle details.

If you are not American, you will be very familiar with the metric system. If
you *are* American, you should consider switching, because your system is
stupid.

At its core, the metric system is composed of seven fundamental units: mass
(*kg*), time (*s*), distance (*m*), count (*mol*), electrical current (*A*),
temperature (*K*) and luminance (*cd*). At first glance, this seems incapable of
expressing most of the things we want to measure, like speed, volume (the liquid
sense), or power.

However, as physicists or otherwise Johnny-on-the-spot readers might see, all
physical measurements turn out to be combinations of the seven listed
previously. Speed is just $m\cdot s^{-1}$, volume $m^3$, and power $kg\cdot m^2
\cdot s^{-3}$.

It is evident, then, that the seven base metric units form a basis for the
metric system. We can describe any physical measurement as a 7-tuple of **[kg,
s, m, mol, A, K, cd]**, analogously to how we could describe any location on
a map of the world as a 2-tuple of **[N, W]**. Furthermore, to expand our
metaphor, we can look at metric-space itself as a map of the measurements, where
each individual unit has a definite location in metric-space, just like every
city has a definite location on Earth.

Also it is important to note that choice of basis for the metric system (the
seven base units) be just one of an infinite number of possible bases. Just like
we could describe the map's coordinates with the **[NE, NEN]** basis, we can
construct a basis for the metric system by using seven derived units of
measurement -- so long as no two are the same and none can be made up by the
other six. It is left as an exercise to the reader to find a basis for the
metric system that satisfies these constraints.


## Word-Space: Not Just a Space of Words

Despite being a software engineer by trade, I'm always amazed by the
*incredible* things people seem to be able to coerce computers to do. There's
a program called [word2vec][w2v] that has recently blown my mind more than most.

word2vec does this: given a large-enough corpus of text, builds
a vector space[^1] that encodes the relationships between words. From the
manual:

> It was recently shown that the word vectors capture many linguistic
> regularities, for example vector operations vector('Paris') - vector('France')
> + vector('Italy') results in a vector that is very close to vector('Rome'),
> and vector('king') - vector('man') + vector('woman') is close to
> vector('queen')

In other words, this software mathemagically can determine that removing the
idea of [man*]* (square-bracket notion explained [here][first20]) from [king]
leaves some sort of abstract notion of [royalty], such that we can add it to
[woman] and get [queen].

Also in the manual but not mentioned in the above excerpt is that taking the
vector closest to [river] + [China] results in [Yangtze].

Computers did that, with absolutely no philosophical "understanding" of the text
being analyzed. Frickin' computers! Please take a second to update on this
information and move your priors a little closer towards [there is nothing
magical about human intelligence]. This is kind of the exact reason why I'm in
this field.

An important point here is that -- as far as I can tell -- the underlying
vectors here (which is to say, the actual coordinates in word-space) have no
real meaning. However, once you slap some semantic labels on the vectors you
care about, the semantic relationships we seem to care about are preserved
through manipulation of the vectors. The coordinates are nothing but the
mathematical artifacts responsible for making this work "behind the scenes".
However, I will leave the (inevitable) philosophical debate about the "meaning
of these coordinates" to the [philosophers][philohate]. To me, the coordinates
are just linear combinations of eigenvectors. But I digress.

A subtle point is that when discussing the [Yangtze], we talked about "the
closest vector". It is a fundamental property of vector spaces (and more
generally, [metric spaces][mspace] (not to be confused with metric-space: the
vector space of the metric system)) that, just like cities on a map, vectors
with similar coordinates are close to one another in space. The reason I bring
this up is to assuage your fears that perhaps it isn't meaningful to discuss the
concept of "distance" when talking about highly abstract ideas. Good news: if
you can prove you're talking about a vector space, it is!

In practice, what this means is that the ideas [man], [king], [lion] and even
[Budweiser] are all spatially-located pretty closely to one another in
concept-space, though likely in different dimensions. Just like how the
longitude and latitude of any two points on a mountain are likely to be pretty
similar, they can have wildly varying altitudes, [man] and [king] are separated
only by the notion of [royalty], while [king] and [lion] might be separated only
by the concept [feline]. Ideas which are located closely with one another, in
aggregate form what is known as a cluster -- clusters in concept-space are
groups of similar ideas.

[w2v]: http://code.google.com/p/word2vec/
[first20]: /blog/first-20-recursive-bees
[philohate]: /blog/ethics-crasher
[mspace]: http://en.wikipedia.org/wiki/Metric_space

[^1]: Well, not really, but for our purposes let's just pretend.



## The Concept of Concept-Space

> Warning: abandon all hope of mathematical rigor, ye who enter here.

While thinking about the word-space as created by word2vec is cool and all, it
seems to me like we should be able to do better. Word-space is descriptive --
which is to say it is generated BY the ideas we currently have -- rather than
prescriptive, which would ideally allow us to postulate entirely *new* concepts
by just adding constituent vectors together.

The remainder of this essay should explicitly be classified with an epistemic
status of "almost certainly false, but potentially a useful tool for modeling
regardless". [Proceed at your own risk][fail2update].


### Definitions

Assume there exists a meaningful concept-space -- a vector space of every
thought possibly thought. This implies every thought has some definite
coordinate representation in concept-space, even if we're unsure about what the
coordinates actually mean (as in the case of word-space). For simplicity, we
shall call points in concept-space **thoughts**. Furthermore, we assume it be
meaningful to combine thoughts with one another (that a combination of two
thoughts results in another point in concept-space).

With the assumption that concept-space have finite degree (though the argument
doesn't depend on this assumption, it makes our terminology
relatively-consistent with existing literature), let any basis of concept-space
be called a **prior**, in adherence with [the Bayesians][bayes].

Let's say that at any given moment, you are able to recall some set of ideas
you're previously thought. For the most part, arguably this set of ideas
uniquely defines your personality. This encompasses the topics you like talking
about, the explicit [affordances][affords] you have to external stimulus, and
the thought patterns your mind takes when tackling new problems. For lack of
a better term, I will call this your thought $bucket$.

By an argument of [diagonalization][cantor], you should be able to combine two
of the thoughts in your $bucket$ to create a new thought, one which is not
currently in your $bucket$ (though this argument doesn't hold if one of the
thoughts be the additive identity). This process allows us to come up with
thoughts previously un-thought, arguably the processes of creativity and
problem-solving. Being able to generate new ideas does not necessarily imply
that you can generate *good* ideas, however.


### An Insight into Insights

Almost by definition, then, the majority of the thoughts in your $bucket$ will
cluster with one another, since they have been composed of one another. We can
thus define an **insight** (in the usual sense of the word) as a thought with
a large distance between itself and the weighted center of the $bucket$
cluster. Suddenly, our model gains predictive power, in that one insight begets
another: adding this new insight to any other thought in the $bucket$ will
likely lead to *another* insight. Indeed, it is generally considered the case
that insights lead to more insights<sup>[citation needed]</sup>.


### Exploration of Concept-Space

Let us call this  act of trying to find specific thoughts the **exploration** of
concept-space. Since our model describes exploration as the linear combination
(and insertion henceforth) of thoughts from (to) the $bucket$, this process is
necessarily serial. Let us then define the **difficulty** of an arbitrary
thought $T$ to be the fewest number of combinations of thoughts from the
$bucket$ necessary to compose thought $T$. (Mathematically speaking, this
difficulty is defined as the minimal sum of the norms of the coefficients of $T$
when expressed in the basis defined by $bucket$.)

Clearly our choice of prior for concept-space will determine the difficulty of
any given thought. If looking for a particular thought, the best case is that
you already know it; the second best case is if it's close to something you
already know; the third best case being if you have lots of thoughts completely
unrelated to one another, allowing you to quickly explore areas of concept-space
you've never been to before.

Intuitively, the fact that difficulty is a function of prior describes why some
people are better at certain types of mental tasks than others, and why
brainstorming works better in a group (the group can combine their individual
$bucket$s, and thus search arbitrary sections of concept-space more
efficiently).


### The Effects of Priors on Exploration

The takeaway here is that not all priors (read: ways of thinking) are created
equally. Different priors are more effective for exploring different regions of
concept-space, analogously to how some vehicles are better suited to getting to
some places.

Assuming complete indifference of concept-space, the best
(difficulty-minimizing) prior is orthogonal: each thought vector points in
a completely different direction than every other thought (recall that North and
East and Up are all orthogonal on a map). If you want to be able to get to
anywhere in concept-space least-difficultly, it is best that your prior express
*no bias whatsoever*. An indifference prior manages an average-level
difficultly for all thoughts at the expense of a complete inability to find
*any* thought efficiently.

However, just like priors aren't created equally, neither are thoughts. Some
thoughts (eg. [evolution by natural selection]) are simply [more useful][evo]
than others. An indifference prior is, by nature, unable to express such
preferences. Clearly we can do better than an indifference prior.

The ideal prior for exploring useful regions of concept-space we shall call the
**eigenprior**, and while it is outside the scope of this paper to find such
a prior, the general strategy is [principle component analysis][pca] (for an
*awesome* example, [this][eigenfaces] article shows how to apply the procedure
for facial recognition -- pictures included!).

It is an open question whether or not the eigenprior is effectively installable
onto human-mindware (let alone if this question is even *meaningful*).

[fail2update]: http://sitemaker.umich.edu/norbert.schwarz/files/lewandowsky_et_al_misinformation_pspi_ip.pdf
[affords]: /blog/affording-ascendancy
[cantor]: https://www.youtube.com/watch?v=elvOZm0d4H0
[bayes]: http://lesswrong.com
[evo]: http://en.wikipedia.org/wiki/Applications_of_evolution
[pca]: http://en.wikipedia.org/wiki/Principal_components_analysis
[eigenfaces]: http://jeremykun.com/2011/07/27/eigenfaces/



## Conclusion

I've got a lot more to write on the topic of concept-space, but this post is
already heavily tangential and long-winded, so I'll save it for another time.

In short, however, the key takeaways from this post I plan to extend on are:

* concept-space is a vector space, and as such, all of linear algebra applies in
  its analysis.
* it is meaningful to discuss the distance between thoughts.
* any arbitrary thought has an associated difficulty of being found, defined by
  characteristics of the mind-doing-the-exploration.
* as such, some means of thinking about the world are simply *more useful* than
  others, and it is thus worthwhile to spend some time trying to optimize this
  process.

In addition, if we're going to continue thinking about this, it's going to need
a snazzy name. I kind of like "Concept Theory" for its high-degree of
[general abstract nonsense][ct], but I'm certain that the internet can do
better.

*Prima facie*, this seems like a highly-worthwhile field of investigation --
I'd love to hear all of your thoughts.

[ct]: http://en.wikipedia.org/wiki/Abstract_nonsense

