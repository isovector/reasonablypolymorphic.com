---
layout: post
title: Dragging Haskell Kicking and Screaming into the Century of the Fruitbat
date: 2021-11-12 12:15
comments: true
tags: eq, non-technical, haskell
---

Yesterday, the new Haskell CLC
[decided](https://github.com/haskell/core-libraries-committee/issues/3) to
remove `(/=)` from the `Eq` typeclass.  As expected, the community has
[embraced](https://twitter.com/Augustsson/status/1458963074556256257) this
change [with](https://twitter.com/snoyberg/status/1459118062674890752)
[characteristic](https://twitter.com/haskellhutt/status/1459147447863816200?s=20)
[grace](https://twitter.com/ChShersh/status/1458935578137931780).  The usual
state of affairs is that people who like the changes are silent, while people
who don't are exceptionally vocal. The result: people working hard to improve
things only ever get yelled at, and nobody says "hey, you're doing a great job.
Thank you!"

To the new Haskell CLC, with my deepest sincerity:

**You're doing a great job! Thank you.**

Today I'd like to talk a little about the problems I see in the Haskell
ecosystem. These are by no means insurmountable problems. They're not even
technical problems. They're *social* problems, which suck, because those are the
sort that are hard to solve.

The `(/=)` proposal has caused a surprising amount of uproar about such a stupid
change. But why? Nobody *actually* cares technically about whether we can define
not-equals instead of equals. I mean, I don't care. You don't care. I'm willing
to bet dollars to donuts that nobody reading this essay *has actually ever
defined `(/=)` in an instance.*

No, the outcry is because `(/=)` is a proxy for the real issue. As best I can
tell, there are three camps, and everyone is talking past one another. This is
my attempt to organize the camps, steel-man them (well, two out of three), and
respond with my commentary.

*Personally,* I support the removal of `(/=)` because it's a tiny, inconspicuous
change that nobody is going to notice. It's a bright beacon in the darkness of
the ecosystem saying "hey, the situation sucks, *but we're willing to improve
the situation.*" Haskell has tons of problems like this, none of which are
controversial --- things like how `head` is antithetical to everything we like
about Haskell, and yet it's included *by default* in every fucking module of all
time. Yes, there are valid arguments as to why it shouldn't be removed, but
nobody would argue to put it in if we were designing `Prelude` today.

In my eyes, removing `(/=)` from `Eq` shows that we as a community are willing
to pay the cost to move out of a bad Nash equilibrium. Because as far as I see
it, there are only two options:

1. break backwards compatibility and pay the migration costs
2. don't break backwards compatibility, and pay the costs of having a shitty
   standard library forever

Asymptotically, option 1 is better than option 2. There is a constant amount of
code today that we will need to fix, compared to a linear (or worse!) amount of
work in the future to work around having a shitty standard library. And yes,
that cost probably is forever, because if we have too much code to break today,
we're going to have even more code that will break tomorrow.

I want us to be able to remove `(/=)`, because it gives me hope that one day we
will be able to add `Foldable1`, and get `join` and `liftA2` into `Prelude`, and
the other hundreds of tiny improvements that would *all of our lives better.*
Not profoundly, but each one saves us a few seconds, multiplied by the number of
practitioners, integrated over all of our careers.

And yes, those things will come at a cost, but it's a cost that is getting
bigger the longer we don't pay it.

In the particular example of `(/=)`, there isn't even any cost. There are ~50
packages that define `(/=)`, and the solution is just to delete those
definitions. Yes, it's churn, but *I personally* am willing to send a patch to
each package. If you're the maintainer of such a package, email me and I'll just
go fix it for you.

This is not a big issue.

*The second camp* as best I can tell, are educators who aren't particularly up
to date on what Haskell *is* in 2021. These are the people saying "this will
break our tutorials" (and, I suspect, are also the ones who say "we need `head`
in `Prelude` because it's good for beginners".) While this group clearly has
good intentions, I don't think they *get it.* Educational materials for
everything go obsolete, made much worse by the [half-life of
knowledge](https://en.wikipedia.org/wiki/Half-life_of_knowledge). If this is
truly a thing you care about, *just update your tutorials.* There is no shortage
of people in the community writing explanatory material, and I guarantee they
will rush in to fill any void.

Of much more importance is *third camp.* They also seems to not care about
`(/=)` *in particular.* But they are concerned about "backwards compatibility at
all costs." And to them, it seems, `(/=)` is a slippery slope. If we can't
maintain backwards compatibility for something as stupid as `(/=)`, we've got no
chance of having long-term maintainability. It's a perfectly good argument.

To quote [Dmitrii](https://github.com/haskell/core-libraries-committee/issues/12#issuecomment-967204354):

> The size of breakage doesn't matter. Breakage is breakage.

My personal rebuttal against this attitude is that it gets us stuck in extremely
suboptimal equilibria. If we can never break anything, then every mistake must
exist *for perpetuity.* By virtue of being human, we're unfortunately fallible,
and thus are going to make mistakes.

However, I can definitely sympathize here. If every week you are called on to
fix a tiny, breaking change, sooner than later you're going to quit. We should
not encourage any behavior that leads to burnout in our best players. That's a
bad long term plan.

But in my experience, it's not breaking changes that are the problem. It's
*lots* of breaking changes that are the problem. Breaking changes are annoying,
sure, but what's worse is the *context shifting* necessary to fix a breaking
change. Doing the work is $O(n)$ with respect to the breakages, but there is an
extremely high constant factor. With this in mind, one big breakage is
significantly better than lots of tiny breakages.

Since we're just about to break things, might I again suggest we add
`Foldable1`, and clean up `Prelude`? If breakage is breakage (it is), we might
as well take advantage of it and do as much cleanup as possible. This is an
excellent opportunity. The status-quo is for all of us to argue about it every
week, with half the people saying "these are bad circumstances and we should fix
them," with the other half saying "yes, they are bad circumstances, but breakage
is worse."

But given that *we now have breakage,* let's make the most of it.

