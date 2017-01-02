---
layout: post
title: Comonadic Collision Resolution
date: 2017-01-01 16:18
comments: true
tags: haskell, comonads, physics, game
---

I have a sinful, guilty pleasure -- I like a sports video-game: [NBA Jam
Tournament Edition][jam]. Regrettably, I don't own a copy, and all of my
attempts to acquire one have ended in remarkable misfortune.

Obviously my only recourse was to make a tribute game that I could play to my
heart's desire.

And so that's what I set out to do, back in 2013. My jam-loving then-coworker
and I drafted up the barest constituent of a design document, and with little
more thought about the whole thing we dove right in.

We "decided" on Python as our language of choice, and off we went. There was no
game engine, so we rolled everything by hand: drawing, collision, you name it.
We got a little demo together, and while it was definitely basketball-like, it
certainly wasn't a game. Eventually my partner lost interest, and the code sits
mostly forgotten in the [back recesses of my Github repositories][jam-time].

I say mostly forgotten because over the last three years, I've occasionally
spent a sleepless night here or there working on it, slowly but surely turning
midnight fuel into reality.

Three years is a long time to spend on a toy project, and it's an even longer
amount of time for a junior engineer's sensibilities to stay constant. As I
learned more and more computer science tools, I found myself waging a constant
battle against Python. The details aren't important, but it was consistently a
headache in order to get the language to allow me to express the things I wanted
to. It got to the point where I stopped work entirely on the project due to it
no longer being fun.

But this basketball video-game of mine was too important to fail, and so I came
up with a solution.

If you're reading this blog, you probably already know what the solution to my
problem was -- I decided to port the game over to Haskell. Remarkable progress
was made: within a few days I had the vast majority of it ported. At first my
process looked a lot like this:

1) Read a few lines of Python.
2) Try to understand what they were doing.
3) Copy them line-by-line into Haskell syntax.

and this worked well enough. If there were obvious improvements that could be
made, I would do them, but for the most part, it was blind and mechanical. At
time of writing I have a bunch of magical constants in my codebase that I dare
not change.

However, when I got to the collision resolution code, I couldn't in good
conscience port the code. It was egregious, and would have been an abomination
upon all that is good and holy if that imperative mess made it into my glorious
new Haskell project.

The old algorithm was like so:

1) Attempt to move the capsule[^capsule] to the desired location.
2) If it doesn't intersect with any other capsules, 👍.
3) Otherwise, perform a sweep from the capsule's original location to the
   desired location, and stop at the point just before it would intersect.
4) Consider the remaining distance a "force" vector attempting to push the other
   capsule out of the way.
5) Weight this force by the mass of the moving capsule relative to the total
   weight of the capsules being resolved.
6) Finish moving the capsule by its share of weighted force vector.
7) Recursively move all capsules it intersects with outwards by their shares of
   the remaining force.

[^capsule]: Lots of physics engines model complicated things as pill-shaped capsules, since these are mathematically simple and usually "good enough".

I mean, it's not the greatest algorithm, but it was fast, simple, and behaved
well-enough that I wasn't going to complain.

Something you will notice, however, is that this is definitively *not* a
functional algorithm. It's got some inherent state in the position of the
capsules, but also involves directly moving other capsules out of your way.

Perhaps more worryingly is that in aggregate, the result of this algorithm isn't
necessarily deterministic -- depending on the order in which the capsules are
iterated we may or may not get different results. It's not an apocalyptic bug,
but you have to admit that it is semantically annoying.

I spent about a week mulling over how to do a better (and more functional) job
of resolving these physics capsules. The key insight was that at the end of the
day, the new positions of all the capsules depend on the new (and old) positions
of all of the other capsules.

When phrased like that, it sounds a lot like we're looking for a comonad,
doesn't it? I felt it in my bones, but I didn't have enough comonadic kung-fu to
figure out what this comonad must actually look like. I was stumped -- nothing I
tried would simultaneously solve my problem and satisfy the comonadic laws.

Big shout-outs to [R&uacute;nar Bjarnason][runar] for steering me into the right
direction: what I was looking for was not in fact a comonad (a data-type with a
`Comonad` instance), but instead a *specific* Cokleisli arrow (a function of
type `Comonad w => w a -> b`).

Comonadic co-actions such as these can be thought of the process of answering
some query `b` about an `a` in some context `w`. And so, in my case, I was
looking for the function `w Capsule -> Capsule`, with some `w` suitable to the
cause. The `w Capsule` obviously needed the semantics of "be capable of storing
all of the relevant `Capsule`s." Implicitly in these semantics are that `w` need
also have a *specific* `Capsule` under focus[^laws].

[^laws]: Otherwise we'd be pretty hard-pressed to find a useful `extract :: w a -> a` function for it.

To relieve the unbearable tension you're experience about what comonad `w` is,
it's a `Store`. If you're unfamiliar with `Store`:

```haskell
data Store s a = Store s (s -> a)
```

which I kind of think of as a warehouse full of `a`s, ordered by `s`es, with a
forklift that drives around but is currently ready to get a particular `a` off
the shelves.

With all of this machinery in place, we're ready to implement the Cokleisli
arrow, `stepCapsule`, for resolving physics collisions. The algorithm looks like
this:

1) For each other object `:: s`, extract its capsule from the `Store`.
2) Filter out any which are not intersecting with the current capsule.
3) Model these intersecting capsules as a spring-mass system, and have each
   other object exert a displacement "force" exactly necessary to make the two
   objects no longer collide (weighted by their relative masses).
4) Sum these displacement vectors, and add it to the current capsule's position.

This algorithm is easy to think about: all it does is compute the new location
of a particular capsule. Notice that it explicitly *doesn't* attempt to push
other capsules out of its way.

And here's where the magic comes in. We can use the comonadic co-bind operator
`extend :: (w a -> b) -> w a -> w b` to lift our "local"-acting function
`stepCapsule` over all the capsules simultaneously.

There's only one problem left. While `extend stepCapsule` ensures that if any
capsules were previously colliding no longer do, it doesn't enforce that the
newly moved capsules don't collide with something new!

Observe of the algorithm that if no objects are colliding, no objects will be
moved after running `extend stepCapsule` over them. And this is in fact just the
trick we need! If we can find a fix point of resolving the capsules, that fix
point must have the no-collisions invariant we want.

However, notice that this is not the usual least-fixed point we're used to
dealing with in Haskell (`fix`). What we are looking for is an iterated fixed
point:

```haskell
iterFix :: Eq a => (a -> a) -> a -> a
iterFix f = head . filter (==) . ap zip tail . iterate f
```

And voila, `iterFix (unpack . extend stepCapsule . pack)` is our final,
functional solution to resolving collisions. It's surprisingly elegant,
especially when compared to [my original imperative solution][original]. For
bonus points, it feels *a lot* like the way I understand actual real-life
physics to work: somehow running a local computation everywhere, simultaneously.

While time forms a monad, physics forms a comonad. At least in this context.

[jam]: https://en.wikipedia.org/wiki/NBA_Jam
[jam-time]: https://github.com/isovector/jam-time
[original]: https://github.com/isovector/jam-time/blob/master/jam/game/CapsuleManager.py#L18-L56
[runar]: http://blog.higher-order.com/

