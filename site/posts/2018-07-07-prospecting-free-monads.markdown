---
layout: post
title: Static Analysis of Free Monads
date: 2018-07-07 15:45
comments: true
tags: free, monad, library, announcement, prospect
---

## Motivation

A [common][harmful] [misperception][dsl] of free monads is that they allow for
analysis of an program expressed with them. This is not true, and in fact,
monads are [too liberal][liberties] of an abstraction to allow for inspection in
general.

[harmful]: https://markkarpov.com/post/free-monad-considered-harmful.html
[dsl]: /blog/free-stories/
[liberties]: https://www.youtube.com/watch?v=GqmsQeSzMdw

In order to see why, consider the following monadic expression:

```haskell
      getLine
  >>= \str -> if str == "backdoor"
                 then launchNukes
                 else pure ()
```

The problem here is that bind is expressed via a continuation, and we're unable
to look inside that continuation without calling the function. So we're stuck.
We can't determine if the above program will ever call `launchNukes` unless we
just happen to call the lambda with the exact string `"backdoor"`.

So, in general, we're unable to statically inspect monads. We can *run* them
(not necessarily in the `IO` monad) and see what happens, but getting a free
monad to help with this is equivalent to mocking the exact problem domain. But,
even though we can't do it in general, it seems like we should be able to do it
in certain cases. Consider the following monadic expression:

```haskell
            getLine
  >>= \_ -> launchNukes
```

In this case, the computation doesn't actually care about the result of
`getLine`, so in theory we can just call the continuation with `undefined` and
find that yes indeed this expression will call `launchNukes`.

Notice that we *can't* use this strategy in the first expression we looked at,
because that one scrutinized the result of `getLine`, and branched depending on
it. If we tried passing `undefined` to it, it would crash with an error when we
tried to force the final value of the monad (although this might be preferable
to actually launching nukes.)

This example of `launchNukes` is admittedly rather silly. My original motivation
for investigating this is in the context of [ecstasy][ecstasy] in which users
can query and manipulate disparate pieces of data. For example, if we wanted to
write a physics simulator where each object may or may not have any of a
`position :: V2 Double`, a `velocity :: V2 Double` and a `hasPhysics
:: Bool`, we could write the following piece of code to update the positions of
any entities that have a velocity and are, in fact, affected by physics:

[ecstasy]: https://github.com/isovector/ecstasy

```haskell
emap $ do
  p <- query position
  v <- query velocity
  h <- query hasPhysics

  guard h

  pure unchanged
    { position = Set $ p + v ^* timeDelta
    }
```

Because objects are not required to have all of the possible data, mapping this
function will intentionally fail for any of the following reasons:

* the object did not have a `position` field
* the object did not have a `velocity` field
* the object did not have a `hasPhysics` field
* the object had a `hasPhysics` field whose value was `False`

Without being able to statically analyze this monadic code, our only recourse is
to attempt to run it over every object in the universe, and be happy when we
succeed. While such an approach works, it's terribly inefficient if the universe
is large but any of the `position`, `velocity` or `hasPhysics` fields is sparse.

What would be significantly more efficient for large worlds with sparse data
would be to compute the intersection of objects who have all three of
`position`, `velocity` and `hasPhysics`, and then run the computation only over
those objects. Free applicatives (which *are* amenable to static analysis) are
no good here, since our `guard h` line really-and-truly is necessarily monadic.

Any such static analysis of this monad would be purely an optimization, which
suggests we don't need it to be *perfect;* all that we are asking for is for it
to be better than nothing. A best-effort approach in the spirit of our earlier
"just pass `undefined` around and hope it doesn't crash" would be sufficient. If
we can be convinced it won't actually crash.

What we'd *really* like to be able to do is count every occurrence of `query` in
this monad before it branches based on the result of an earlier `query`. Which
is to say we'd like to pass `undefined` around, do as much static analysis as we
can, and then somehow `fail` our analysis *just before* Haskell would crash due
to evaluating an `undefined`.


## Prospecting Monads

I've been playing around with this conceptual approach for some time, but could
never seem to get it to work. Laziness can sure be one hell of a bastard when
you're trying to pervert Haskell's execution order.

However, last week Foner et al. dropped a bomb of a paper [Keep Your Laziness
in Check][strict], which describes a novel approach for observing evaluations of
thunks in Haskell. The gist of the technique is to use `unsafePerformIO` to
build an `IORef`, and then set its value at the same time you force the thunk.
If you (unsafely) read from the `IORef` and see that it hasn't been set, then
nobody has forced your value yet.

[strict]: http://very.science/pdf/StrictCheck.pdf

We can use a similar approach to accomplish our optimization goals. For the crux
of the approach, consider the follow `verify` function that will evaluate a
pure thunk and return `empty` if it instead found a bottom:

```haskell
verify :: Alternative f => a -> f b
verify f a = unsafePerformIO $ do
  catch
    (let !_ = a
      in pure $ pure a)
    (\(_ :: SomeException) -> pure empty)
```

The bang pattern `!_ = a` tells Haskell to `seq` `a`, which reduces it to WHNF,
which, if its WHNF is bottom, will be caught inside of the `catch`.
`unsafePerformIO` is necessary here, because exceptions can only be caught in
`IO`.

Using this approach, if we're very careful, we can tear down a free monad by
following its continuations using bottom, and doing the `verify` trick to stop
exactly when we need to.

I call such a thing `prospect`, and you can find it [on
github][prospect]. The name comes from the fact that this can lead to gold, but
carries with it the intrinsic dangers of plumbing into the depths, such as
cave-ins, blackened lungs, or the worse things that dwell in the darkness.

[prospect]: https://github.com/isovector/prospect

The primary export of `prospect` is the titular function `prospect :: Free f a
-> (Maybe a, [f ()])`, which tears down a free monad, tells you whether or not
it has a pure return value, and spits out as many `f` constructors as it could
before the computation branched. If you got a `Just` back, it means it found
every constructor, but there are no other guarantees.

[Happy prospecting!][prospect]

---

Huge shoutouts to Vikrem who was a very patient sounding-board for all of my
crazy ideas, and to [kcsongor][kcsongor] who suggested that I pay a lot more
attention to where I'm being strict.

[kcsongor]: http://kcsongor.github.io/

