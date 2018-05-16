---
layout: post
title: Follow the Denotation
date: 2018-05-03 15:11
comments: true
tags: papers, review, elliott, haskell, denotational design
---

> Your scientists were so preoccupied with whether or not they could, they
> didn't stop to think if they should.
>
> Ian, Jurassic Park


## Overview

Designing an abstraction or library often feels wonderfully unconstrained; it is
the task of the engineer (or logician) to create something from nothing. With
experience and training, we begin to be able to consider and make trade-offs:
efficiency vs simplicity-of-implementation vs ease-of-use vs preventing our
users from doing the wrong thing, among many other considerations. Undeniably,
however, there seems to be a strong element of "taste" that goes into design as
well; two engineers with the same background, task, and sensibilities will still
come up with two different interfaces to the same abstraction.

The tool of denotational design aims to help us nail down exactly what is this
"taste" thing. Denotational design gives us the ability to look at
designs and ask ourselves whether or not they are *correct.*

However, it's important to recognize that having a tool to help us design
doesn't need to take the *fun* out of the endeavor. Like any instrument, it's up
to the craftsman to know when and how to apply it.

This essay closely works through [Conal Elliott][conal]'s fantastic paper
[Denotational design with type class morphisms][deno].

[conal]: http://conal.net/
[deno]: http://conal.net/papers/type-class-morphisms/type-class-morphisms-long.pdf


## Example: Maps

Consider the example of `Data.Map.Map`. At it's essence, the interface is
given by the following "core" pieces of functionality:

```haskell
empty  :: Map k v
insert :: k -> v -> Map k v -> Map k v
lookup :: k -> Map k v -> Maybe v
union  :: Map k v -> Map k v -> Map k v
```

With the laws:

```haskell
-- get back what you put in
lookup k   (insert k v m) = Just v

-- keys replace one another
insert k b (insert k a m) = insert k b m

-- empty is an identity for union
union empty m = m
union m empty = m

-- union is just repeated inserts
insert k v m = union (insert k v empty) m
```

These laws correspond with our intuitions behind what a `Map` is, and
furthermore, capture exactly the semantics we'd like. Although it might seem
silly to explicitly write out such "obvious" laws, it is the laws that give your
abstraction meaning.

Consider instead the example:

```haskell
empathy :: r -> f -> X r f -> X r f
fear    :: e -> X e m -> Either () m
taste   :: X o i -> X o i -> X o i
zoo     :: X z x
```

It might take you some time to notice that this `X` thing is just the result
of me randomly renaming identifiers in `Map`. The names are valuable to us
only because they suggest meanings to us. Despite this, performing the same
substitutions on the `Map` laws would still capture the semantics we want.
The implication is clear: names are helpful, but laws are invaluable.


## Meanings

Our quick investigation into the value of laws has shown us one example of how
to assert meaning on our abstractions. We will now take a more in-depth look at
another way of doing so.

Let us consider the concept of a "meaning functor." We can think of the term
`μ(Map k v)` as "the meaning of `Map k v`." `μ(Map k v)` asks not
how is `Map k v` implemented, but instead, how should we think about it? What
metaphor should we use to think about a `Map`? The $\mu(\cdot)$ operator,
like any functor, will map types to types, and functions to functions.

We can encode this mapping as a function, and the partiality with `Maybe`:

```haskell
μ(Map k v) = k -> Maybe v
```

With the meaning of our type nailed down, we can now also provide meanings for
our primitive operations on `Map`s:


```haskell
  μ(empty) = \k -> Nothing
```

An empty map is one which assigns `Nothing` to everything.


```haskell
  μ(lookup k m) = μ(m) k
```

Looking up a key in the map is just giving back the value at that key.

```haskell
  μ(insert k' v m) = \k ->
    if k == k'
      then Just v
      else μ(m) k
```

If the key we ask for is the one we inserted, give back the value associated
with it.

```haskell
  μ(union m1 m2) = \k ->
    case μ(m1) k of
      Just v  -> Just v
      Nothing -> μ(m2) k
```

Attempt a lookup in a union by looking in the left map first.

Looking at these definitions of meaning, it's clear to see that they capture an
intuitive (if perhaps, naive) meaning and implementation of a `Map`.
Regardless of our eventual implementation of `Map`, $\mu(\cdot)$ is a
functor that transforms it into the same "structure" (whatever that means) over
*functions.*

Herein lies the core principle of denotational design: for any type `X` designed
in this way, `X` *must be isomorphic* to `μ(X)`; literally no observational (ie.
you're not allowed to run a profiler on the executed code) test should be able
to differentiate one from the other.

This is not to say that it's necessary that `X = μ(X)`. Performance
or other engineering concerns may dissuade us from equating the two -- after
all, it would be insane if `Map` were actually implemented as a big chain of
nested if-blocks. All we're saying is that nothing in the implementation is
allowed to break our suspension of believe that we are actually working with
`μ(Map)`. Believe it or not, this is a desirable property; we all have a
lot more familiarity with functions and other fundamental types than we do with
the rest of the (possibly weird corners of) ecosystem.

The condition that `X` $\cong$ `μ(X)` is much more constraining than it
might seem at first glance. For example, it means that all instances of our
type-classes must agree between `X` and `μ(X)` -- otherwise we'd be
able to differentiate the two.

Our `Map` has some obvious primitives for building a `Monoid`, so let's do
that:

```haskell
instance Monoid (Map k v) where
  mempty  = empty
  mappend = union
```

While this is indeed a `Monoid`, it looks like we're already in trouble. The
`Monoid` instance definition for `μ(Map)`, after specializing to our
types, instead looks like this:

```haskell
instance Monoid v => Monoid (k -> Maybe v) where
```

There's absolutely no way that these two instances could be the same. Darn.
Something's gone wrong along the way; suggesting that `μ(Map)` isn't in
fact a denotation of `Map`. Don't panic; this kind of thing happens. We're
left with an intriguing question; is it our meaning functor that's wrong, or the
original API itself?


## Homomorphisms

Our instances of `Monoid Map` and `Monoid μ(Map)` do not agree, leading
us to the conclusion that `μ(Map)` *cannot be* the denotation for
`Map`. We are left with the uneasy knowledge that at least one of them is
incorrect, but without further information, we are unable to do better.

A property of denotations is that their instances of typeclasses are always
homomorphisms,  which is to say that they are *structure preserving.* Even if
you are not necessarily familiar with the word, you will recognize the concept
when you see it. It's a pattern that often comes up when writing instances over
polymorphic datastructures.

For example, let's look at the `Functor` instance for a pair of type `(a, b)`:

```haskell
instance Functor ((,) a) where
  fmap f (a, b) = (a, f b)
```

This is a common pattern; unwrap your datatype, apply what you've got anywhere
you can, and package it all up again in the same shape. It's this "same shape"
part that makes the thing structure preserving.

The principle to which we must adhere can be expressed with a pithy phrase: *the
meaning of the instance is the instance of the meaning.* This is true for any
meaning functor which is truly a denotation. What this means, for our
hypothetical type `μ(X)`, is that all of our instances must be of this form:

```haskell
instance Functor μ(X) where
  μ(fmap f x) = fmap f μ(x)

instance Applicative μ(X) where
  μ(pure x)  = pure x
  μ(f <*> x) = μ(f) <*> μ(x)
```

and so on.

Having such a principle gives us an easy test for whether or not our meaning
functor is correct; if any of our instances do not reduce down to this form, we
know our meaning must be incorrect. Let's take a look at our implementation of
`mempty`:

```haskell
μ(mempty) = \k -> Nothing
          = \k -> mempty
          = const mempty
          = mempty  -- (1)
```

At (1), we can collapse our `const mempty` with `mempty` because
that is the definition of the `Monoid ((->) a)` instance. So far, our meaning
is looking like a true denotation. Let's also look at `mappend`:

```haskell
μ(mappend m1 m2) = \k ->
  case μ(m1) k of
    Just v  -> Just v
    Nothing -> μ(m2) k
```

It's not immediately clear how to wrestle this into a homomorphism, so let's
work backwards and see if we can go backwards:

```haskell
mappend μ(m1) μ(m2)
    = mappend (\k -> v1) (\k -> v2)
    = \k -> mappend v1 v2
    = \k ->
        case v1 of   -- (2)
          z@(Just a) ->
            case v2 of
              Just b  -> Just $ mappend a b
              Nothing -> z
          Nothing -> v2
```

At (2) we inline the definition of `mappend` for `Maybe`.

That's as far as we can go, and, thankfully, that's far enough to see that our
instances do not line up. While `mappend` for `μ(Map)` is left-biased,
the one for our denotation may not be.

We're left with the conclusion that our meaning functor $\mu(\cdot)$ must be
wrong; either the representation of `μ(Map)` is incorrect, or our meaning
`μ(mappend)` is. Fortunately, we are free to change either in order to
make them agree. Because we're sure that the left-bias in `mappend` is indeed
the semantics we want, we must change the representation.

Fortunately, this is an easy fix; `Data.Monoid` provides the `First`
newtype wrapper, which provides the left-biased monoid instance we want.
Substituting it in gives us:

```haskell
μ(Map k v) = k -> First v
```

Subsequent analysis of this revised definition of `μ(Map)` reveals that
indeed it satisfies the homomorphism requirement. This is left as an exercise to
the reader.


## (De)composition of Functors

 We have now derived a denotation behind `Map`, one with a sensible `Monoid`
instance. This gives rise to a further question---which other instances should
we provide for `Map`?

`Map` is obviously a `Functor`, but is it an `Applicative`? There are certainly
*implementations* for `Applicative (Map k)`, but it's unclear which is the one
we should provide. To make the discussion concrete, what should be the semantics
behind `pure 17`? Your intuition probably suggests we should get a singleton
`Map` with a value of 17, but what should it's key be?  There's no obvious
choice, unless we ensure `k` is a `Monoid`.

Another alternative is that we return a `Map` in which *every* key maps to 17.
This is implementation suggested by the `Applicative` homomorphism of `μ(Map)`,
but it doesn't agree with our intuition. Alternatively, we could follow in the
footsteps of `Data.Map.Map`, whose solution to this predicament is to sit on the
fence, and not provide any `Applicative` instance whatsoever.

Sitting on the fence is not a very satisfying solution, however.  `Applicative`
is a particularly useful class, and having access to it would greatly leverage
the Haskell ecosystem in terms of what we can do with our `Map`. As a general
rule of thumb, any type which *can* be an instance of the standard classes
*should* be, even if it requires a little finagling in order to make happen.

We find ourselves at an impasse, and so we can instead turn to other tweaks in
our meaning functor, crossing our fingers that they will elicit inspiration.

Given the `Compose` type from `Data.Functor.Compose`, we can re-evaluate our
choices once more (as we will see, this is a common theme in denotational
design.)

```haskell
data Compose f g a = Compose
  { getCompose :: f (g a)
  }
```

`Compose` is a fantastic tool when building new types that are composites of
others. For example, consider the meaning of `μ(Map k v) = \k -> First v`. If
we'd like to `fmap` over the `v` here, we'll need to perform two of them:

```haskell
             f  ::         v  ->         w
  fmap (fmap f) :: μ(Map k v) -> μ(Map k w)
```

Although it seems minor, this is in fact quite a large inconvenience. Not only
does it require us two `fmap` through two layers of functors, more egregiously,
it allows us to use a *single* `fmap` to break the abstraction. Consider the
case of `fmap (const 5)` -- this will transform a `μ(Map k v)` into a `k -> 5`,
which is obviously *not* a functor.  Yikes.

We instead can re-redefine `μ(Map k v)`:

```haskell
`μ(Map k v) = Compose ((->) k) First v`
```

Presented in this form, we are exposed to another interpretation of what our
type means. `μ(Map)` is a composition of some sort of *mapping-ness* `((->) k)`
and of *partiality* (`First`). The mapping-ness is obviously crucial to the
underlying concept, but it's harder to justify the partiality. One
interpretation is that we use the `Nothing` value to indicate there was no
corresponding key, but another is that we use `Nothing` as a *default value*.

When viewed as a default, a few minutes' pondering on this thought reveals that
a partial map (`k -> Maybe v`) is just a special case of a total map (`k
-> v`) where the value itself is partial. Maybe---if you'll excuse the
pun---partiality is completely orthogonal to the semantics we want to express.

As our final (and ultimately correct) attempt, we define

```haskell
μ(Map k v) = \k -> v
```

From here, the problem of "what typeclasses should this thing have" becomes
quite trivial---we should provide equivalent instances for all of those of
`k -> v`. The question about what should our `Applicative` instance do
is resolved: the same thing arrows do.

A point worth stressing here is that just because the *meaning* of `Map
k v` is `k -> v`, it doesn't mean our *representation* must be. For
example, we could conceive implementing `Map` as the following:

```haskell
data Map k v = Map
  { mapDefVal :: v
  , mapTree   :: BalancedTree k v
  }

lookup :: Ord k => Map k v -> k -> v
lookup m = fromMaybe (mapDefVal m) . treeLookup (mapTree m)
```

Such an implementation gives us all of the asymptotics of a tree-based map, but
the denotations of (and therefore the *intuitions* behind) functions.

Hopefully this worked example has given you some insight into how the process of
denotational design works. Guess at a denotation and then ruthlessly refine
it until you get something that captures the real essence of what you're trying
to model. It's an spectacularly rewarding experience to find an elegant solution
to a half-baked idea, and your users will thank you to boot.

