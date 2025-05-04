---
layout: post
title: liftA2 on Maps
date: TO_BE_DETERMINED
comments: true
tags: foo, bar
---

The other day, someone asked:

> Why doesn't [the Data.Map function] `unionWith :: (a -> a -> a) -> Map k a ->
> Map k a -> Map k a` allow for different value types the way `intersectionWith
> :: (a -> b -> c) -> Map k a -> Map k b -> Map k c` does?

This is a very reasonable question, and it lead down an interesting rabbit hole
of at the intersection of API design and efficient implementation.

To answer the original question, what would the type of a different value type
of `unionWith` look like? It would be something in the flavor of:

```haskell
unionWith :: (Maybe a -> Maybe b -> c) -> Map k a -> Map k b -> Map k c
```

But this new `Maybe a -> Maybe b -> c` parameter is somewhat lossy, in that it
gives the impression that it could be called with `Nothing Nothing` as
parameters, which doesn't fit into the vibe of being a "union."

So instead we could restrict that possibility by using `These a b`:

```haskell
data These a b = This a | That b | These a b

unionWith :: (These a b -> c) -> Map k a -> Map k b -> Map k c
```

which seems reasonable enough.

---

But let's take *reasonableness* out of the picture and start again from first
principles. Instead let's ask ourselves the deep philsophical question of *what
even IS a map?*

A `Map k v` is a particularly efficient implementation of functions with type `k
-> Maybe v`. But why is this `Maybe` here? It's really only to encode the
"default" value of performing a lookup. Nothing goes wrong if we generalize this
to be `Monoid v => k -> v`. In fact, it helps us make sense of the right bias
present in `Data.Map`, where we see:

```haskell
lookup k (singleton k v1 <> singleton k v2) = Just v2
```

This equality is hard to justify under the normal understanding of `Map k v`
being an encoding of a function `k -> Maybe v`. But under the general monoid
interpretation, we get a nice semigroup homomorphism:

```haskell
lookup k (m1 <> m2) = lookup k m1 <> lookup k m2
```

where the monoid in question has been specialized to be
[`Last`](https://hackage.haskell.org/package/base-4.21.0.0/docs/Data-Monoid.html#t:Last).

Of course, we also have a monoid homomorphism:

```haskell
lookup k mempty = mempty
```

Let's re-evaluate the original question in terms of this newly-generalized
`Map`. Now that we've removed all of the unnecessary baggage of `Maybe`, we can
again think about the desired type of `unionWith`:

```haskell
unionWith
    :: (a -> b -> c)
    -> Map k a
    -> Map k b
    -> Map k c
```

which looks [awfully
familiar](https://hackage.haskell.org/package/base-4.21.0.0/docs/Prelude.html#v:liftA2).
This new type signature automatically resolves our original concerns about "what
should we do if the key isn't present?"---just call the function with `mempty`
as a parameter!

We can give some semantics as to what `unionWith` ought to do again by relating
it to the observation `lookup`. The relevant law here seems like it ought to be:

```haskell
lookup k (unionWith f m n) = f (lookup k m) (lookup k n)
```

By choosing a degenerate function `f`, say, `\_ _ -> nontrivial`, where
`nontrivial` is some value that is *not* `mempty`, we can see the beginnings of
a problem:

```haskell
  lookup k (unionWith f m n)
=
  f (lookup k m) (lookup k n)
= <let f = \_ _ -> nontrivial>
  nontrivial
```

Regardless of the key we lookup in our `unionWith`ed `Map`, we need to get back
`nontrivial`. How can we implement such a thing? I see only two ways:

1. explicitly associate every key in the map with `nontrivial`, or
2. keep `nontrivial` around as a default value in the map

#1 is clearly a non-starter, given that we want our `Map`s to be *efficient*
encodings of functions, which leaves us with only #2. This is actually a pretty
common construction, which stems immediately from the fact that a pair of
monoids is itself a monoid. The construction would look something like this:

```haskell
data Map k v = Map
  { defaultValue :: v
  , implementation :: Data.Map.Map k v
  }
  deriving stock Generic
  deriving (Semigroup, Monoid) via (Generically (Map k v))

unionWith
    :: (a -> b -> c)
    -> Map k a
    -> Map k b
    -> Map k c
unionWith f (Map def1 imp1) (Map def2 imp2) =
  Map (f def1 def2) (liftA2 f imp1 imp2)
```

Seems fine, right? The nail in the coffin comes from when we reintroduce our
semigroup homomorphism:

```haskell
lookup k (m1 <> m2) = lookup k m1 <> lookup k m2
```

Without loss of generalization, take `m2 = pure nontrivial` (where `pure` is
just `unionWith` with a constant function.) This gives us:

```haskell
lookup k (m1 <> pure nontrivial) = lookup k m1 <> nontrivial
```

Making this thing efficient is a further complication! We again have two
options:

1. modify the value at every key by multiplying in `nontrivial`, or
2. finding a way of suspending this computation

#1 clearly requires $O(n)$ work, which again forces us to look at #2. But #2
seems very challenging, because the monoidal values we need to suspend _need
not_ span the entire `Map`. For example, consider a `Map` constructed a la:

```haskell
((pure prefix1 <> ((pure prefix2 <> m) <> n)) <> (p <> pure suffix)
```

Representing this thing efficiently certainly isn't impossible, but you're not
going to be able to do it on the balanced binary search trees that underlie the
implementation of `Data.Map.Map`.

---

I find this quite an interesting result. I always assumed that `Data.Map.Map`
(or at least, `Data.Map.Monoidal.MonoidalMap`) didn't have an `Applicative`
instance because it would require a `Monoid` constraint on its output---but
that's not the sort of thing we can express in Haskell.

But the analysis above says that's not actually the reason! It's that there can
be no efficient implementation of `Applicative`, even if we *could* constrain
the result.

What I find so cool about this style of analysis is that we didn't actually write
any code, nor did we peek into the implementation of `Data.Map` (except to know
that it's implemented as a balanced BST.) All we did was look at the obvious
laws, instantiate them with degenerate inputs, and think about what would be
required to to efficiently get the right answer.

