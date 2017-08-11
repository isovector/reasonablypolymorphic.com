---
layout: post
title: "Review: Information Effects"
date: 2017-08-08 22:37
comments: true
tags: papers, review, james, sabry, haskell, reversible computing
---

One of the most exciting papers I've read in a long time is James and Sabry's
[Information Effects][paper]. It starts with the hook "computation is a physical
process which, like all other physical processes, is fundamentally reversible,"
and it goes from there. If that doesn't immediately pull you in, perhaps some of
the subsequent PL jargon will -- it promises a "typed, universal, and
reversible computation model in which information is treated as a linear
resource".

[paper]:

I don't know about you, but I was positively shaking with anticipation at this
point. That's one heck of an abstract.

After some philosophy and overview of the paper, James and Sabry dive into the
appetizer in a section titled "Thermodynamics of Computation and Information".
They give the following definition:

> DEFINITION 2.2 (Entropy of a variable). Let $b$ be a (not necessarily finite)
> type whose values are labeled $b_1$, $b_2$, $\ldots$. Let $\xi$ be a random
> variable of type $b$ that is equal to $b_i$ with probability $p_i$. The
> entropy of $\xi$ is defined as $- \sum p_i \log{p_i}$.

and the following, arguably less inspired definition:

> DEFINITION 2.3 (Output entropy of a function). Consider a function `f : a ->
> b` where `b` is a (not necessarily finite) type whose values are labeled
> $b_1$, $b_2$, $\ldots$. The output entropy of the function is given by $- \sum
> q_j \log{q_j}$ where $q_j$ indicates the probability of the function to have
> value $b_j$.

We can say now that a function is reversible if and only if the entropy of its
arguments is equal to the entropy of its output. Which is to say that the gain
in entropy across the function is 0.

Of course, as astute students of mathematics we know that reversibility of a
function is equivalent to whether that function is an isomorphism. While this is
how we will prefer to think of reversibility, the definition in terms of entropy
brings up interesting questions of pragmatics that we will get to later.

James et al. present the following language, which we have reproduced here
translated into Haskell. The language is first order, and so we will ignore
function types, giving us the types:

```haskell
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE NoImplicitPrelude #-}

-- Corresponds to Haskell '()' type
data U = U

-- Corresponds to Haskell 'Either' type
data a + b
  = InL a
  | InR a

-- Corresponds to Haskell '(,)' type
data a * b = Pair a b
```

The language presented is based around the notion of type isomorphisms, and so
in order to model this language in Haskell, we'll need the following types:

```haskell
data a <=> b = Iso
  { to   :: a -> b
  , from :: b -> a
  }
```

This type `a <=> b` represents an isomorphism between type `a` and type `b`, as
witnessed by a pair of functions `to` and `from`. This probably isn't the best
encoding of an isomorphism, but for our purposes it will be sufficient.

James and Sabry present the following axioms of their language:

```haskell
swapP   ::       a + b <=> b + a
asoccP  :: a + (b + c) <=> (a + b) + c
unite   ::       U * a <=> a
swapT   ::       a * b <=> b * a
assocT  :: a * (b * c) <=> (a * b) * c
distrib :: (a + b) * c <=> (a * c) + (b * c)
id      ::           a <=> a
```

The implementations of these terms are all trivial, being that they are purely
syntactic isomorphisms. They will not be reproduced here, but can be found in
the [code accompanying this post][code]. The motivated reader is encouraged to
implement them for themself.

[code]: TODO(sandy)

With the terms of our algebra out of the way, we're now ready for the operators.
We are presented with the following:

```haskell
-- Isomorphisms are symmetric.
sym :: (a <=> b) -> (b <=> a)

-- Isomorphisms are transitive.
(>>) :: (a <=> b) -> (b <=> c) -> (a <=> c)

-- Products and coproducts are bifunctors.
(.+) :: (a <=> c) -> (b <=> d) -> (a + b <=> c + d)
(.*) :: (a <=> c) -> (b <=> d) -> (a * b <=> c * d)
```

It turns out that the resulting language is already surprisingly expressive. We
can encode booleans:

```haskell
type Bool = U + U

true, false :: Bool
true  = InL U
false = InR U
```

With these out of the way, James et al. show us a "one-armed if-expression": if
the incoming `Bool` is `true`, transform the `a` by the provided combinator:

```haskell
ifthen :: (a <=> a) -> (Bool * a <=> Bool * a)
ifthen c = distrib >> (id .* c) .+ id >> sym distrib
```

For syntactic convenience, we will enable rebindable syntax, allowing us to
represent these chains of isomorphism transitivities with `do` notation. We can
thus express the above more clearly as:

```haskell
{-# LANGUAGE RebindableSyntax #-}

ifthen :: (a <=> a) -> (Bool * a <=> Bool * a)
ifthen c = do
  distrib
  (id .* c) .+ id
  sym distrib
```

The mystery behind naming our transitivity operator `(>>)` is thus explained.

But how does our `ifthen` combinator actually work? Recall that `Bool = U + U`,
meaning that we can distribute the `U`s across the pair, giving us the type `(U
* a) + (U * a)`. The left branch (of type `U * a`) of this coproduct has an
inhabitant if the incoming boolean was `true`.

We can thus bimap over the coproduct. Since the left case corresponds to an
incoming `true`, we can apply an isomorphism over only that branch. Because we
want to transform the incoming `a` by the combinator `c`, we then bimap over our
`U * a` with `id .* c` -- not touching the `U` but using our combinator.

Finally, we need to repackage our `(U * a) + (U * a)` into the correct return
type `Bool * a`, which we can do by factoring out the `a`. Factoring is the
inverse of `distrib`uting, and so we can use the `sym` operator to "undo" the
`distrib`.

It's crazy, but it actually works!

