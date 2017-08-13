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
  { run :: a -> b
  , rev :: b -> a
  }
```

This type `a <=> b` represents an isomorphism between type `a` and type `b`, as
witnessed by a pair of functions `to` and `from`. This probably isn't the best
encoding of an isomorphism, but for our purposes it will be sufficient.

James and Sabry present the following axioms of their language:

```haskell
swapP   ::       a + b <=> b + a
assocP  :: a + (b + c) <=> (a + b) + c
unite   ::       U * a <=> a
swapT   ::       a * b <=> b * a
assocT  :: a * (b * c) <=> (a * b) * c
distrib :: (a + b) * c <=> (a * c) + (b * c)
id      ::           a <=> a
```

The implementations of these terms are all trivial, being that they are purely
syntactic isomorphisms. They will not be reproduced here, but can be found in
the [code accompanying this post][code]. The motivated reader is encouraged to
implement these for themself.

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

It's crazy, but it actually works! We can run these things to convince
ourselves. Given:

```haskell
not :: Bool <=> Bool
not = swapP  -- move a left ('true') to a right ('false'), and vice versa.
```

We get:

```
> run (ifthen not) $ Pair true false
Pair true true

> run (ifthen not) $ Pair false false
Pair false false
```

Neat, no? For fun, we can also run these things *backwards*:

```
> rev (ifthen not) $ Pair true true
Pair true false

> rev (ifthen not) $ Pair false false
Pair false false
```

James et al. are eager to point out that `ifthen (ifthen not) :: Bool * (Bool *
Bool) <=> Bool * (Bool * Bool)` is the [Toffoli gate][toffoli] -- a known
universal reversible gate. Because we can implement Toffoli (and due to its
universalness), we can thus implement *any* boolean expression.

[toffoli]: https://en.wikipedia.org/wiki/Toffoli_gate


## Recursion and Natural Numbers

Given two more primitives, James and Sabry show us how we can extend this
language to be "expressive enough to write arbitrary looping programs, including
non-terminating ones."

We'll need to define a term-level recursion axiom:

```haskell
trace :: (a + b <=> a + c) -> (b <=> c)
```

The semantics of `trace` are as follows: given an incoming `b` (or,
symmetrically, a `c`), lift it into `InR b :: a + b`, and then run the given iso
over it looping until the result is an `InR c`, which can then be returned.

Notice here that we have introduced potentially non-terminating looping.
Combined with our universal boolean expressiveness, this language is now
Turing-complete, meaning it is capable of computing anything computable.
Furthermore, by construction, we *also* have the capability to compute backwards
-- given an output, we can see what the original input was.

You might be concerned that the potential for partiality given by the `trace`
operator breaks the bijection upon which all of our reversibility has been
based. This, we are assured is not a problem, because a divergence is never
actually observed, and as such, does not *technically* violate the
bijectiveness. It's fine, you guys. Don't worry.


There is one final addition we need, which is the ability to represent inductive
types:

```haskell
data Fix f = Fix { unFix :: f (Fix f) }

fold :: f (Fix f) <=> Fix f
fold = Iso Fix unFix
```

Given these things, we can define the natural numbers a little circuitously. We
can define their type as follows:

```haskell
type Nat = Fix ((+) U)
```

Constructing such things is a little tricky, however. First we'll need a way to
introduce a coproduct. The type and name of this isomorphism should be
suggestive:

```haskell
just :: a <=> U + a
just = trace $ do
  sym assocP
  (sym fold >> swapP) .+ id
```

`just` is a tricky little beast; it works by using `trace` to eliminate the `Nat
+ U` of a `(Nat + U) + (U + a)`. We can follow the derivation a little more
closely:

```haskell
body :: (Nat + U) + a <=> (Nat + U) + (U + a)
body = do
  sym assocP      -- Nat + (U + a)
  sym fold .+ id  -- (U + Nat) + (U + a)
  swapP    .+ id  -- (Nat + U) + (U + a)

trace body :: a <=> U + a
```

I wish I had come up with this, because it's quite clever. Notice however that
this is a partial isomorphism; when run backwards, it will diverge in the case
of `InR U :: U + a`.

Given `just`, we can now define `succ`:

```haskell
succ :: Nat <=> Nat
succ = do
  just  -- U + Nat
  fold  -- Nat
```

James et al. provide a little more machinery in order to get to the introduction
of a 0:

```haskell
injectR :: a <=> a + a
injectR = do
  sym unite       -- U * a
  just .* id      -- (U + U) * a
  distrib         -- (U * a) + (U * a)
  unite .+ unite  -- a + a
```

and finally:

```haskell
zero :: U <=> Nat
zero = trace $ do
  id       -- Nat + U
  swapP    -- U + Nat
  fold     -- Nat
  injectR  -- Nat + Nat
```

What's interesting here is that the introduction of 0 is an isomorphism between
`U` and `Nat`, as we should expect since 0 is a constant.


### Induction on Nats

The paper teases an implementation of `isEven` for natural numbers -- from the
text:

> For example, it is possible to write a function `even? :: Nat * Bool <=> Nat *
> Bool` which, given inputs `(n, b)`, reveals whether `n` is even or odd by
> iterating `not` `n`-times starting with `b`. The iteration is realized using
> `trace` as shown in the diagram below **(where we have omitted the boxes for
> `fold` and `unfold`)**.

Emphasis mine. The omitted `fold` and `unfold` bits of the diagram are the
actual workhorses of the isomorphism, and their omission caused me a few days of
work to rediscover. I have presented the working example here to save you,
gentle reader, from the same frustration.

The insight is this -- our desired isomorphism has type `Nat * a <=> Nat * a`.
Due to its universally qualified nature, we are unable to pack any information
into the `a`, and thus to be reversible, the `Nat` must be the same on both
sides. Since we are unable to clone arbitrary values given our axioms
(seriously!  try it!), our only solution is to build a resulting `Nat` up from 0
as we tear apart the one we were given.

We can view the `a` in `trace :: (a + b <=> a + c) -> (b <=> c)` as "scratch
space" or "intermediate state". It is clear that in order to execute upon our
earlier insight, we will need three separate pieces of state: the `Nat` we're
tearing down, the `Nat` we're building up, and the `a` along for the ride.

For reasons I don't deeply understand, other than it happened to make the
derivation work, we also need to introduce a unit to the input of our traced
combinator.

With this line of reasoning, we have the following:

```haskell
iterNat :: (a <=> a) -> (Nat * a <=> Nat * a)
iterNat step = do
  sym unite
  trace $ do
    id  -- (Nat' * (Nat * a)) + (U * (Nat * a))
  unite
```

For clarity, we'll annotate the natural number under construction as `Nat'`.

When the iteration begins, our combinator receives an `InR` whose contents are
of type `U * (Nat * a)` corresponding to the fact that there is not yet any
internal state. From there we can factor our the `Nat * a`:

```haskell
  ...
  trace $ do
    id           -- (Nat' * (Nat * a)) + (U * (Nat * a))
    sym distrib  -- (Nat' + U) * (Nat * a)
  ...
```

All of a sudden this looks like a more tenable problem. We now have a product of
(conceptually) a `Maybe Nat'`, the `Nat` being torn down, and our `a`. We can
`fold :: U + Nat <=> Nat` our `Nat'`, which will give us 0 in the case that the
state hasn't yet been created, or $n+1$ in the case it has.

```haskell
  ...
  trace $ do
    id                     -- (Nat' * (Nat * a)) + (U * (Nat * a))
    sym distrib            -- (Nat' + U) * (Nat * a)
    (swapP >> fold) .* id  -- Nat' * (Nat * a)
  ...
```

The only thing left is to destruct the incoming `Nat` and apply our `step`
isomorphism. We introduce a lemma to help:

```haskell
swapBacT :: a * (b * c) <=> b * (a * c)
sw = do
  assocT
  swapT .* id
  sym assocT
```

which we can then use to move the pieces of our state and destruct the correct
number:

```haskell
  ...
  trace $ do
    id                         -- (Nat' * (Nat * a)) + (U * (Nat * a))
    sym distrib                -- (Nat' + U) * (Nat * a)
    (swapP >> fold) .* id      -- Nat' * (Nat * a)
    sw                         -- Nat * (Nat' * a)
    (sym fold >> swapP) .* id  -- (Nat + U) * (Nat' * a)
  ...
```

We can then distribute out the `Nat + U` again:


```haskell
  ...
  trace $ do
    id                         -- (Nat' * (Nat * a)) + (U * (Nat * a))
    sym distrib                -- (Nat' + U) * (Nat * a)
    (swapP >> fold) .* id      -- Nat' * (Nat * a)
    sw                         -- Nat * (Nat' * a)
    (sym fold >> swapP) .* id  -- (Nat + U) * (Nat' * a)
    distrib                    -- (Nat * (Nat' * a)) + (U * (Nat' * a))
  ...
```

And finally, we apply our `step` iso to the internal state (we do this after the
`distrib` so that we don't apply the combinator if the incoming number was 0).
The fruits of our labor are presented in entirety:

```haskell
iterNat :: (a <=> a) -> (Nat * a <=> Nat * a)
iterNat step = do
  sym unite
  trace $ do
    id                                -- (Nat' * (Nat * a)) + (U * (Nat * a))
    sym distrib                       -- (Nat' + U) * (Nat * a)
    (swapP >> fold) .* id             -- Nat' * (Nat * a)
    sw                                -- Nat * (Nat' * a)
    (sym fold >> swapP) .* id         -- (Nat + U) * (Nat' * a)
    distrib                           -- (Nat * (Nat' * a)) + (U * (Nat' * a))
    (id .* (id .* step) >> sw) .+ id  -- (Nat' * (Nat * a)) + (U * (Nat' * a))
  unite
```

Lo and behold, the types now line up, and thus quod erat demonstrandum. The
implementation of `isEven` is now trivial:

```haskell
isEven :: Nat * Bool <=> Nat * Bool
isEven = iterNat not
```

which computes if a `Nat` is even in the case the incoming `Bool` is `false`,
and whether it is odd otherwise.


## Lists

James and Sabry provide a sketch of how to define lists, but I wanted to flesh
out the implementation to test my understanding.

For reasons I don't pretend to understand, Haskell won't let us partially apply
a type synonym, so we're forced to write a higher-kinded data definition in
order to describe the shape of a list.

```haskell
-- To be read as @type ListF a b = U + (a * b)@.
data ListF a b
  = Nil
  | Cons a b
```

We can then get the fixpoint of this in order to derive a real list:

```haskell
type List a = Fix (ListF a)
```

And to get around the fact that we had to introduce a wrapper datatype in order
to embed this into Haskell, we then provide an eliminator to perform "pattern
matching" on a `List a`. In a perfect world, this function would just be `sym
fold`, but alas, we must work with what we have.

```haskell
liste :: List a <=> U + (a * List a)
liste = Iso to from
  where
    to (Fix Nil)          = InL U
    to (Fix (Cons a b))   = InR (Pair a b)
    from (InL U)          = Fix Nil
    from (InR (Pair a b)) = Fix (Cons a b)
```

From here, it is trivial to write `cons`:

```haskell
cons :: a * List a <=> List a
cons = do
  just       -- U + (a * List a)
  sym liste  -- List
```

However, introducing a list via `nil` is actually quite complicated. Note the
parallels with the natural numbers, where it was trivial to define `succ` but
required a clever trick to introduce a `zero`.

We begin with a lemma that moves a coproduct:

```haskell
swapCbaP :: (a + b) + c <=> (c + b) + a
swapCbaP = do
  sym assocP   -- a + (b + c)
  swapP        -- (b + c) + a
  swapP .+ id  -- (c + b) + a
```

And given that, we can write an isomorphism between any `a` and any `b`. The
catch, of course, is that you can never witness such a thing since it obviously
doesn't exist. Nevertheless, we can use it to convince the type checker that
we're doing the right thing in cases that would diverge in any case.

```haskell
diverge :: a <=> b
diverge = trace $ do
  id                 -- (a + b) + a
  swapP .+ id        -- (b + a) + a
  swapCbaP           -- (a + a) + b
  sym injectR .+ id  -- a + b
  swapP              -- b + a
  right .+ id        -- (b + b) + a
  swapCbaP           -- (a + b) + b
```

Finally we can implement `nil` using the same trick we did for `zero` -- use
`trace` to vacuously introduce exactly the type we need, rip out the result, and
then divergently reconstruct the type that `trace` expects.

```haskell
nil :: U <=> List a
nil = trace $ do
  id                        -- (a * List a) + U
  swapP                     -- U + (a * List a)
  sym liste                 -- List a
  sym unite                 -- U * List a
  just .* id                -- (U + U) * List a
  distrib                   -- (U * List a) + (U * List a)
  (diverge .* id) .+ unite  -- (a * List a) + List a
```


