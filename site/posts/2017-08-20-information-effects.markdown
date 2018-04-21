---
layout: post
title: "Review: Information Effects"
date: 2017-08-20 20:31
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

[paper]: https://www.cs.indiana.edu/~sabry/papers/information-effects.pdf

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

[code]: https://github.com/isovector/information-effects/blob/master/src/Main.hs

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
swapBacT = do
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
    swapBacT                   -- Nat * (Nat' * a)
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
    swapBacT                   -- Nat * (Nat' * a)
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
    id                          -- (Nat' * (Nat * a)) + (U * (Nat * a))
    sym distrib                 -- (Nat' + U) * (Nat * a)
    (swapP >> fold) .* id       -- Nat' * (Nat * a)
    swapBacT                    -- Nat * (Nat' * a)
    (sym fold >> swapP) .* id   -- (Nat + U) * (Nat' * a)
    distrib                     -- (Nat * (Nat' * a)) + (U * (Nat' * a))
    (id .* (id .* step)) .+ id  -- (Nat * (Nat' * a)) + (U * (Nat' * a))
    swapBacT .+ id              -- (Nat' * (Nat * a)) + (U * (Nat' * a))
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


### Induction on Lists

In a manner spiritually similar to `iterNat`, we can define `iterList :: (a * z
<=> b * z) -> (List a * z <=> List b * z)`. The semantics are mostly what you'd
expect from its type, except that the resulting `List b` is in reverse order due
to having to be constructed as the `List a` was being destructed. We present the
implementation here for completeness but without further commentary.

```haskell
iterList :: (a * z <=> b * z) -> (List a * z <=> List b * z)
iterList f = do
  sym unite
  trace $ do
                                -- ((b * List b) * (List a * z)) + (U * (List a * z))
    sym distrib                 -- ((b * List b) + U) * (List a * z)
    (swapP >> sym liste) .* id  -- List b * (List a * z)
    swapBacT                    -- List a * (List b * z)
    liste .* id                 -- (U + (a * List a)) * (List b * z)
    distrib                     -- (U * (List b * z)) + ((a * List a) * (List b * z))
    (.+) id $                   -- (U * (List b * z)) + ...
      do
        swapT .* id             --    ((List a * a) * (List b * z))
        swapAcbdT               --    ((List a * List b) * (a * z))
        id .* f                 --    ((List a * List b) * (b * z))
        swapAcbdT               --    ((List a * b) * (List b * z))

    swapP                       -- ((List a * b) * (List b * z)) + (U * (List b * z))
    (swapT .* id) .+ id         -- ((b * List a) * (List b * z)) + (U * (List b * z))
    swapAcbdT .+ id             -- ((b * List b) * (List a * z)) + (U * (List b * z))
  unite

swapAcbdT :: (a * b) * (c * d) <=> (a * c) * (b * d)
swapAcbdT = do
  sym assocT
  id .* sw
  assocT
```

From here, the functional programming favorite `map` is easily defined:

```haskell
map :: (a <=> b) -> (List a <=> List b)
map f = do
  sym unite
  swapT
  iterList $ f .* id  -- map
  iterList id         -- reverse to original order
  swapT
  unite
```


## Remnants

The bulk of the remainder of the paper is an extension to the reversible
semantics above, introducing `create :: U ~> a` and `erase :: a ~> U` where
`(~>)` is a non-reversible arrow. We are shown how traditional non-reversible
languages can be transformed into the `(~>)`-language.

Of more interest is James and Sabry's construction which in general transforms
`(~>)` (a non-reversible language) into `(<=>)` (a reversible one). But how can
such a thing be possible? Obviously there is a trick!

The trick is this: given `a ~> b`, we can build `h * a <=> g * b` where `h` is
"heap" space, and `g` is "garbage". Our non-reversible functions `create` and
`erase` thus become reversible functions which move data from the heap and to
the garbage respectively.

Unfortunately, this is a difficult thing to model in Haskell, since the
construction requires `h` and `g` to vary based on the axioms used. Such a thing
requires dependent types, which, while possible, is quite an unpleasant
undertaking. Trust me, I actually tried it.

However, just because it's hard to model entirely in Haskell doesn't mean we
can't discuss it. We can start with the construction of `(~>)`:

```haskell
{-# LANGUAGE GADTs #-}

data a ~> b where
  Arr     :: (a <=> b) -> (a ~> b)
  Compose :: (a ~> b) -> (b ~> c) -> (a ~> c)
  First   :: (a ~> b) -> (a * c ~> b * c)
  Left    :: (a ~> b) -> (a + c ~> b + c)
  Create  :: U ~> a
  Erase   :: a ~> U
```

The axioms here are quite explanatory and will not be discussed further. A point
of note, however, is that `Arr` allows arbitrary embeddings of our iso `(<=>)`
language in this arrow language.

The semantics of `Create` is given by induction:

$$
\newcommand{\u}{\text{U}}
\begin{align*}
\text{create U} & \mapsto \u \\
\text{create}(a + b) & \mapsto \text{InL } (\text{create } a) \\
\text{create}(a \times b) & \mapsto (\text{create } a, \text{create } b)
\end{align*}
$$


With the ability to create and erase information, we're (thankfully) now able to
write some everyday functions that you never knew you missed until trying to
program in the iso language without them. James et al. give us what we want:

```haskell
fstA :: a * b ~> a
fstA = do
  arr swapT    -- b * a
  first erase  -- U * a
  arr unite    -- a
```

In addition to projections, we also get injections:

```haskell
leftA :: a ~> a + b
leftA = do
  arr $ sym unite  -- U * a
  first create     -- (a + b) * a
  arr leftSwap     -- (a + b) * a
  fstA             -- a + b

leftSwap :: (a + b) * a <=> (a + b) * a
leftSwap = do
  distrib      -- (a * a') + (b * a')
  swapT .+ id  -- (a' * a) + (b * a')
  sym distrib  -- (a' + b) * a
```

And the ability to extract from a coproduct:

```haskell
join :: a + a ~> a
join = do
  arr $ do
    sym unite .+ sym unite  -- (U * a) + (U * a)
    sym distrib             -- (U + U) * a
    swapT                   -- a * (U + U)
  fstA                      -- a
```

We are also provided with the ability to clone a piece of information, given by
structural induction. Cloning `U` is trivial, and cloning a pair is just cloning
its projections and then shuffling them into place. The construction of cloning
a coproduct, however, is more involved:

```haskell
clone :: a + b ~> (a + b) * (a + b)
clone = do
  left $ do
    clone                -- (a * a) + b
    first leftA          -- ((a + b) * a) + b
    arr swapT            -- (a * (a + b)) + b
  arr swapP              -- b + (a * (a + b))
  left $ do
    clone                -- (b * b) + (a * (a + b))
    first leftA          -- ((b + a) * b) + (a * (a + b))
    arr swapT            -- (b * (b + a)) + (a * (a + b))
  arr $ do
    swapP                -- (a * (a + b)) + (b * (b + a))
    id .+ (id .* swapP)  -- (a * (a + b)) + (b * (a + b))
    sym distrib          -- (a + b) * (a + b)
```

It should be quite clear that this arrow language of ours is now more-or-less
equivalent to some hypothetical first-order version of Haskell (like
[Elm][elm]?). As witnessed above, information is no longer a linear commodity. A
motivated programmer could likely get work done in a 9 to 5 with what we've
built so far. It probably wouldn't be a lot of fun, but it's higher level than C
at the very least.

[elm]: http://reasonablypolymorphic.com/blog/elm-is-wrong

The coup de grace of Information Effects is its construction lifting our arrow
language *back* into the isomorphism language. The trick is to carefully
construct heap and garbage types to correspond exactly with what our program
needs to create and erase. We can investigate this further by case analysis on
the constructors of our arrow type:

```haskell
Arr :: (a <=> b) -> (a ~> b)
```

As we'd expect, an embedding of an isomorphism in the arrow language is already
reversible. However, because we need to introduce a heap and garbage anyway,
we'll use unit.

Since we can't express the typing judgment in Haskell, we'll use a sequent
instead:

$$
\newcommand{\lifted}[3]{\text{lift } #1 : #2 \leftrightarrow #3}
\newcommand{\arr}{\rightsquigarrow}
\frac{\text{arr } f : a \arr b}{\lifted{(\text{arr } f)}{\u
\times a}{\u \times b}}
$$

Assuming we have a way of describing this type in Haskell, all that's left is to
implement the `lift`ing of our iso into the enriched iso language:

```haskell
lift (Arr f) = id .* f
```

---

```haskell
Compose :: (a ~> b) -> (b ~> c) -> (a ~> c)
```

Composition of arrows proceeds likewise in a rather uninteresting manner. Here,
we have two pairs of heaps and garbages, results from lifting each of the arrows
we'd like to compose. Because composition will run *both* of our arrows, we'll
need both heaps and garbages in order to implement the result. By this logic,
the resulting heap and garbage types are pairs of the incoming ones.

$$
\frac{\lifted{f}{h_1\times a}{g_1\times b},\; \lifted{g}{h_2\times b}{g_2\times
c}}{\lifted{(g \circ f)}{(h_1\times h_2)\times a}{(g_1\times g_2)\times c}}
$$

We can express the resulting combinator in Haskell:

```haskell
lift (Compose f g) = do
  id            -- (H1 * H2) * a
  swapT .* id   -- (H2 * H1) * a
  sym assocT    -- H2 * (H1 * a)
  id .* lift f  -- H2 * (G1 * b)
  assocT        -- (H2 * G1) * b
  swapT .* id   -- (G1 * H2) * b
  sym assocT    -- G1 * (H2 * b)
  id .* lift g  -- G1 * (G2 * c)
  assocT        -- (G1 * G2) * c
```

---

```haskell
First :: (a ~> b) -> (a * c ~> b * c)
```

Lifting arrows over products again is uninteresting -- since we're doing nothing
with the second projection, the only heap and garbage we have to work with are
those resulting from the lifting of our arrow over the first projection.

$$
\frac{\lifted{f}{h\times a}{g\times b}}
{\lifted{(\text{First } f)}{h\times (a\times c)}{g\times (b\times c)}}
$$

In Haskell, our resulting combinator looks like this:

```haskell
lift (First f) = do
  id          -- H * (a * c)
  assocT      -- (H * a) * c
  f .* id     -- (G * b) * c
  sym assocT  -- G * (b * c)
```

---

```haskell
Left :: (a ~> b) -> (a + c ~> b + c)
```

Finally, we get to an interesting case. In the execution of `Left`, we may or
may not use the incoming heap. We also need a means of creating a `b + c` given
a `b` *or* given a `c`. Recall that in our iso language, we do not have `create`
(nor relatedly, `leftA`) at our disposal, and so this is a harrier problem than
it sounds at first.

We can solve this problem by requiring both a `b + c` and a `c + b` from the
heap. Remember that the Toffoli construction (what we're implementing here) will
create a reversible gate with additional inputs and outputs that gives the same
result when all of its inputs have their default values (ie. the same as those
provided by `create`'s semantics). This means that our incoming `b + c` and `c +
b` will both be constructed with `InL`.

Given this, we can thus perform case analysis on the incoming `a + c`, and then
use `leftSwap` from earlier to move the resulting values into their coproduct.

What does the garbage situation look like? In the case we had an incoming `InL`,
we will have used up our function's heap, as well as our `b + c`, releasing the
`g`, `b` (the default value swapped out of our incoming `b + c`), and the unused
`c + b`.

If an `InR` was input to our isomorphism, we instead emit the function's heap
`h`, the unused `b + c`, and the default `c` originally in the heap's coproduct.

Our final typing judgment thus looks like this:

$$
\frac{\lifted{f}{h\times a}{g\times b}}{\lifted{(\text{Left f})}{h'\times (a + c)}{g' \times (b + c)}}
$$

$$
h' = h\times ((b + c) \times(c + b)) \\
g' = (g\times (b\times(c + b))) + (h\times ((b+c)\times c))
$$

and is rather horrifyingly implemented:

```haskell
lift (Left f) = do
  swapT
  distrib
  leftSide f .+ rightSide
  sym distrib

leftSide
    :: (h * a <=> g * b)
    -> (a * (h * ((b + c) * (c + b))) <=> (g * (b * (c + b))) * (b + c))
leftSide f = do
  swapT                -- (H * ((b + c) * (c + b))) * a
  swapT .* id          -- (((b + c) * (c + b)) * H) * a
  sym assocT           -- ((b + c) * (c + b)) * (H * a)
  id .* f              -- ((b + c) * (c + b)) * (G * b')
  swapT .* id          -- ((c + b) * (b + c)) * (G * b')
  sw2                  -- ((c + b) * G) * ((b + c) * b')
  id .* leftSwap       -- ((c + b) * G) * ((b' + c) * b)
  swapT .* swapT       -- (G * (c + b)) * (b * (b' + c))
  assocT               -- ((G * (c + b)) * b) * (b' + c)
  sym assocT .* id     -- (G * ((c + b) * b)) * (b' + c)
  (id .* swapT) .* id  -- (G * (b * (c + b))) * (b' + c)

rightSide :: c * (h * ((b + c) * (c + b))) <=> (h * ((b + c) * c)) * (b + c)
rightSide = do
  swapT                -- c' * (H * ((b + c) * (c + b)))
  assocT .* id         -- ((H * (b + c)) * (c + b)) * c'
  sym assocT           -- (H * (b + c)) * ((c + b) * c')
  id .* leftSwap       -- (H * (b + c)) * ((c' + b) * c)
  id .* swapT          -- (H * (b + c)) * (c * (c' + b))
  assocT               -- ((H * (b + c)) * c) * (c' + b)
  sym assocT .* swapP  -- (H * ((b + c) * c)) * (b + c')
```

---

The home stretch is within sight. We have only two constructors of our arrow
language left. We look first at `Create`:

```haskell
Create  :: U ~> a
```

Because we've done all of this work to thread through a heap in order to give us
the ability to create values, the typing judgment should come as no surprise:

$$
\frac{}{\lifted{\text{create}}{a\times\u}{\u\times a}}
$$

Our heap contains the `a` we want, and we drop our incoming `U` as garbage. The
implementation of this is obvious:

```haskell
lift Create = swapT
```

---

We're left with `Erase`, whose type looks suspiciously like running `Create` in
reverse:

```haskell
Erase  :: a ~> U
```

This is no coincidence; the two operations are duals of one another.

$$
\frac{}{\lifted{\text{erase}}{\u\times a}{a\times\u}}
$$

As expected, the implementation is the same as `Create`:

```haskell
lift Erase = swapT
```

And we're done! We've now constructed a means of transforming any non-reversible
program into a reversible one. Success!


## Summary

Still here? We've come a long way, which we'll briefly summarize. In this paper,
James and Sabry have taken us through the construction of a reversible language,
given a proof that it's Turing-complete, and given us some simple constructions
on it. We set out on our own to implement lists and derived `map` for them.

We then constructed a non-reversible language (due to its capability to create
and erase information), and then gave a transformation from this language to our
earlier reversible language -- showing that non-reversible computing is a
special case of its reversible counterpart.

Information Effects ends with a short discussion of potential applications,
which won't be replicated here.


## Commentary (on the physics)

Assuming I understand the physics correctly (which I probably don't), the fact
that these reversible functions do not increase entropy implies that they should
be capable of shunting information for near-zero energy. [Landauer's
Principle][landauer] and [Szilard's engine][szilard] suggests that information entropy
and thermodynamic entropy are *one and the same*; if we don't increase entropy
in our computation of a function, there is nowhere for us to have created any
heat.

[landauer]: https://en.wikipedia.org/wiki/Landauer's_principle
[szilard]: https://en.wikipedia.org/wiki/Entropy_in_thermodynamics_and_information_theory#Szilard.27s_engine

That's pretty remarkable, if you ask me. Together with our construction from any
non-reversible program to a reversible one, it suggests we should be able to cut
down on our CPU power usage by a significant order of magnitudes.


## Commentary (on where to go from here)

An obvious limitation of what we've built here today is that it is first-order,
which is to say that functions are not a first class citizen. I can think of no
immediate problem with representing reversible functions in this manner. We'd
need to move our `(<=>)` directly into the language.

`id` would provide introduction of this type, and `(>>)` (transitivity) would
allow us to create useful values of the type. We'd also need a new axiom:

```haskell
apply :: a * (a <=> b) <=> b * (b <=> a)
```

which would allow us to use our functions. We should also expect the following
theorems (which may or may not be axioms) due to our iso language forming a
cartesian closed category:

```haskell
product   :: (a <=> (b * c)) <=> (a <=> b) * (a <=> c)
```

Things that we'd expect to be theorems but are **not** are:

```haskell
terminal :: U <=> (a <=> U)
select   :: a <=> (U <=> a)
coproduct :: (a <=> (b + c)) <=> (a <=> b) + (a <=> c)
```

due to the symmetry of `(<=>)`, both of these are equivalent to `create` and
`erase`. I think the fact that these are not theorems despite `U` being the
terminal object is that `(<=>)` requires arrows in both directions, but `U` only
has incoming arrows.

