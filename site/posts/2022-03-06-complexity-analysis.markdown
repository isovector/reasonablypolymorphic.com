---
layout: post
title: "Review: Lightweight Semiformal Time Complexity Analysis for Purely Functional Data Structures"
date: 2022-03-06 15:37
comments: true
tags: danielsson, asymptotics, complexity, agda
---

What a mouthful of a title! [LWTCAfPFDS][paper] is our paper for the week,
written by Nils Anders Danielsson. At a high level, the idea is to introduce a
graded monad which counts computation steps, whose bind adds those steps
together. By constructing our program in this monad, we can use the type-system
to track its runtime asymptotics.

[paper]: https://www.cse.chalmers.se/~nad/publications/danielsson-popl2008.pdf


## Core Definitions

We might as well dive in. Since all of this complexity analysis stuff shouldn't
*change* anything at runtime, we really only need to stick the analysis in the
types, and can erase it all at runtime.

The paper thus presents its main tools in an `abstract` block, which is a new
Agda feature for me. And wow, does Agda ever feel like it's Haskell but from the
future. An `abstract` block lets us give some definitions, which *inside* the
`abstract` block can be normalized. But outside the block, they are opaque
symbols that are just what they are. This is a delightful contrast to Haskell,
where we need to play a game of making a new module, and carefully not exporting
things in order to get the same behavior. And even then, in Haskell, we can't
give opaque `type` synonyms or anything like that.

Anyway, the main type in the paper is `Thunk`{.Agda}, which tracks how many
computation steps are necessary to produce an eventual value:

<!--
```
{-# OPTIONS --rewriting #-}

module blog.complexity-analysis where

open import Function
open import Data.Nat
open import Data.Nat.Properties
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality as Eq

open Eq

private variable
  a b : Set
  m n : ℕ
```
-->

```
abstract
  Thunk : ℕ → Set → Set
  Thunk n a = a
```

Because none of this exists at runtime, we can just ignore the `n` argument, and
use the `abstract`ion barrier to ensure nobody can use this fact in anger.
`Thunk`{.Agda} is a *graded* monad, that is, a monad parameterized by a monoid,
which uses `mempty` for `pure`, and `mappend` for binding. We can show that
`Thunk`{.Agda} does form a graded monad:

```
  pure : a → Thunk 0 a
  pure x = x

  infixl 1 _>>=_
  _>>=_ : Thunk m a → (a → Thunk n b) → Thunk (m + n) b
  x >>= f = f x

  infixr 1 _=<<_
  _=<<_ : (a → Thunk n b) → Thunk m a → Thunk (m + n) b
  f =<< x = f x
```

We'll omit the proofs that `Thunk`{.Agda} really is a monad, but it's not hard
to see; `Thunk`{.Agda} is truly just the identity monad.

`Thunk`{.Agda} is also equipped with two further operations; the ability to mark
a computation cycle, and the ability to extract the underlying value by throwing
away the complexity analysis:

```
  infixr 0 !_
  !_ : Thunk n a → Thunk (suc n) a
  !_ a = a

  force : {a : Set} → Thunk n a → a
  force x = x
```

Here, `!_`{.Agda} is given a low, right-spanning precedence, which means it's
relatively painless to annotate with:

```
_ : Thunk 3 ℕ
_ = ! ! ! pure 0
```


## Conventions

Our definitions are "opt-in," in the sense that the compiler won't yell at you
if you forget to call `!_`{.Agda} somewhere a computational step happens. Thus,
we require users to follow the following conventions:

1. Every function body must begin with a call to `!_`{.Agda}.
2. `force`{.Agda} may not be used in a function body.
3. None of `pure`{.Agda}, `_>>=_`{.Agda} nor `!_`{.Agda} may be called partially
   applied.

The first convention ensures we count everything that should be counted. The
second ensures we don't cheat by discarding complexity information before it's
been counted. And the third ensures we don't accidentally introduce uncounted
computation steps.

The first two are pretty obvious, but the third is a little subtler. Under the
hood, partial application gets turned into a lambda, which introduces a
computation step to evaluate. But that step won't be ticked via `!_`{.Agda}, so
we will have lost the bijection between our programs and their analyses.


## Lazy Data Types

The paper shows us how to define a lazy vector. `VecL`{.Agda} `a c n` is a
vector of `n` elements of type `a`, where the cost of forcing each subsequent
tail is `c`:

```
{-# NO_POSITIVITY_CHECK #-}
data VecL (a : Set) (c : ℕ) : ℕ → Set where
  [] : VecL a c 0
  _∷_ : a → Thunk c (VecL a c n) → VecL a c (suc n)

infixr 5 _∷_
```

Let's try to write `fmap`{.Agda}  for `VecL`{.Agda}. We're going to need a
helper function, which delays a computation by artificially inflating its number
of steps:

```
abstract
  wait : {n : ℕ} → Thunk m a → Thunk (n + m) a
  wait m = m
```

(the paper follows its own rules and ensures that we call `!_`{.Agda} every
time we `wait`{.Agda}, thus it comes with an extra `suc`{.Agda} in the type of
`wait`{.Agda}. It gets confusing, so we'll use this version instead.)

Unfortunately, the paper also plays fast and loose with its math. It's fine,
because the math is right, but the code presented in the paper doesn't typecheck
in Agda. As a workaround, we need to enable rewriting:

```
open import Agda.Builtin.Equality.Rewrite
{-# REWRITE +-suc +-identityʳ #-}
```

We'll also need to be able to lift equalities over the `Thunk` time bounds:

```
cast : m ≡ n → Thunk m a → Thunk n a
cast eq x rewrite eq = x
```

Finally, we can write `fmap`{.Agda}:

```
fmap
  : {c fc : ℕ}
  → (a → Thunk fc b)
  → VecL a c n
  → Thunk (2 + fc) (VecL b (2 + fc + c) n)
fmap f [] = wait (pure [])
fmap {c = c} f (x ∷ xs)
          = ! f x
  >>= \x' → ! pure (x' ∷ cast (+-comm c _) (xs >>= fmap f))
```

This took me about an hour to write; I'm not convinced the approach here is as
"lightweight" as claimed. Of particular challenge was figuring out the actual
time bounds on this thing. The problem is that we usually reason about
asymptotics via Big-O notation, which ignores all of these constant factors.
What would be nicer is the hypothetical type:

```haskell
fmap
  : {c fc : ℕ}
  → (a → Thunk (O fc) b)
  → VecL a c n
  → Thunk (O c) (VecL b (O (fc + c)) n)
```

where every thunk is now parameterized by `O x` saying our asymptotics are
bounded by `x`. We'll see about fleshing this idea out later. For now, we can
power through on the paper, and write vector insertion. Let's assume we have a
constant time comparison function for `a`{.Agda}:

```
postulate
  _<=_ : a → a → Thunk 1 Bool
```

First things first, we need another waiting function to inflate the times on
every tail:

```
waitL
    : {c' : ℕ} {c : ℕ}
    → VecL a c' n
    → Thunk 1 (VecL a (2 + c + c') n)
waitL [] = ! pure []
waitL (x ∷ xs) = ! pure (x ∷ wait (waitL =<< xs))
```

and a helper version of `if_then_else_`{.Agda} which accounts in `Thunk`{.Agda}:

```
if_then_else_ : Bool → a → a → Thunk 1 a
if false then t else f = ! pure f
if true  then t else f = ! pure t
infixr 2 if_then_else_
```

we can thus write vector insertion:

```
insert
    : {c : ℕ}
    → a
    → VecL a c n
    → Thunk 4 (VecL a (4 + c) (suc n))
insert x [] = wait (pure (x ∷ wait (pure [])))
insert x (y ∷ ys)
         = ! x <= y
  >>= \b → ! if b then x ∷ wait (waitL (y ∷ ys))
                  else y ∷ (insert x =<< ys)
```

The obvious followup to `insert`{.Agda} is insertion `sort`{.Agda}:

```
open import Data.Vec using (Vec; []; _∷_; tail)

sort : Vec a n → Thunk (1 + 5 * n) (VecL a (4 * n) n)
sort [] = ! pure []
sort (x ∷ xs) = ! insert x =<< sort xs
```

This thing looks linear, but insertion sort is $O(n^2)$, so what gives? The
thing to notice is that the cost of each *tail* is linear, but we have $O(n)$
tails, so forcing the whole thing indeed works out to $O(n^2)$. We can now show
`head`{.Agda} runs in constant time:

```
head : {c : ℕ} → VecL a c (suc n) → Thunk 1 a
head (x ∷ _) = ! pure x
```

and that we can find the `minimum`{.Agda}  element in linear time:

```
minimum : Vec a (suc n) → Thunk (8 + 5 * n) a
minimum xs = ! head =<< sort xs
```

Interestingly, Agda can figure out the bounds on `minimum`{.Agda}  by itself,
but not any of our other functions.

The paper goes on to show that we can define `last`{.Agda}, and then get a
quadratic-time `maximum` using it:

```
last : {c : ℕ} → VecL a c (suc n) → Thunk (1 + suc n * suc c) a
last (x ∷ xs) = ! last' x =<< xs
  where
    last' : {c : ℕ} → a → VecL a c n → Thunk (1 + n * suc c) a
    last' a [] = ! pure a
    last' _ (x ∷ xs) = ! last' x =<< xs
```

Trying to define `maximum` makes Agda spin, probably because of one of my
rewrite rules. But here's what it should be:

```haskell
maximum : Vec a (suc n) → Thunk (13 + 14 * n + 4 * n ^ 2) a
maximum xs = ! last =<< sort xs
```

The paper goes on to say some thinks about partially evaluating thunks, and then
shows its use to measure some popular libraries. But I'm more interested in
making the experience better.


## Extra-curricular Big O

Clearly this is all too much work. When we do complexity analysis by hand, we
are primarily concerned with *complexity classes,* not exact numbers of steps.
How hard would it be to generalize all of this so that `Thunk` takes a function
bounding the runtime necessary to produce its value?

First, a quick refresher on what big-O means. A function $f : \mathbb{N} \to
\mathbb{N}$ is said to be in $O(g)$ for some $g : \mathbb{N} \to \mathbb{N}$
iff:

$$
\exists (C k : \mathbb{N}). \forall (n : \mathbb{N}, k \leq n). f(n) \leq C \cdot g(n)
$$

That is, there is some point $k$ at which $g(n)$ stays above $f(n)$. This is the
formal definition, but in practice we usually play rather fast and loose with
our notation. For example, we say "quicksort is $O(n\cdot\log{n})$ in the
length of the list", or "$O(n\cdot\log{m})$ , where $m$ is the size of the first
argument."

We need to do a bit of elaboration here to turn these informal statements into
a formal claim. In both cases, there should are implicit binders inside the
$O(-)$, binding $n$ in the first, and $m, n$ in the second. These functions
then get instantiated with the actual sizes of the lists. It's a subtle point,
but it needs to be kept in mind.

The other question is how the hell do we generalize that definition to multiple
variables? Easy! We replace $n : \mathbb{N}, k \leq n$ with a vector of natural
numbers, subject to the constraint that they're *all* bigger than $k$.

OK, let's write some code. We can give the definition of `O`{.Agda}:

```
open import Data.Vec.Relation.Unary.All
    using (All; _∷_; [])
    renaming (tail to tailAll)

record O {vars : ℕ} (g : Vec ℕ vars  → ℕ) : Set where
  field
    f : Vec ℕ vars → ℕ
    C : ℕ
    k : ℕ
    def : (n : Vec ℕ vars) → All (k ≤_) n → f n ≤ C * g n
```

The generality of `O`{.Agda} is a bit annoying for the common case of being a
function over one variable, so we can introduce a helper function `O'`{.Agda}:

```
hoist : {a b : Set} → (a → b) → Vec a 1 → b
hoist f (x ∷ []) = f x

O' : (ℕ → ℕ) → Set
O' f = O (hoist f)
```

We can trivially lift any function `f` into `O`{.Agda} `f`:

```
O-build : {vars : ℕ} → (f : Vec ℕ vars → ℕ) → O f
O-build f .O.f = f
O-build f .O.C = 1
O-build f .O.k = 0
O-build f .O.def n x = ≤-refl
```

and also trivially weaken an `O`{.Agda} into using more variables:

```
O-weaken : ∀ {vars} {f : Vec ℕ vars → ℕ} → O f → O (f ∘ tail)
O-weaken o .O.f = o .O.f ∘ tail
O-weaken o .O.C = o .O.C
O-weaken o .O.k = o .O.k
O-weaken o .O.def (_ ∷ x) (_ ∷ eq) = o .O.def x eq
```

More interestingly, we can lift a given `O'`{.Agda} into a higher power,
witnessing the fact that eg, something of $O(n^2)$ is also $O(n^3)$:

```
O-^-suc : {n : ℕ} → O' (_^ n) → O' (_^ suc n)
O-^-suc o .O.f = o .O.f
O-^-suc o .O.C = o .O.C
O-^-suc o .O.k = suc (o .O.k)
O-^-suc {n} o .O.def xs@(x ∷ []) ps@(s≤s px ∷ []) =
  begin
    f xs               ≤⟨ def xs (≤-step px ∷ []) ⟩
    C * (x ^ n)        ≤⟨ *-monoˡ-≤ (x ^ n) (m≤m*n C (s≤s z≤n)) ⟩
    (C * x) * (x ^ n)  ≡⟨ *-assoc C x (x ^ n) ⟩
    C * (x * (x ^ n))
  ∎
  where
    open O o
    open ≤-Reasoning
```

However, the challenge is and has always been to simplify the construction of
`Thunk`{.Agda} bounds. Thus, we'd like the ability to remove low-order terms
from `O`{.Agda}s. We can do this by eliminating $n^k$ whenever there is a
$n^{k'}$ term around with $k \leq k'$:

```
postulate
  O-drop-low
    : {z x y k k' : ℕ}
    → k ≤ k'
    → O' (\n → z + x * n ^ k + y * n ^ k')
    → O' (\n → z + n ^ k')
```

The `z` variable here lets us compose `O-drop-low`{.Agda} terms, by subsequently
instantiating

As a special case, we can eliminate constant terms via `O-drop-low`{.Agda} by
first expanding constant terms to be coefficients of $n^0$:

```
O-drop-1
  : {x y k : ℕ}
  → O' (\n → x + y * n ^ k)
  → O' (\n → n ^ k)
O-drop-1 {x} {y} {k} o rewrite sym (*-identityʳ x) =
  O-drop-low {0} {x} {y} {k = 0} {k} z≤n o
```

With these functions, we can now easily construct `O'`{.Agda} values for
arbitrary one-variable functions:

```
_ : O' (_^ 1)
_ = O-drop-1 {4} {5} {1} $ O-build $ hoist \n → 4 + 5 * n ^ 1

_ : O' (_^ 2)
_ = O-drop-1 {4} {1} {2}
  $ O-drop-low {4} {5} {3} {1} {2} (s≤s z≤n)
  $ O-build $ hoist \n → 4 + 5 * n ^ 1 + 3 * n ^ 2
```

Finally, we just need to build a version of `Thunk`{.Agda} that is adequately
lifted over the same functions we use for `O`{.Agda}:

```
abstract
  OThunk : {vars : ℕ} → (Vec ℕ vars → ℕ) → Set → Set
  OThunk _ a = a

  OThunk' : (ℕ → ℕ) → Set → Set
  OThunk' f = OThunk (hoist f)
```

The `limit`{.Agda} function can be used to lift a `Thunk`{.Agda} into an
`OThunk`{.Agda}:

```
  limit
    : {vars : ℕ} {f : Vec ℕ vars → ℕ} {a : Set}
    → (v : Vec ℕ vars)
    → (o : O f)
    → Thunk (o .O.f v) a → OThunk f a
  limit _ _ x = x
```

and we can now give an asymptotic bound over `sort`{.Agda}:

```haskell
o2 : O' (_^ 1)
o2 = O-drop-1 {1} {5} {1} $ O-build $ hoist \n -> 1 + 5 * n

linearHeadSort : Vec a n → OThunk' (_^ 1) (VecL a (4 * n) n)
linearHeadSort {n = n} v = limit (n ∷ []) o2 $ sort v
```


## Conclusions

I'm traveling right now, and ran out of internet on publication day, which means
I don't have a copy of the paper in front of me as I write this (foolish!)
Overall, the paper is slightly interesting, though I don't think there's
anything especially novel here. Sticking the runtime behavior into the type is
pretty much babby's first example of graded monads, and we don't even get
asymptotics out of it! Instead we need to push big polynomials around, and
explicitly call `wait`{.Agda} to make different branches work out.

The `O`{.Agda} stuff I've presented here alleviates a few of those problems; as
it allows us to relatively-easily throw away the polynomials and just work with
the highest order terms. A probably better approach would be to throw away the
functions, and use a canonical normalizing-form to express the asymptotes. Then
we could define a $\lub$ operator over `OThunk`{.Agda}s, and define:

```haskell
_>>=_ : OThunk f a → (a → OThunk g b) → OThunk (f ⊔ g) b
```

to let us work compositionally in the land of big O.

My biggest takeaway here is that the techniques described in this paper are
probably not powerful enough to be used in anger. Or, at least, not if you
actually want to get any work done. Between the monads, polynomials, and
waiting, the experience could use a lot of TLC.

