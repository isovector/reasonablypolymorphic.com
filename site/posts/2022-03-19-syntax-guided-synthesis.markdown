---
layout: post
title: "Review: Syntax-Guided Synthesis"
date: 2022-03-19 22:39
comments: true
tags: synthesis, pl, alur, review, sketch
---

<!--
```
module blog.syntax-guided-synthesis where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (Dec; yes; no; _because_; ¬_; ofʸ; ofⁿ)
open import Data.Bool hiding (_≟_; _≤_; _≤?_)
open import Relation.Nullary.Negation
open import Data.List hiding (and; [_])
open import Function hiding (const)
open import Data.Maybe
```
-->

I was describing my idea from [last week][generic] to [automatically optimize
programs][idea] to Colin, who pointed me towards [Syntax-Guided Synthesis][paper]
by Alur et al.

[generic]: /blog/generic-parallel-fp
[idea]: /blog/generic-parallel-fp/#future-work
[paper]: https://sygus.org/assets/pdf/Journal_SyGuS.pdf

Syntax-Guided Synthesis is the idea that free-range program synthesis is really
hard, so instead, let's constrain the search space with a grammar of allowable
programs. We can then enumerate those possible programs, attempting to find one
that satisfies some constraints. The idea is quite straightforward when you see
it, but that's not to say it's unimpressive; the paper has lots of quantitative
results about exactly how well this approach does.

The idea is we want to find programs with type `I`{.Agda} `→` `O`{.Agda}, that
satisfy some `spec`{.Agda}ification. We'll do that by picking some
`Lang`{.Agda}uage of syntax, and trying to build our programs there.

All of this is sorta moot, because we assume we have some `oracle`{.Agda} which
can tell us if our program satisfies the `spec`{.Agda}. But the `oracle`{.Agda}
is probably some SMT solver, and is thus expensive to call, so we'd like to try
hard not to call it if possible.

Let's take an example, and say that we'd like to synthesize the `max` of two
`Nat`{.Agda}s. There are lots of ways of doing that! But we'd like to find a
function that satisfies the following:

```
data MaxSpec (f : ℕ × ℕ → ℕ) : ℕ × ℕ → Set where
  is-max : {x y : ℕ}
         → x ≤ f (x , y)
         → y ≤ f (x , y)
         → ((f (x , y) ≡ x) ⊎ (f (x , y) ≡ y))
         → MaxSpec f (x , y)
```

If we can successfully produce an element of `MaxSpec`{.Agda} `f`, we have a
proof that `f` is an implementation of `max`. Of course, actually producing such
a thing is rather tricky; it's equivalent to determining if `MaxSpec`{.Agda} `f`
is `Dec`{.Agda}idable  for the given input.

In the first three cases, we have some conflicting piece of information, so we
are unable to produce a `MaxSpec`{.Agda}:

```
decideMax : (f : ℕ × ℕ → ℕ) → (i : ℕ × ℕ) → Dec (MaxSpec f i)
decideMax f i@(x , y) with f i | inspect f i
... | o | [ fi≡o ] with x ≤? o | y ≤? o
... | no ¬x≤o | _ = no λ { (is-max x≤o _ _) →
        contradiction (≤-trans x≤o (≤-reflexive fi≡o)) ¬x≤o }
... | yes _ | no ¬y≤o = no λ { (is-max x y≤o x₂) →
        contradiction (≤-trans y≤o (≤-reflexive fi≡o)) ¬y≤o }
... | yes x≤o | yes y≤o with o ≟ x | o ≟ y
... | no x≠o | no y≠o =
        no λ { (is-max x x₁ (inj₁ x₂)) →
                  contradiction (trans (sym fi≡o) x₂) x≠o
             ; (is-max x x₁ (inj₂ y)) →
                  contradiction (trans (sym fi≡o) y) y≠o
             }
```

Otherwise, we have a proof that `o` is equal to either `y` or `x`:

```
... | no proof | yes o≡y = yes
        (is-max (≤-trans x≤o (≤-reflexive (sym fi≡o)))
                (≤-trans y≤o (≤-reflexive (sym fi≡o)))
                (inj₂ (trans fi≡o o≡y)))
... | yes o≡x | _ = yes
        (is-max (≤-trans x≤o (≤-reflexive (sym fi≡o)))
                (≤-trans y≤o (≤-reflexive (sym fi≡o)))
                (inj₁ (trans fi≡o o≡x)))
```

`MaxSpec`{.Agda} is a proof that our function is an implementation of `max`, and
`decideMax`{.Agda} is a proof that "we'd know one if we saw one." So that's the
specification taken care of. The next step is to define the syntax we'd like to
guard our search.

The paper presents this syntax as a BNF grammar, but my thought is why use a
grammar when we could instead use a type system? Our syntax is a tiny little
branching calculus, capable of representing `Term`{.Agda}s and branching
`Cond`{.Agda}itionals:

```
mutual
  data Term : Set where
    var-x : Term
    var-y : Term
    const : ℕ → Term
    if-then-else : Cond → Term → Term → Term

  data Cond : Set where
    leq : Term → Term → Cond
    and : Cond → Cond → Cond
    invert : Cond → Cond
```

All that's left for our example is the ability to "compile" a `Term`{.Agda} down
to a candidate function. Just pattern match on the constructors and push the
inputs around until we're done:


```
mutual
  eval : Term → ℕ × ℕ → ℕ
  eval var-x (x , y) = x
  eval var-y (x , y) = y
  eval (const c) (x , y) = c
  eval (if-then-else c t f) i =
    if evalCond c i then eval t i else eval f i

  evalCond : Cond → ℕ × ℕ → Bool
  evalCond (leq m n) i   = Dec.does (eval m i ≤? eval n i)
  evalCond (and c1 c2) i = evalCond c1 i ∧ evalCond c2 i
  evalCond (invert c) i  = not (evalCond c i)
```

So that's most of the idea; we've specified what we're looking for, via
`MaxSpec`{.Agda}, what our syntax is, via `Term`{.Agda}, and a way of compiling
our syntax into functions, via `eval`{.Agda}. This is the gist of the technique;
the rest is just algorithms.

The paper presents several algorithms and evaluates their performances. But one
is clearly better than the others in the included benchmarks, so we'll just go
through that one.

Our algorithm to synthesize code corresponding to the specification takes a few
parameters. We've seen the first few:


```
module Solver
    {Lang I O : Set}
    (spec : (I → O) → I → Set)
    (decide : (f : I → O) → (i : I) → Dec (spec f i))
    (compile : Lang → I → O)
```

However, we also need a way of synthesizing terms in our `Lang`{.Agda}uage. For
that, we'll use `enumerate`{.Agda}, which maps a natural number to a term:

```
    (enumerate : ℕ → Lang)
```

Although it's not necessary for the algorithm, we should be able to implement
`exhaustive`{.Agda} over `enumerate`{.Agda}, which states every `Lang`{.Agda} is
eventually produced by `enumerate`{.Agda}:

```
    (exhaustive : (x : Lang) → Σ[ n ∈ ℕ ] (enumerate n ≡ x))
```

Finally, we need an `oracle`{.Agda} capable of telling us if our solution is
correct. This might sound a bit like cheating, but behind the scenes it's just a
magic SMT solver. The idea is that SMT can either confirm that our program is
correct, or produce a counterexample that violates the `spec`{.Agda}. The type
here is a bit crazy, so we'll take it one step at a time.

An `oracle`{.Agda} is a function that takes a `Lang`{.Agda}...

```
    (oracle
      : (exp : Lang)
```

and either gives back a function that can produce a `spec (compile exp)` for
every input:

```
      →   ((i : I) → spec (compile exp) i)
```

or gives back some input which is not a `spec (compile exp)`:

```
        ⊎ Σ[ i ∈ I ] ¬ spec (compile exp) i)
    where
```

The algorithm here is actually quite clever. The idea is that to try each
`enumerate`{.Agda}d value in order, attempting to minimize the number of calls
we make to the `oracle`{.Agda}, because they're expensive. So instead, well keep
a list of every counterexample we've seen so far, and ensure that our
synthesized function passes all of them before sending it off to the
`oracle`{.Agda}. First, we'll need a data structure to store our search
progress:

```
  record SearchState : Set where
    field
      iteration : ℕ
      cases : List I
  open SearchState
```

The initial search state is one in which we start at the beginning, and have no
counterexamples:

```
  start : SearchState
  iteration start = 0
  cases start = []
```

We can try a function by testing every counterexample:


```
  try : (I → O) → List I → Bool
  try f = all (Dec.does ∘ decide f)
```

and finally, can now attempt to synthesize some code. Our function
`check`{.Agda} takes a `SearchState`{.Agda}, and either gives back the next step
of the search, or some program, and a proof that it's what we're looking for.

```
  check
      : SearchState
      → SearchState
          ⊎ (Σ[ exp ∈ Lang ] ((i : I) → spec (compile exp) i))
  check ss
```

We begin by getting and compiling the next `enumerate`{.Agda}d term:

```
           with enumerate (iteration ss)
  ... | exp with compile exp
```

check if it passes all the previous counterexamples:

```
  ... | f with try f (cases ss)
```

if it doesn't, just fail with the next `iteration`{.Agda}:

```
  ... | false = inj₁ (record { iteration = suc (iteration ss)
                             ; cases = cases ss
                             })
```

Otherwise, our proposed function might just be the thing we're looking for, so
it's time to consult the `oracle`{.Agda}:

```
  ... | true with oracle exp
```

which either gives a counterexample that we need to record:

```
  ... | inj₂ (y , _) =
          inj₁ (record { iteration = suc (iteration ss)
                       ; cases = y ∷ cases ss
                       })
```

or it confirms that our function satisfies the specification, and thus that were
done:

```
  ... | inj₁ x = inj₂ (exp , x)
```

Pretty cool! The paper gives an optimization that caches the result of every
counterexample on every synthesized program, and reuses these whenever that
program appears as a subprogram of a larger one. The idea is that we can trade
storage so we only ever need to evaluate each subprogram once --- important for
expensive computations.

Of course, pumping `check`{.Agda} by hand is annoying, so we can instead package
it up as `solve`{.Agda} which takes a search depth, and iterates `check`{.Agda}
until it runs out of gas or gets the right answer:

```
  solve
      : ℕ
      → Maybe (Σ[ exp ∈ Lang ] ((i : I) → spec (compile exp) i))
  solve = go start
    where
      go
          : SearchState
          → ℕ
          → Maybe
              (Σ Lang (λ exp → (i : I) → spec (compile exp) i))
      go ss zero = nothing
      go ss (suc n) with check ss
      ... | inj₁ x = go ss n
      ... | inj₂ y = just y
```

