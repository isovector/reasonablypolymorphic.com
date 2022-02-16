---
layout: post
title: "Automatic Ring Solving"
date: 2022-02-16 12:33
comments: true
tags: kidney, ring solving, agda, review
---

Today's sorta-review is of [Automatically and Efficiently Illustrating
Polynomial Equations in Agda][paper] by [Donnacha Oisin Kidney][kidney]. I say
it's sorta a review because I had to write some annoying proofs recently, and
discovered that Agda has a ring solver that automates annoying proofs. For
example, it can solve things like `(a + b) * (a + b) = a^2 + 2*a*b + b^2`, which
is rather amazing if you think about it. I got curious about how this is
possible, and came across AaEIPEiA, quickly skimmed it for the rough approach,
and then decided to write my own ring solver. As a result, this post is
certainly inspired by AaEIPiA, but my implementation is extremely naive compared
to the one presented in the paper. Kidney's paper is very good, and I apologize
for not doing it justice here.

[paper]: https://github.com/oisdk/agda-ring-solver-report/blob/master/report.pdf
[kidney]: https://doisinkidney.com/

So, some background. Agda lets you write types that correspond to equalities,
and values of those types are proofs of those equalities. For example, we can
write the following type:

```agda
(x : ℕ) → (x + 1) * (x + 1) ≡ (x * x) + (1 + 1) * x + 1
```

You probably wouldn't write this for its own sake, but it might come up as a
lemma of something else you're trying to prove. However, actually proving this
equality is a huge amount of busywork, that takes forever, and isn't actually
interesting because we all know that this equality holds. For example, the proof
might look something like this:

```agda
  begin
    (x + 1) * (x + 1)
  ≡⟨ *-+-distrib (x + 1) x 1 ⟩
    (x + 1) * x + (x + 1) * 1
  ≡⟨ cong (\φ -> ((x + 1) * x + φ)) $ *-1-id-r (x + 1) ⟩
    (x + 1) * x + (x + 1)
  ≡⟨ cong (\φ -> φ + (x + 1)) $ *-comm (x + 1) x ⟩
    x * (x + 1) + (x + 1)
  ≡⟨ cong (\φ -> φ + (x + 1)) $ *-+-distrib x x 1 ⟩
    (x * x + x * 1) + (x + 1)
  ≡⟨ ? ⟩
    -- kill me
  ≡⟨ ? ⟩
    (x * x) + (1 + 1) * x + 1
  ∎
```

It's SO MUCH WORK to do _nothing!_ This is not an interesting proof! A ring
solver lets us reduce the above proof to:

```agda
  begin
    (x + 1) * (x + 1)
  ≡⟨ solve ⟩
    (x * x) + (1 + 1) * x + 1
  ∎
```

or, even more tersely:

```agda
  solve
```

So that's the goal here. Automate stupid, boring proofs so that we as humans can
focus on the interesting bits of the problem.

## I Don't Even Know What a Ring Is

Why is this called a ring solver? I don't exactly know, but a ring is some math
thing. My guess is that it's the abstract version of an algebra containing
addition and multiplication, with all the usual rules.

And looking at it, sure enough! A ring is a set with two monoids on it, one
corresponding to addition, and the other to multiplication. Importantly, we
require that multiplication distributes over addition.

Rings technically have additive inverses, but I didn't end up implementing (or
needing them.) However, I did require commutativity of both addition and
multiplication --- more on this later.

The ring laws mean that algebra works in the way we expect arithmetic to work.
We can shuffle things around, and probably all have enough experience solving
these sorts of problems with pen and paper. But what's the actual algorithm
here?


## How Do You Solve A Ring?

At first blush, this sounds like a hard problem! It feels like we need to see if
there's a way to turn some arbitrary expression into some other arbitrary
expression. And that is indeed true, but it's made easier when you realize that
polynomials have a normal form as a sum of products of descending powers. For
example, this is in normal form:

```
5*x^2 - 3*x + 0
```

The problem thus simplifies to determining if two expressions have the same
normal form. Thus, we can construct a proof that each expression is equal to
its normal form, and then compose those proofs together to show the unnormalized
forms are equal.

My implementation is naive, and only works for expressions with a single
variable, but I think the approach generalizes if you can find a suitable normal
form for multiple variables.

All of this sounds like a good tack, but the hard part is convincing ourselves
(and perhaps more importantly, Agda,) that the stated relationship holds. As it
happens, we require three equivalent types:

* `A`, the ring we're actually trying to solve
* `Poly`, a syntactic representation of the ring operations
* `Horner`, the type of `A`-normal forms

`Poly` and `Horner` are indexed by `A`, but I've left that out for presentation
purposes. Furthermore, they're also both indexed by the degree of the
polynomial, that is, the biggest power they contain. I'm not sure this was
necessary, but it helped me make sure my math was right when I was figuring out
how to multiply `Horner`s.

At a high level, solving a ring equality is really a statement about how `A` is
related to `Poly` and `Horner`. We can construct an A-expression by substituting
an `A` for all the variables in a `Poly`:

```agda
construct : {n : ℕ} → Poly n → A → A
```

and we can normalize any syntactic expression:

```agda
normalize : {n : ℕ} → Poly n → Horner n
```

thus we can solve a ring equation by hoisting a proof of equality of its normal
forms into a proof of equality of its construction:

```agda
solve
    : {n : ℕ}
    → (x y : Poly n)
    → normalize x ≡ normalize y
    → (a : A)
    → construct x a ≡ construct y a
```

This approach is a bit underwhelming, since we need to explicitly construct
syntactic objects (in `Poly`) corresponding to the expressions we're trying to
solve (in `A`). But this is something we can solve with Agda's macro system, by
creating the `Poly`s by inspecting the actual AST, so we'll consider the
approach good enough. Today's post is about understanding how to do ring
solving, not about how to engineer a nice user-facing interface.

The actual implementation of `solve` is entirely straight-forward:


```agda
solve x y eq a =
  begin
    construct x a             ≡⟨ construct-is-normal x a ⟩
    evaluate (normalize x) a  ≡⟨ cong (\φ → evaluate φ a) eq ⟩
    evaluate (normalize y) a  ≡⟨ sym $ construct-is-normal y a ⟩
    construct y a
  ∎
```

given a lemma that `construct` is equal to evaluating the normal form:


```agda
construct-is-normal
    : {N : ℕ}
    → (x : Poly N)
    → (a : A)
    → construct x a ≡ evaluate (normalize x) a
```

The implementation of this is pretty straightforward too, requiring only that we
have `+` and `*` homomorphisms between `Horner` and `A`:

```agda
+A-+H-homo
    : ∀ {m n} j k a
    → evaluate {m} j a +A evaluate {n} k a ≡ evaluate (j +H k) a

*A-*H-homo
    : ∀ {m n} j k a
    → evaluate {m} j a *A evaluate {n} k a ≡ evaluate (j *H k) a
```

These two lemmas turn out to be the hard part.


## But First, Types

Before we get into all of that, let's first discuss what each of the types looks
like. We have `Poly`, which again, is an initial encoding of the ring algebra:

```agda
data Poly : ℕ → Set where
  con : A → Poly 0
  var : Poly 1
  _:+_ : {m n : ℕ} → Poly m → Poly n → Poly (m ⊔ n)
  _:*_ : {m n : ℕ} → Poly m → Poly n → Poly (m + n)
```

We can reify the meaning of `Poly` by giving a transformation into `A`:

```agda
construct : {N : ℕ} → Poly N → A → A
construct (con x) a = x
construct var a = a
construct (p :+ p2) a = construct p a +A construct p2 a
construct (p :* p2) a = construct p a *A construct p2 a
```

Our other core type is `Horner`, which is an encoding of the Horner normal form
of a polynomial:

```agda
data Horner : ℕ → Set where
  PC : A → Horner 0
  PX : {n : ℕ} → A → Horner n → Horner (suc n)
```

`Horner` requires some discussion. Horner normal form isn't the same normal form
presented earlier, instead, it's a chain of linear multiplications. For example,
we earlier saw this:

```
5*x^2 - 3*x + 0
```

in Horner normal form, this would be written as

```
0 + x * (3 + x * 5)
```

The idea is we can write any polynomial inductively by nesting the bigger terms
as sums inside of multiplications against `x`. We can encode the above as a
`Horner` like this:

```agda
PX 0 (PX 3 (PC 5))
```

and then reify the meaning of `Horner` with respect to `A` via `evaluate`:

```agda
evaluate : {n : ℕ} → Horner n → A → A
evaluate (PC x) v = x
evaluate (PX x xs) v = x +A (v *A evaluate xs v)
```


## Operations on Horners

We can define addition over `Horner` terms, which is essentially `zipWith (+A)`:

```agda
_+H_ : {m n : ℕ} → Horner m → Horner n → Horner (m ⊔ n)
_+H_ (PC x)    (PC y)    = PC (x +A y)
_+H_ (PC x)    (PX y ys) = PX (x +A y) ys
_+H_ (PX x xs) (PC y)    = PX (x +A y) xs
_+H_ (PX x xs) (PX y ys) = PX (x +A y) (xs +H ys)
```

We can also implement scalar transformations over `Horner`, which is exactly a
monomorphic `fmap`:

```agda
scalMapHorner : {m : ℕ} → (A → A) → Horner m → Horner m
scalMapHorner f (PC x) = PC (f x)
scalMapHorner f (PX x xs) = PX (f x) (scalMapHorner f xs)
```

and finally, we can define multiplication over `Horner` terms:

```agda
_*H_ : {m n : ℕ} → Horner m → Horner n → Horner (m + n)
_*H_ (PC x) y = scalMapHorner (x *A_) y
_*H_ (PX {m} x xs) (PC y) = scalMapHorner (_*A y) (PX x xs)
_*H_ (PX {m} x xs) yy =
  scalMapHorner (x *A_) yy +H PX #0 (xs *H yy)
```

The first two cases here are straightforward, just `scalMapHorner`-multiply in
the constant value and go on your way. The `PX-PX` case is rather complicated
however, but corresponds to the `*-+-distrib` law:

```
*-+-distrib : ∀ x xs yy → (x + xs) * yy ≡ x * yy +A xs * yy
```

We take advantage of the fact that we know `x` is a scalar, by immediately
multiplying it in via `scalMapHorner`.


## Tying it All Together

As alluded to earlier, all that's left is to show `evaluate`-homomorphisms
for `+H`/`+A` and `*H`/`*A`:

```agda
+A-+H-homo
    : ∀ {m n} j k a
    → evaluate {m} j a +A evaluate {n} k a ≡ evaluate (j +H k) a

*A-*H-homo
    : ∀ {m n} j k a
    → evaluate {m} j a *A evaluate {n} k a ≡ evaluate (j *H k) a
```

There's nothing interesting in these proofs, it's just three hundred ironic
lines of tedious, boring proofs, of the sort that we are trying to automate
away.

Given these, we can implement `construct-is-normal`

```agda
construct-is-normal
    : {N : ℕ}
    → (x : Poly N)
    → (a : A)
    → construct x a ≡ evaluate (normalize x) a
construct-is-normal (con x) a = refl
construct-is-normal var a = refl
construct-is-normal (x :+ y) a
  rewrite construct-is-normal x a
        | construct-is-normal y a
        | +A-+H-homo (normalize x) (normalize y) a
        = refl
construct-is-normal (x :* y) a
  rewrite construct-is-normal x a
        | construct-is-normal y a
        | *A-*H-homo (normalize x) (normalize y) a
        = refl
```

Nice!

The homomorphism proofs are left as an exercise to the reader, or you can go
look at the [code][code] if you want to skip doing it.

[code]: https://github.com/isovector/reviews/blob/master/agda-src/RingSolving.agda


## Agda Woes

My implementation isn't 100% complete, I still need to prove that `*H` is
commutative:

```agda
*H-comm : ∀ j k → j *H k ≡ k *H j
```

which shouldn't be hard, because it _is_ commutative. Unfortunately, Agda has
gone into hysterics, and won't even typecheck the type of `*H-comm`, because it
can't figure out that `m + n = n + m` (the implicit indices on the result of
`*H`). As far as I can tell, there is no easy fix here; there's some weird
`cong`-like thing for types called `subst`, but it seems to infect a program and
push these weird-ass constraints everywhere.

This is extremely frustrating, because it's literally the last thing to prove
after 300 grueling lines of proof. And it's also true and isn't even hard to
show. It's just that I can't get Agda to accept the type of the proof because
it's an idiot that doesn't know about additive commutativity. After a few hours
of fighting with getting this thing to typecheck, I just said fuck it and
postulated `*H-comm`.

Stupid Agda.

If you know what I've done wrong to deserve this sort of hell, please let me
know. It would be nice to be able to avoid problems like this in the future, or
resolve them with great ease.


## Conclusion

So, that's it! Modulo a postulate, we've managed to implement a ring-solver by
showing the equivalence of three different representations of the same data.
Just to convince ourselves that it works:

```agda
test-a : Poly 2
test-a = (var :+ con #1) :* (var :+ con #1)

test-b : Poly 2
test-b = var :* var :+ two :* var :+ con #1
  where
    two = con #1 :+ con #1

success
    : (x : A)
    → (x +A #1) *A (x +A #1) ≡ (x *A x) +A (#1 +A #1) *A x +A #1
success x = solve test-a test-b refl x
```

which Agda happily accepts!

I don't exactly know offhand how to generalize this to multivariate polynomials,
but I think the trick is to just find a normal form for them.

As usual, the code for this post is [available on Github.][code]

