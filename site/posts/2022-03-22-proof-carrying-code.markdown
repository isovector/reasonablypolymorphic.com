---
layout: post
title: "Review: Proof-Carrying Code"
date: 2022-03-22 11:16
comments: true
tags: verification, pl, necula, review
---

<!--
```
module blog.proof-carrying-code where

open import Data.Nat
open import Data.Vec
open import Data.Fin
```
-->

A few months ago, the excellent [David Rusu][david] gave me an impromptu lecture
on [ring signatures][ringsigs], which are a way of signing something as an
anonymous member of a group. That is, you can show someone in the signing pool
was actually responsible for signing the thing, but can't determine *which
member of the pool actually signed it.* David walked me through all the math as
to how that actually happens, but I was unable to follow it, because the math
was hard and, perhaps more importantly, it felt like hand-compiling a proof.

[david]: https://davidrusu.github.io/
[ringsigs]: https://en.wikipedia.org/wiki/Ring_signature

What do I mean by "hand-compiling" a proof? Well, we have some mathematical
object, something like

```
postulate
  Identity : Set
  Message : Set
  SignedBy : Message → Identity → Set

  use-your-imagination : {A : Set} → A

record SignedMessage {n : ℕ} (pool : Vec Identity n) : Set where
  field
    message : Message
    @erased
      signer : Fin n
    signature : SignedBy message (lookup pool signer)
```

where `@erased` is Agda's [runtime irrelevance][irr] annotation, meaning the
`signer`{.Agda} field won't exist at runtime. In fact, attempting to write a
function that would extract it results in the following error:

[irr]: https://agda.readthedocs.io/en/v2.6.2.1/language/runtime-irrelevance.html#runtime-irrelevance

> Identifier `signer` is declared erased, so it cannot be used here \
> when checking that the expression `signer x` has type `Fin n`

Nice one Agda!

Hand-compiling this thing is thus constructing some object that has the desired
properties, but doing it in a way that requires BEING VERY SMART, and throwing
away any chance at composability in the process. For example, it'd be nice to
have the following:

```
open SignedMessage

weakenL : ∀ {n pool new-id}
        → SignedMessage {n} pool
        → SignedMessage (new-id ∷ pool)
weakenL x = use-your-imagination

weakenR : ∀ {n pool new-id}
        → SignedMessage {n} pool
        → SignedMessage (pool ++ [ new-id ])
weakenR x = use-your-imagination
```

which would allow us to arbitrarily extend the pool of a signed message. Then,
we could trivially construct one:

```
sign : Message → (who : Identity) → SignedMessage [ who ]
message   (sign msg who) = msg
signer    (sign msg who) = zero
signature (sign msg who) = use-your-imagination
```

and then obfuscate who signed by some random choice of subsequent
`weakenL`{.Agda}s and `weakenR`{.Agda}s.

Unfortunately, this is not the case with ring signatures. Ring signatures
require you to "bake in" the signing pool when you construct your signature, and
you can never again change that pool, short of doing all the work again. This
behavior is non-composable, and thus, in my reckoning, unlikely to be a true
solution to the problem.

The paper I chose to review this week is [Proof-Carrying Code][paper] by George
Necula, in an attempt to understand if the PL literature has anything to say
about this problem.

[paper]: https://www.cs.jhu.edu/~fabian/courses/CS600.624/proof-carrying-code.pdf

PCC is an old paper (from 1997, egads!) but it was the first thing I found on
the subject. I should really get better at vetting my literature before I go
through the effort of going through it, but hey, what are you going to do?

The idea behind PCC is that we want to execute some untrusted machine code. But
we don't want to sacrifice our system security to do it. And we don't want to
evaluate some safe language into machine code, because that would be too slow.
Instead, we'll send the machine code, as well as a safety proof that verifies
it's safe to execute this code. The safety proof is tied to the machine code,
such that you can't just generate a safety proof for an unrelated problem, and
then attach it to some malicious code. But the safety proof isn't obfuscated or
anything; the claim is that if you can construct a safety proof for a given
program, that program is necessarily safe to run.

On the runtime side, there is a simple algorithm for checking the safety proof,
and it is independent of the arguments that the program is run with; therefore,
we can get away with checking code once and evaluating it many times. It's
important that the algorithm be simple, because it's a necessarily trusted piece
of code, and it would be bad news if it were to have bugs.

PCC's approach is a bit... unimaginative. For every opcode we'd like to allow in
the programs, we attach a safety precondition, and a postcondition. Then, we map
the vector of opcodes we'd like to run into its pre/post conditions, and make
sure they are confluent. If they are, we're good to go. This vector of
conditions is called the vector VC in the paper.

So, the compiler computes the VC and attaches it to the code. Think of the VC as
a proposition of safety (that is, a type), and a proof of that proposition (the
VC itself.) In order to validate this, the runtime does a safety typecheck,
figuring out what the proposition of safety would have to be. It compares this
against the attached proof, and if they match, it typechecks the VC to ensure it
has the type it says. If it does, our code is safe.

The PCC paper is a bit light on details here, so it's worth thinking about
exactly what's going on here. Presumably determining the safety preconditions is
an easy problem if we can do it at runtime, but proving some code satisfies it
is hard, *or else we could just do that at runtime too.*

I'm a bit hesitant to dive into the details here, because I don't really care
about determining whether some blob of machine code is safe to run. It's a big
ball of poorly typed typing judgments about memory usage. Why do I say poorly
typed? Well consider one of the rules from the paper:

$$
\frac{m \vdash e : \tau \text{list} \quad \quad e \neq 0}
     {m \vdash e : \text{addr} \wedge \ldots}
$$

Here we have that from `e : List τ` (and that `e` isn't 0) we can derive `e :
addr`. At best, if we are charitable in assuming $e \neq 0$ means that `e` isn't
`nil`, there is a type preservation error here. If we are less charitable, there
is also some awful type error here involving 0, which might be a null check or
something? This seems sufficiently messy that I don't care enough to decipher
it.

How applicable is any of this to our original question around ring signatures?
Not very, I think, unfortunately. We already have the ring signature math if
we'd like to encode a proof, and the verification of it is easy enough. But it's
still not very composable, and I doubt this paper will add much there. Some more
promising approaches would be to draw the mystery commutative diagrams ala
[Adders and Arrows][adders], starting from a specification and deriving a chain
of proofs that the eventual implementation satisfies the specification. The
value there is in all the intermediary nodes of the commutative diagram, and
whether we can prove weakening lemmas there.

[adders]: /blog/adders-and-arrows

But PCC isn't entirely a loss; I learned about `@erased` in Agda.

