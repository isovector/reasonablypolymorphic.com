---
layout: post
title: "Review: A Very Elementary Introduction to Sheaves"
date: 2022-02-27 13:08
comments: true
tags: agrios, sheaves, math, reverse engineering, agda
---

```
{-# OPTIONS --type-in-type #-}

module posts.sheafs where

open import Data.Integer hiding (_<_)
open import Data.Integer.Properties using (*-zeroˡ; ≤-reflexive; ≤-trans)
open import Data.Vec hiding (restrict; reverse)
open import Categories
open import Category.LIN
open import Category.SET
open import Category.AGRP
open import Category.MyFunctor
import Relation.Binary.PropositionalEquality as Eq

open Eq using (_≡_; cong; sym; refl)
open LinMap
```

A while back I reviewed some paper (maybe codata? --- too lazy to check) and
came away thinking "I should learn more about presheaves." The first paper I
found is [A Very Elementary Introduction to Sheaves][paper] by Mark Agrios, and
mildly interestingly, was published less than three weeks ago.

[paper]: https://arxiv.org/pdf/2202.01379.pdf

The paper is called "very elementary," and in the first sentence states it "is a
very non-rigorous, loose, and extremely basic introduction to sheaves," and it
delivers on these promises. There is a section on metaphorically what a sheaf
is, and then two somewhat-worked examples.

After reading through the paper, I feel like I have a very rough idea of what a
sheaf is, and thought that this would be an excellent opportunity to flex my
category theory muscles. That is, can I correctly generalize from these two
examples to a solid category theoretical definition of a sheaf? I'm not sure,
but this is a unique opportunity, so it's worth a shot.


## The Metaphor

The central metaphor of the paper is that a sheaf enriches some mathematical
structure, much like a garden enriches a plot of dirt. There are lots of gardens
you could make on a plot of dirt, and then you can harvest things from them. I
guess this makes sense to the author, but it doesn't particularly help me. I
suspect this is an example of the monad tutorial fallacy in the wild: after
thinking really hard about an idea for a while, the author came up with a
metaphor that really works for them. But, this metaphor is more an artifact of
their thinking process than it is descriptive of the idea itself. Anyway, either
way, I wasn't able to extract much meaning here.


## Example: Graphs

We can build a (pre-?)sheaf over a graph. By playing fast and loose with our
types like mathematicians are so wont to do, we can model the edge $e_{ij} : V_i
\to V_j$ in a graph as an "intersection of the nodes it connects." The paper
writes $e_{ij} < v_i, v_j$. I'm not super sure what that means, but I think it's
saying that given some graph $G = (V, E)$, we can say $e_{ij} \subseteq v_i \cup
v_j$? Except that this doesn't typecheck, since `v_i` is an element of a set,
not a set itself. I don't know.

Anyway, the important thing here seems to be that there is a preorder between
edges and vertices. So let's quickly define a `Preorder`:


```
record Preorder : Set where
  field
    Carrier : Set
    _<_ : Carrier → Carrier → Set
    <-refl : (a : Carrier) → a < a
    <-trans : {a b c : Carrier} → a < b → b < c → a < c
```

and then just forget about the whole graph thing, because I am not convinced it
is a meaningful presentation. Instead, we'll cheat, and just build exactly the
object we want to discuss.

```
data Ex : Set where
  v1  : Ex
  v2  : Ex
  e12 : Ex
```

corresponding to this rather boring graph:

~~~{.quiver}
\[\begin{tikzcd}
  v1 && {} && v2
  \arrow["e12"', from=1-1, to=1-5]
\end{tikzcd}\]
~~~

We can then build a `Preorder`{.Agda} on `Ex`{.Agda} with explicit cases for
`e12`{.Agda} being less than its vertices:

```
data Ex< : Ex → Ex → Set where
  e12<v1 : Ex< e12 v1
  e12<v2 : Ex< e12 v2
```

and two cases to satisfy the preorder laws:

```
  ex<-refl : (x : Ex) → Ex< x x
```

and then mechanically hook everything up:

```
module _ where
  open Preorder
  ex-preorder : Preorder
  ex-preorder .Carrier = Ex
  ex-preorder ._<_ = Ex<
  ex-preorder .<-refl = ex<-refl
  ex-preorder .<-trans e12<v1 (ex<-refl .v1) = e12<v1
  ex-preorder .<-trans e12<v2 (ex<-refl .v2) = e12<v2
  ex-preorder .<-trans (ex<-refl _) e12<v1 = e12<v1
  ex-preorder .<-trans (ex<-refl _) e12<v2 = e12<v2
  ex-preorder .<-trans (ex<-refl x) (ex<-refl _) = ex<-refl x
```


The paper goes on to say we have some sheaf `F`, which maps `Ex`{.Agda}s to
"just about anything," this codomain being called the *stalk.* For now, let's
assume it's to `Set`{.Agda}.

Furthermore, the sheaf `F` also has a "second mechanism," which in our example
maps an edge $e_{ij} : v_i \to v_j$ to two functions:

$$
F_{v_i;e_{ij}} : F(v_i) \to F(e_{ij}) \\
F_{v_j;e_{ij}} : F(v_j) \to F(e_{ij})
$$

This is where some of the frustration in only being given examples comes in. Why
are these in the definition of a sheaf? The only thing that could possibly make
any sense to me is that this comes from a more general construction:

```text
restrict : (x y : Ex) → x < y → Stalk y → Stalk x
```

which states we have a mapping from $F(y)$ to $F(x)$ if and only if we have
$x < y$. These `restrict` things are called *restriction maps*.

What's further confusing is the following point:

> Since each stalk is a vector space, it is natural to have our restriction maps
> be linear transformations described by matrices.

Why linear transformations, and not just arbitrary functions? When I hear
"linear transformation" I think homomorphism, or more probably, morphism in some
category. Which then probably means the `Stalk` isn't a function to
`Set`{.Agda}, it's a mapping into a category.

OK, so that all seems straightforward enough. Let's try to formalize it.

```
module Sheaf (pre : Preorder) (C : Category) where
  open Preorder pre
  open Category C

  record Sheaf : Set where
    field
      Stalk : Carrier → Obj
      restrict : {x y : Carrier} → x < y → Stalk y ~> Stalk x
```

which seems reasonable. The paper now gives us a specific sheaf, with
`restrict`{.Agda} `e12<v1`{.Agda} being the linear map encoded by the matrix:

$$
\begin{bmatrix}
1 & -1 \\
0 & 2
\end{bmatrix}
$$

which we can write as a morphism in `LIN`{.Agda} (the category of linear
algebra, with objects as vector spaces, and morphisms as linear maps):

<!--
```
module _ where
  open Category LIN
  open Sheaf ex-preorder LIN
  open Sheaf.Sheaf

  postulate
    trustMe : ∀ {A : Set} {a b : A} → a ≡ b
    sorry : ∀ {A : Set} → A
```
-->

```
  e12~>v1 : 2 ~> 2
  e12~>v1 .linmap (x ∷ y ∷ []) =
    (x - y)   ∷
    (+ 2 * y) ∷
             []
  e12~>v1 .preserves-+ u v = trustMe
  e12~>v1 .preserves-* a v = trustMe
```

and `restrict`{.Agda} `e12<v2`{.Agda} being the linear map encoded by the
matrix:

$$
\begin{bmatrix}
3 & 1 & -1 \\
2 & 0 & 2
\end{bmatrix}
$$

written as:

```
  e12~>v2 : 3 ~> 2
  e12~>v2 .linmap (x ∷ y ∷ z ∷ []) =
    (+ 3 * x + y - z)   ∷
    (+ 2 * x + + 2 * z) ∷
                       []
  e12~>v2 .preserves-+ u v = trustMe
  e12~>v2 .preserves-* a v = trustMe
```

Thus, we can finally build the example `Sheaf`:

```
  ex : Sheaf
  ex .Stalk v1  = 2
  ex .Stalk v2  = 3
  ex .Stalk e12 = 2
  ex .restrict e12<v1 = e12~>v1
  ex .restrict e12<v2 = e12~>v2
  ex .restrict (ex<-refl z) = id
```

What's with the `Stalk`{.Agda} of `v1`{.Agda} being 2, you might ask? Remember,
the stalk is an object in some category, in this case `LIN`{.Agda}. Objects in
`LIN`{.Agda} are natural numbers, corresponding to the length of vectors.


### Sections and Global Sections

Here's where our categorical generalization of the paper goes a bit haywire. The
paper defines a *section* as picking an element from each `Stalk`{.Agda} of the
sheaf. He picks, for example:

$$
\begin{bmatrix}
2 \\ 1
\end{bmatrix}
\in \text{Stalk } v1
$$

$$
\begin{bmatrix}
3 \\ -1 \\ 0
\end{bmatrix}
\in \text{Stalk } v2
$$

and

$$
\begin{bmatrix}
1 \\ -1
\end{bmatrix}
\in \text{Stalk } e12
$$

which is all fine and dandy, except that when we categorize, our objects no
longer have internal structure. Fortunately, we can use "generalized elements,"
a.k.a., morphisms out of the `terminal`{.Agda} object.

<!--
```
module BadSections
         {pre : Preorder}
         {C : Category}
         (term : HasTerminal C)
         (sheaf : Sheaf.Sheaf pre C) where
  open HasTerminal term
  open Preorder pre
  open Sheaf.Sheaf sheaf
  open Category C
```
-->

```
  Section : Carrier → Set
  Section c = terminal ~> Stalk c
```

That is, a `Section`{.Agda} is a mapping from every element in the
`Preorder`{.Agda} to a generalized element of its `Stalk`{.Agda}. We can
evaluate a `Section`{.Agda} by checking the commutativity of all
`restrict`{.Agda}s. That is, we'd like the following diagram to commute:

~~~{.quiver}
\[\begin{tikzcd}
  && {0} \\
  \\
  {\text{Stalk } v_1} &&&& {\text{Stalk } e_{12}}
  \arrow["{\text{Section }v_1}"', from=1-3, to=3-1]
  \arrow["{\text{Section } e_{12}}", from=1-3, to=3-5]
  \arrow["{\text{restrict } e_{12}<v_1}"', from=3-1, to=3-5]
\end{tikzcd}\]
~~~

Doing this in Agda is hard because it wants lots of dumb arithmetic proofs, so
instead we'll make ourselves content with some by-hand math:

$$
r \circ S v1
=  \begin{bmatrix}
      1 & -1 \\
      0 & 2
    \end{bmatrix}
    \begin{bmatrix}
      2 \\ 1
    \end{bmatrix}
=  \begin{bmatrix}
      1 \\
      2
    \end{bmatrix}
\neq
    \begin{bmatrix}
    1 \\ -1
    \end{bmatrix}
$$

So, our chosen `Section`{.Agda} doesn't commute. That is, it doesn't respect the
global equalities, thus it is not a *global section.* Sounds like something
worth formalizing:

```
  record GlobalSection : Set where
    field
      section : forall (c : Carrier) → Section c
      commutes
        : {x y : Carrier}
        → (x<y : x < y)
        → restrict x<y ∘ section y ≈ section x
```

All that's left is to find a `GlobalSection`{.Agda} of our weird graph category:

<!--
```
module BadEx where
  open Preorder
  open Category LIN
  open Sheaf ex-preorder LIN
  open Sheaf.Sheaf
```
-->

-- TODO(sandy): make this cleaner

Unfortunately, this formalization doesn't quite work out; there are no arrows
out of `terminal`{.Agda}:

```
  boring-arrows
      : (f : 0 ~> 1)
      → (x : Vec ℤ 0)
      → f .linmap x ≡ + 0 ∷ []
  boring-arrows f [] with f .linmap [] in eq
  ... | x ∷ [] rewrite sym eq =
    begin
      f .linmap []                 ≡⟨⟩
      f .linmap (map (+ 0 *_) [])  ≡⟨ f .preserves-* (+ 0) _ ⟩
      map (+ 0 *_) (f .linmap [])  ≡⟨ cong (map (+ 0 *_)) eq ⟩
      map (+ 0 *_) (x ∷ [])        ≡⟨⟩
      (+ 0 * x) ∷ []               ≡⟨ cong (_∷ []) (*-zeroˡ +0) ⟩
      +0 ∷ []
    ∎
    where open Eq.≡-Reasoning
```

So, that's no good. We've modeled `Section`{.Agda} incorrectly, as the
generalized element approach doesn't work, since we are unable to follow the
example.

What are some other ways to go from an `Obj`{.Agda} to a `Set`{.Agda}? Maybe we
could try modeling this as a functor to `SET`{.Agda} instead:

<!--
```
module _ where
  open _=>_
  open import Relation.Binary.PropositionalEquality using (refl)
```
-->

```
  ex-func : LIN => SET
  ex-func .F-Obj x = Vec ℤ x
  ex-func .F-map f = f .linmap
  ex-func .F-map-id _ _ = refl
  ex-func .F-map-∘ g f a = refl
```

And we can try again with `Section`s:

and then we can say a `Section` is an element of the action of `Func`{.Agda}:

<!--
```
import Category.MyFunctor
module Sections
         {pre : Preorder}
         {C : Category}
         (Func : C Category.MyFunctor.=> SET)
         (sheaf : Sheaf.Sheaf pre C) where
  open Preorder pre
  open Sheaf.Sheaf sheaf
  open Category.MyFunctor._=>_ Func
  open Category SET
  open import Relation.Binary.PropositionalEquality using (_≡_)
```
-->

```
  Section : Carrier → Set
  Section c = F-Obj (Stalk c)
```

and a `GlobalSection`, which recall, is a globally-coherent assignment of
sections:

```
  record GlobalSection : Set where
    field
      section : forall (c : Carrier) → Section c
      commutes
        : {x y : Carrier}
        → (x<y : x < y)
        → F-map (restrict x<y) (section y) ≡ section x
```

<!--
```
module GoodEx where
  open Sheaf ex-preorder LIN
  open Sheaf.Sheaf ex
  open Sections ex-func ex
  open GlobalSection
  open Category.MyFunctor._=>_ ex-func
```
-->

```
  soln : GlobalSection
  soln .section v1 = + 2 ∷ + 1 ∷ []
  soln .section v2 = -[1+ 1 ] ∷ + 10 ∷ + 3 ∷ []
  soln .section e12 = + 1 ∷ + 2 ∷ []
  soln .commutes e12<v1 = refl
  soln .commutes e12<v2 = refl
  soln .commutes (ex<-refl _) = refl
```

Sure enough, this was a global section:

$$
\begin{bmatrix}
2 \\ 1
\end{bmatrix}
\in \text{Stalk } v1
$$

$$
\begin{bmatrix}
-2 \\ 10 \\ 3
\end{bmatrix}
\in \text{Stalk } v2
$$

and

$$
\begin{bmatrix}
1 \\ 2
\end{bmatrix}
\in \text{Stalk } e12
$$


## Example: Continuous Intervals

The paper presents a second example as well. Maybe it's just that I'm less
well-versed in the subject matter, but this example feels significantly more
incoherent than the first. I tried to work through it, and the formalization
above was sufficiently powerful to do what I needed, but I didn't understand the
example or what it was trying to accomplish. There was some Abelian group stuff
that never actually got used.

Rather than clean this section up, I'm instead going to spend the time before my
publication deadline writing about what I learned about pre-sheafs after hitting
the wall, and asking for help.


## Extracuricular Presheafs

So let's talk about what all of this sheaf business above is trying to do. The
ever helpful Reed Mullanix came to my rescue with a few helpful intuitions. To
paraphrase him (if there are any mistakes in the following, they are my
mistakes, not his):

> Think about a sensor network. You have some physical space, with a series of
> sensors attached in specific places. Maybe you have a microphone in the
> hallway, and a camera at the front door, and a thermometer in the bedroom.
> Each of these sensors is _locally correct_, that is, we can be reasonably sure
> that if the thermometer says 37C, it is in fact 37C.
>
> A presheaf is a mapping from this collection of sensors to a world in which
> we can reason about the total space. For example, we might want to get an idea
> of what's going on in the basement, where we have no sensors, but which is
> part of our house nevertheless.
>
> And a global section over that presheaf is a globally consistent take on the
> system. It's some mapping into the hypothesis space that _agrees with all of
> the measurements._ If we know it's 37C in the bedroom, we're probably not
> going to see snow in the front-door camera.

Okay, so what's all this preorder stuff about? I think it's actually just a poor
man's category. We can lift any preorder into a category by considering the `<`
relationship to be a morphism:

```
module PreorderToCategory (P : Preorder) where
  open Preorder P
  open Category

  open import Data.Unit using (⊤; tt)

  cat : Category
  cat .Obj = Carrier
  cat ._~>_ = _<_
  cat ._≈_ f g = ⊤
  cat .≈-equiv = sorry
  cat .id {A = A} = <-refl A
  cat ._∘_ g f = <-trans f g
  cat .∘-cong = λ _ _ → tt
  cat .id-r f = tt
  cat .id-l f = tt
  cat .∘-assoc h g f = tt
```

and now that we have a `Category`{.Agda}, we can avoid the whole `Sheaf`{.Agda}
/ `GlobalSection`{.Agda} by giving a functor into `SET`{.Agda}. Well, almost,
because `restrict`{.Agda} goes the opposite direction. So instead, we can build
an opposite category:

```
module Op (C : Category) where
  open Category

  data OpArr : Obj C → Obj C → Set where
    reverse : {X Y : Obj C} → C [ X , Y ] → OpArr Y X

  op : Category
  op .Obj = C .Obj
  op ._~>_ = OpArr
  op ._≈_ (reverse f) (reverse g) = C ._≈_ f g
  op .≈-equiv {A} {B} = sorry
  op .id = reverse (C .id)
  op ._∘_ (reverse g) (reverse f) = reverse (C ._∘_ f g)
  op .∘-cong = sorry
  op .id-r (reverse f) = C .id-l f
  op .id-l (reverse f) = C .id-r f
  op .∘-assoc (reverse h) (reverse g) (reverse f) =
    setoid C .isEquivalence .S.IsEquivalence.sym (C .∘-assoc f g h)
    where
      open import Relation.Binary.Bundles using (Setoid)
      open Setoid using (isEquivalence)
      import Relation.Binary.Structures as S
```

Now, we can express a presheaf as a functor:

```
module _ where
  open import Category.MyFunctor
  open Op

  Presheaf : Category → Set
  Presheaf C = op C => SET
```

or our specific example from earlier:

```
module _ where
  open PreorderToCategory ex-preorder
  open _=>_
  open import Data.Nat using (ℕ)
  open Op

  Z : ℕ → Set
  Z = Vec ℤ

  ex' : Presheaf cat
  ex' .F-Obj v1 = Z 2
  ex' .F-Obj v2 = Z 3
  ex' .F-Obj e12 = Z 2
  ex' .F-map (reverse e12<v1) = e12~>v1 .linmap
  ex' .F-map (reverse e12<v2) = e12~>v2 .linmap
  ex' .F-map (reverse (ex<-refl _)) a = a
  ex' .F-map-id A a = refl
  ex' .F-map-∘ (reverse e12<v1) (reverse (ex<-refl _)) a = refl
  ex' .F-map-∘ (reverse e12<v2) (reverse (ex<-refl _)) a = refl
  ex' .F-map-∘ (reverse (ex<-refl _)) (reverse e12<v1) a = refl
  ex' .F-map-∘ (reverse (ex<-refl _)) (reverse e12<v2) a = refl
  ex' .F-map-∘ (reverse (ex<-refl _)) (reverse (ex<-refl _)) a = refl
```

which leaves only the question of what a `GlobalSection` is under this
representation.


I got stumped on this one for a while too, but again, Reed to
the rescue, who points out that in our preorder, `<` corresponds to a "smaller"
space. Thus, we want to find a mapping out of the biggest space, which
corresponds to a top element in the order, or a terminal object in the category.
The terminal object is going to be the "total space" in consideration (in our
sensor example, eg.) and the functor laws will ensure consistency.

```
GlobalSection
    : {C : Category}
    → (pre : Presheaf C)
    → (t : HasTerminal C)
    → Set
GlobalSection pre t =
  pre ._=>_.F-Obj (t .HasTerminal.terminal)
```

Unfortunately, this is a problem for our worked example --- we don't *have* a
terminal object! But that's OK, it's easy to trivially construct one by just
adding a top:

~~~{.quiver}
\[\begin{tikzcd}
  & terminal \\
  v1 && v2 \\
  & e12
  \arrow[from=3-2, to=2-1]
  \arrow[from=3-2, to=2-3]
  \arrow[from=2-3, to=1-2]
  \arrow[from=2-1, to=1-2]
\end{tikzcd}\]
~~~

and by picking an object in `SET`{.Agda} to map it to for our presheaf. There
are some interesting choices here; we could just pick `⊤`{.Agda}, which is
interesting in how boring a choice it is. Such a thing trivially satisfies all
of the requirements, but it doesn't tell us much about the world. This is the
metaphorical equivalent of explaining our sensors' readings as "anything is
possible!"

More interestingly, we could pick `F-Obj terminal` to be `ℤ2 × ℤ3 × ℤ2`,
corresponding to the product of `F-Obj v1`, `F-Obj v2` and `F-Obj e12`. We can
satisfy the functor laws by projecting from the `F-Obj term` down to one of its
components. And, best of all, it gives us a place to stick the values from our
worked example.

I'd love to code this up in more detail, but unfortunately I'm out of time.
That's the flaw of trying to get through one paper a week, the deadline is
strict whether you're ready for it or not.

This whole post is a literate Agda file. I'm currently in the process of writing
an Agda blogging backend for the site, so hopefully if you come back in a week
or so, everything here should be hyperlinked and interactive.

