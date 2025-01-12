```
{-# OPTIONS --type-in-type #-}

module blog.symbolic-differentiation where

open import Data.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.All
open import Relation.Binary.PropositionalEquality hiding ([_]; Extensionality)
open import Function
open import Axiom.Extensionality.Propositional using (Extensionality)

module Stuff (A : Set) where

  data Lang : Set where
    fail : Lang
    trivial : Lang
    done : Lang
    char : A → Lang
    both : Lang → Lang → Lang
    either : Lang → Lang → Lang
    after : Lang → Lang → Lang
    many : Lang → Lang
    also : Set → Lang → Lang

  compile : Lang → List A → Set
  compile fail w = ⊥
  compile trivial w = ⊤
  compile done w = w ≡ []
  compile (char c) w = w  ≡ [ c ]
  compile (both x y) w = compile x w × compile y w
  compile (either x y) w = compile x w ⊎ compile y w
  compile (after x y) w =
    Σ (List A × List A)
      λ { (u , v) → (w ≡ u ++ v) × compile x u × compile y v }
  compile (many x) w =
    Σ (List (List A))
      λ ws → (w ≡ concat ws) × All (compile x) ws
  compile (also x y) w = x × compile y w


  private
    variable
      B : Set

  v : (List A → B) → B
  v f = f []

  D : (List A → B) → List A → List A → B
  D f u = \v → f (u ++ v)

  v∘D : {B : Set} →  (f : List A → B) → (v ∘ D f) ≗ f
  v∘D f x = cong f $ ++-identityʳ x

  D[] : {B : Set} →  (f : List A → B) → D f [] ≡ f
  D[] f = refl

  postulate
    funext : Extensionality Agda.Primitive.lzero Agda.Primitive.lzero

  D++ : {B : Set} {u v : List A} → (f : List A → B) → D f (u ++ v) ≡ D (D f u) v
  D++ {u = u} {v = v} f = funext λ { x → cong f $ ++-assoc u v x }

  d : (List A → B) → A → (List A → B)
  d f a = D f [ a ]

  Dfoldl : {f : List A → B} → D f ≗ foldl d f
  Dfoldl [] = refl
  Dfoldl (x ∷ x₁) = Dfoldl x₁

  v_fail : v (compile fail) ≡ ⊥
  v_fail = refl

  v_trivial : v (compile trivial) ≡ ⊤
  v_trivial = refl


  v_done : v (compile done) ↔ ⊤
  Inverse.f v_done x = tt
  Inverse.f⁻¹ v_done x = refl
  Inverse.cong₁ v_done x = refl
  Inverse.cong₂ v_done x = refl
  proj₁ (Inverse.inverse v_done) tt = refl
  proj₂ (Inverse.inverse v_done) refl = refl









-- module _ where
--   open import Data.Char
--   open Stuff Char

--   a∪b : Lang
--   a∪b = (′ 'a' ∪ ′ 'b') ✹

--   _ : a∪b [ 'a' ]
--   _ = (('a' ∷ []) ∷ []) , refl , inj₁ refl ∷ []


```
