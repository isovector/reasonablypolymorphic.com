{-# OPTIONS --type-in-type #-}

module Category.AGRP where

open import Algebra.Bundles using (AbelianGroup)
open import Categories
open import Relation.Binary.Bundles

open import Relation.Binary.Structures

import Relation.Binary.Reasoning.Setoid as SetoidR

record AGrpArr (S T : AbelianGroup _ _) : Set where
  open AbelianGroup S using (_≈_; _∙_; ε; _⁻¹)

  open AbelianGroup T using () renaming (_≈_ to _≋_; _∙_ to _×_; ε to εT; _⁻¹ to _-inv)
  field
    map : AbelianGroup.Carrier S → AbelianGroup.Carrier T
    preserves-∙
      : (a b : AbelianGroup.Carrier S)
      → map (a ∙ b) ≋ map a × map b
    preserves-ε
      : map ε ≋ εT
    preserves-inv
      : (a : AbelianGroup.Carrier S)
      → map (a ⁻¹) ≋ (map a) -inv
    preserves-≈
      : (a a' : AbelianGroup.Carrier S)
      → a ≈ a'
      → map a ≋ map a'

open Category hiding (setoid)
open AGrpArr
open AbelianGroup hiding (_∙_)

AGRP : Category
AGRP .Obj = AbelianGroup _ _
AGRP ._~>_ = AGrpArr
AGRP ._≈_ {A} {B} f g = forall a → B ._≈_ (map f a) (map g a)
AGRP .≈-equiv {B = B} .IsEquivalence.refl _ = B .refl
AGRP .≈-equiv {B = B} .IsEquivalence.sym f a = B .sym (f a)
AGRP .≈-equiv {B = B} .IsEquivalence.trans f g a = B .trans (f a) (g a)
AGRP .id .map x = x
AGRP .id {A} .preserves-∙ _ _ = A .refl
AGRP .id {A} .preserves-ε = A .refl
AGRP .id {A} .preserves-inv _ = A .refl
AGRP .id .preserves-≈ a a' x = x
(AGRP ∘ g) f .map ca = g .map (f .map ca)
AGRP ._∘_ {C = C} g f .preserves-∙ a b =
  C .trans (g .preserves-≈ _ _ (preserves-∙ f _ _)) (preserves-∙ g _ _)
AGRP ._∘_ {C = C} g f .preserves-ε =
  C .trans (g .preserves-≈ _ _ (preserves-ε f )) (preserves-ε g)
AGRP ._∘_ {C = C} g f .preserves-inv a =
  C .trans (g .preserves-≈ _ _ (preserves-inv f _)) (preserves-inv g _)
AGRP ._∘_ g f .preserves-≈ a a' x = g .preserves-≈ _ _ (f .preserves-≈ _ _ x)
AGRP .∘-cong {A} {B} {C} {g} {g'} {f} {f'} geq feq a =
  begin
    g .map (f .map a)
  ≈⟨ preserves-≈ g _ _ (feq _) ⟩
    map g (f' .map a)
  ≈⟨ geq _ ⟩
    g' .map (f' .map a)
  ∎
  where open SetoidR (setoid C) public
AGRP .id-r {B = B} f a = B .refl
AGRP .id-l {B = B} f a = B .refl
AGRP .∘-assoc {D = D} h g f a = D .refl

