{-# OPTIONS --type-in-type #-}

module Categories where

open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as SetoidR

record Category : Set where
  infix 6 _~>_
  infix 2 _≈_

  field
    -- Objects and arrows in the category
    Obj : Set
    _~>_ : (A B : Obj) → Set

    -- The meaning of equality of morphisms
    _≈_
      : {A B : Obj}
      → A ~> B
      → A ~> B
      → Set

    -- _≈_ forms a equivalence relationship
    ≈-equiv : {A B : Obj} → IsEquivalence (_≈_ {A} {B})

    -- Id and composition
    id : {A : Obj} → A ~> A
    _∘_ : {A B C : Obj} → B ~> C → A ~> B → A ~> C

    ∘-cong
        : ∀ {A B C} {g g' : B ~> C} {f f' : A ~> B}
        → g ≈ g'
        → f ≈ f'
        → g ∘ f ≈ g' ∘ f'

    -- Laws
    id-r : {A B : Obj} (f : A ~> B) → f ∘ id ≈ f
    id-l : {A B : Obj} (f : A ~> B) → id ∘ f ≈ f
    ∘-assoc
      : {A B C D : Obj}
      → (h : C ~> D)
      → (g : B ~> C)
      → (f : A ~> B)
      → h ∘ (g ∘ f) ≈ (h ∘ g) ∘ f

  -- "Forward" composition
  _>>_ : {A B C : Obj} → A ~> B → B ~> C → A ~> C
  _>>_ f g = g ∘ f

  >>-assoc
      : {A B C D : Obj}
      → (f : A ~> B)
      → (g : B ~> C)
      → (h : C ~> D)
      → f >> (g >> h) ≈ (f >> g) >> h
  >>-assoc f g h = IsEquivalence.sym ≈-equiv (∘-assoc h g f)

  setoid : {X Y : Obj} → Setoid _ _
  Setoid.Carrier (setoid {X} {Y}) = X ~> Y
  Setoid._≈_ setoid  = _≈_
  Setoid.isEquivalence setoid = ≈-equiv

  module HomReasoning {A B : Obj} where
    open SetoidR (setoid {A} {B}) public
    open IsEquivalence (≈-equiv {A} {B}) public

module _ where
  open Category


  infix 2 _[_≈_]
  _[_≈_] : (r : Category) {A B : Obj r} → (r ~> A) B → (r ~> A) B → Set
  _[_≈_] = _≈_

  -- Notational convenience for arrows in a category. Helpful when dealing with
  -- multiple categories at once.
  -- eg we can talk about a set arrow via `SET [ Bool , Int ]`
  infix 5 _[_,_]
  _[_,_] : (C : Category) -> Obj C -> Obj C -> Set
  C [ X , Y ] = _~>_ C X Y

  -- Notational convenience for composition.
  -- eg we can talk about a set composition `SET [ show ∘ length ] : SET [ List A , String ]`
  infix 5 _[_∘_]
  _[_∘_] : (C : Category) -> {X Y Z : Obj C} -> C [ Y , Z ] -> C [ X , Y ] -> C [ X , Z ]
  _[_∘_] = _∘_

  -- Notational convenience for "forward" composition.
  -- eg we can talk about a set composition `SET [ length >> show ] : SET [ List A , String ]`
  infix 5 _[_>>_]
  _[_>>_] : (C : Category) -> {X Y Z : Obj C} -> C [ X , Y ] -> C [ Y , Z ] -> C [ X , Z ]
  _[_>>_] = _>>_

module _ (C : Category) where
  open Category C
  record HasTerminal : Set where
    field
      terminal : Obj
      term-arr
          : (A : Obj)
          → A ~> terminal
      term-unique
          : {A : Obj}
          → (f : A ~> terminal)
          → f ≈ term-arr A

