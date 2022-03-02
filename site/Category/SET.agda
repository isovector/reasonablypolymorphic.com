{-# OPTIONS --type-in-type #-}

module Category.SET where

open import Categories
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Relation.Binary.Structures


open Category

SET : Category
Obj     SET         = Set
_~>_    SET S T     = S → T
_≈_     SET {A} f g = forall (a : A) → f a ≡ g a
IsEquivalence.refl  (≈-equiv SET) _     = refl
IsEquivalence.sym   (≈-equiv SET) f a   = Eq.sym (f a)
IsEquivalence.trans (≈-equiv SET) f g a = Eq.trans (f a) (g a)
id      SET         = \a → a
_∘_     SET         = \g f a → g (f a)
∘-cong  SET {f' = f'} gg' ff' a rewrite ff' a | gg' (f' a) = refl
id-r    SET _ _     = refl
id-l    SET _ _     = refl
∘-assoc SET _ _ _ _ = refl

