{-# OPTIONS --type-in-type #-}

module Category.LIN where

open import Categories
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Relation.Binary.Structures
open import Data.Nat using (ℕ; zero; suc)


open import Data.Vec
open import Data.Integer

record LinMap (m n : ℕ) : Set where
  field
    linmap : Vec ℤ m → Vec ℤ n
    preserves-+
        : ∀ u v
        → linmap (zipWith _+_ u v) ≡ zipWith _+_ (linmap u) (linmap v)
    preserves-*
        : ∀ a v
        → linmap (map (a *_) v) ≡ map (a *_) (linmap v)

open LinMap


open Category
LIN : Category
LIN .Obj = ℕ
LIN ._~>_ = LinMap
LIN ._≈_ f g = forall x → linmap f x ≡ linmap g x
IsEquivalence.refl  (≈-equiv LIN) _     = refl
IsEquivalence.sym   (≈-equiv LIN) f a   = Eq.sym (f a)
IsEquivalence.trans (≈-equiv LIN) f g a = Eq.trans (f a) (g a)
LIN .id .linmap a = a
LIN .id .preserves-+ u v = refl
LIN .id .preserves-* a v = refl
(LIN ∘ g) f .linmap a = linmap g (linmap f a)
(LIN ∘ g) f .preserves-+ u v =
  begin
    linmap g (linmap f (zipWith _+_ u v))
  ≡⟨ cong (linmap g) (preserves-+ f _ _) ⟩
    linmap g (zipWith _+_ (linmap f u) (linmap f v))
  ≡⟨ preserves-+ g _ _ ⟩
    zipWith _+_ (linmap g (linmap f u)) (linmap g (linmap f v))
  ∎
  where open Eq.≡-Reasoning
(LIN ∘ g) f .preserves-* a v =
  begin
    linmap g (linmap f (map (_*_ a) v))
  ≡⟨ cong (linmap g) (preserves-* f a _) ⟩
    linmap g (map (_*_ a) (linmap f v))
  ≡⟨ preserves-* g a _ ⟩
    map (_*_ a) (linmap g (linmap f v))
  ∎
  where open Eq.≡-Reasoning
LIN .∘-cong {g = g} {f = f} p2 p1 a rewrite p2 (linmap f a) | p1 a = refl
LIN .id-r f x = refl
LIN .id-l f x = refl
LIN .∘-assoc h g f x = refl


LIN-term : HasTerminal LIN
LIN-term .HasTerminal.terminal = 0
LIN-term .HasTerminal.term-arr _ .linmap _ = []
LIN-term .HasTerminal.term-arr _ .preserves-+ u v = refl
LIN-term .HasTerminal.term-arr _ .preserves-* a v = refl
LIN-term .HasTerminal.term-unique {A = n} f x = help (linmap f x)
  where
    help : {A : Set} (w : Vec A 0) → w ≡ []
    help [] = refl

