module Category.MyFunctor where

open import Categories

open Category

infix 6 _=>_
record _=>_ (C : Category) (D : Category) : Set where
  field
    F-Obj : Obj C → Obj D
    F-map : {A B : Obj C} → C [ A , B ] → D [ F-Obj A , F-Obj B ]

    F-map-id
        : (A : Obj C)
        → D [ F-map (id C {A})
            ≈ id D {F-Obj A}
            ]
    F-map-∘
        : {X Y Z : Obj C}
        → (g : C [ Y ,  Z ])
        → (f : C [ X ,  Y ])
        → D [     F-map ( C [ g ∘ f ])
            ≈ D [ F-map g ∘ F-map f ]
            ]

