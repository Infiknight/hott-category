{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import lib.Basics renaming (_∘_ to _after_)
open import Precategory
open import lib.types.Sigma
open import lib.types.Pi

record Functor (C D : Precategory) : Set₁  where
  field
    on-objects : [ C ] → [ D ]
    on-arrows : ∀ {x y} → hom C x y → hom D (on-objects x) (on-objects y)
    respects-id : (x : [ C ]) → (on-arrows (id-on {C} x)) == (id-on {D} (on-objects x))
    respects-comp : ∀ {x y z} → (f : hom C x y) → (g : hom C y z ) →
                    (on-arrows (C :: g ∘ f )) == (D :: (on-arrows g) ∘ (on-arrows f))


module _ { C D : Precategory } where

  _on-obj_ : (Functor C D) → [ C ] → [ D ]
  _on-obj_ F = Functor.on-objects F

  _on-arr_ : (F : Functor C D) → ∀ {x y} → (f : hom C x y) → hom D (F on-obj x) (F on-obj y)
  _on-arr_ F f = Functor.on-arrows F f

-- precategory-set : Precategory
-- precategory-set = record { objects = Σ Set (is-set)
--                           ; arrows = λ x y → (fst x) → (fst y)
--                           ; id-arrow =  λ x y → y
--                           ; homs-are-hsets = {!   !}
--                           ; _∘_ = λ g f → g after f
--                           ; ∘-unit-l = idp
--                           ; ∘-unit-r = idp
--                           ; assoc = idp }

_*_ : ∀ {A B C} (G : Functor B C) (F : Functor A B) → (Functor A C)
_*_  G F = record { on-objects = λ x → G on-obj (F on-obj x)
                   ; on-arrows = λ f →  G on-arr (F on-arr f)
                   ; respects-id = λ x → ap (on-arrows G) (respects-id F x) ∙ respects-id G ( F on-obj x)
                   ; respects-comp = λ f g → ap (on-arrows G) (respects-comp F f g) ∙ respects-comp G (F on-arr f) (F on-arr g) }
           where open Functor
