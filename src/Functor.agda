{-# OPTIONS --without-K #-}

open import lib.Equality
open import Precategory

record Functor (C D : Precategory) : Set  where
  field
    on-objects : [ C ] → [ D ]
    on-arrows : {x y : [ C ]} → C [ x , y ] → D [ on-objects x , on-objects y ]
    respects-id : (x : [ C ]) → (on-arrows (id-on {C} x)) == (id-on {D} (on-objects x))
    respects-comp : {x y z : [ C ]} → (f : C [ x , y ]) → (g : C [ y , z ]) →
                    (on-arrows (C :: g ∘ f )) == (D :: (on-arrows g) ∘ (on-arrows f))

_on-obj_ : {C D : Precategory} (F : Functor C D) → [ C ] → [ D ]
_on-obj_ F x = Functor.on-objects F x

_on-arr_ : {C D : Precategory} (F : Functor C D) → {x y : [ C ]} → (f : C [ x , y ]) → D [ F on-obj x , F on-obj y ]
_on-arr_ F f = Functor.on-arrows F f

record Natural-transformation {C D : Precategory} (F G : Functor C D) : Set  where
   field
     component : (x : [ C ]) → D [ F on-obj x , G on-obj x ]
     naturality : {x y : [ C ]} → (f : C [ x , y ]) →
                  (D :: (G on-arr f) ∘ (component x)) == (D :: (component y) ∘ (F on-arr f))

open Functor
open Natural-transformation

_at_ : {C D : Precategory} {F G : Functor C D} → (Natural-transformation F G) → (x : [ C ]) → D [ F on-obj x , G on-obj x ]
_at_ = component

nat-tr-id : {C D : Precategory} (F : Functor C D) → Natural-transformation F F
nat-tr-id {C} {D} F = record { component = λ x → id-on {D} (F on-obj x) ; naturality = λ F → Precategory.∘-unit-r D ∙ ! (Precategory.∘-unit-l D) }

nat-tr-comp : { C D : Precategory} { F G H : Functor C D} → Natural-transformation F G → Natural-transformation G H → Natural-transformation F H
nat-tr-comp {C} {D} {F} {G} {H} α β =
  record { component = λ x → D :: (β at x) ∘ (α at x) ;
           naturality = λ {x} {y} f → {! ap (λ h → D :: (β at y) ∘ h) (Natural-transformation.naturality α f) !} }

functor-precategory : (A B : Precategory) → Precategory
functor-precategory A B = record { objects = Functor A B
                                  ; arrows = λ F G → Natural-transformation F G
                                  ; id-arrow = nat-tr-id
                                  ; homs-are-hsets = {!   !}
                                  ; _∘_ = λ α β → record { component = λ x → B :: (α at x) ∘ (β at x) ;
                                                           naturality = λ f → {!   !} }
                                  ; ∘-unit-l = {!   !}
                                  ; ∘-unit-r = {!   !}
                                  ; assoc = {!   !} }
