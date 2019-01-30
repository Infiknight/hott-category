{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics renaming (_∘_ to _after_)
open import Precategory
 

record Functor (C D : Precategory) : Set₁  where
  field
    on-objects : [ C ] → [ D ]
    on-arrows : ∀ {x y} → hom C x y → hom D (on-objects x) (on-objects y)
    respects-id : (x : [ C ]) → (on-arrows (id-on {C} x)) == (id-on {D} (on-objects x))
    respects-comp : ∀ {x y z} → (f : hom C x y) → (g : hom C y z ) →
                    (on-arrows (C :: g ∘ f )) == (D :: (on-arrows g) ∘ (on-arrows f))

_on-obj_ : ∀ {C D} → Functor C D → [ C ] → [ D ]
_on-obj_ F x = Functor.on-objects F x

_on-arr_ : ∀ {C D} (F : Functor C D) → {x y : [ C ]} → (f : hom C x y) → hom D (F on-obj x) (F on-obj y)
_on-arr_ F f = Functor.on-arrows F f

Identity-Functor : (A : Precategory) → (Functor A A)
Identity-Functor A = record
                       { on-objects = λ x → x
                       ; on-arrows = λ x₁ → x₁
                       ; respects-id = λ x → idp
                       ; respects-comp = λ f g → idp
                       }




record Natural-transformation {C D : Precategory} (F G : Functor C D) : Set₁  where
   field
     component : (x : [ C ]) → hom D (F on-obj x) (G on-obj x)
     naturality : ∀ {x y} → (f : hom C x y) →
                  (D :: (G on-arr f) ∘ (component x)) == (D :: (component y) ∘ (F on-arr f))

open Functor
open Natural-transformation

_at_ : ∀ {C D} {F G : Functor C D} → (Natural-transformation F G) → (x : [ C ]) → hom D (F on-obj x) (G on-obj x)
_at_ = component

nat-tr-id : ∀ {C D} (F : Functor C D) → Natural-transformation F F
nat-tr-id {C} {D} F = record { component = λ x → id-on {D} (F on-obj x) ; naturality = λ F → Precategory.∘-unit-r D ∙ ! (Precategory.∘-unit-l D) }

nat-tr-comp : ∀ {C D} { F G H : Functor C D} → Natural-transformation F G → Natural-transformation G H → Natural-transformation F H
nat-tr-comp {C} {D} {F} {G} {H} α β =
  record { component = λ x → D :: (β at x) ∘ (α at x) ;
           naturality = λ {x} {y} f → {! ap (λ h → D :: (β at y) ∘ h) (naturality α f) !} }

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



_*_ : {A B C : Precategory} (G : Functor B C) (F : Functor A B) → (Functor A C)
_*_  G F = record
                             { on-objects = λ x → G on-obj (F on-obj x) 
                             ; on-arrows = λ f →  G on-arr (F on-arr f)
                             ; respects-id = λ x → ap (λ f → G on-arr f) (respects-id F x) ∙ respects-id G ( F on-obj x)
                             ; respects-comp = λ f g → ap (λ f → G on-arr f) (respects-comp F f g) ∙ respects-comp G (F on-arr f) (F on-arr g)
                             }



Id-Functor-Equality-Right : {A B : Precategory} (F : Functor A B) → ((F * (Identity-Functor A)) == F)
Id-Functor-Equality-Right F = idp

Id-Functor-Equality-Left : {A B : Precategory} (F : Functor A B) → (((Identity-Functor B) * F) == F)
Id-Functor-Equality-Left record { on-objects = on-objects ; on-arrows = on-arrows ; respects-id = respects-id ; respects-comp = respects-comp } = {!!}

left-composite : {A B C : Precategory} (F : Functor A B) (G H : Functor B C) (N : Natural-transformation G H) → (Natural-transformation (G * F) (H * F))
left-composite F G H N = record { component = λ x → N at (F on-obj x) ; naturality = λ f → naturality N (F on-arr f) }

right-composite : {B C D : Precategory} (G H : Functor B C) (K : Functor C D) (N : Natural-transformation G H)  → (Natural-transformation (K * G) (K * H))
right-composite G H K N = record { component = λ x → K on-arr (component N x) ; naturality = λ {x} {y} f →  (! (respects-comp K (component N x) (H on-arr f)) ∙ ap (_on-arr_ K) (naturality N f)) ∙ respects-comp K (G on-arr f) (component N y)}

Functor-on-obj-associativity : {A B C D : Precategory} (H : Functor C D) (G : Functor B C) (F : Functor A B) → (( on-objects H) after (( on-objects G) after ( on-objects F))) ==  (((on-objects H) after (on-objects G)) after  (on-objects F))
Functor-on-obj-associativity H G F = λ= λ x → idp

Functor-on-arr-associativity : {A B C D : Precategory} (H : Functor C D) (G : Functor B C) (F : Functor A B) → (( on-objects H) after (( on-objects G) after ( on-objects F))) ==  (((on-objects H) after (on-objects G)) after  (on-objects F))
Functor-on-arr-associativity H G F = λ= λ x → idp


record Left-Adjoint {A B : Precategory} (F : Functor A B) : Set₁ where
  field
    G : Functor B A
    N : Natural-transformation (Identity-Functor A) (G * F)
    E : Natural-transformation (F * G) (Identity-Functor B)
    --p : nat-tr-comp ({!left-composite F (F * G) (Identity-Functor B) E)!} {!(right-composite (Identity-Functor A) (G * F) F N)!} == nat-tr-id F
    --p : (nat-tr-comp (right-composite (Identity-Functor A) (G * F) F N) (left-composite ?))) == (nat-tr-id F)
    p : nat-tr-comp (right-composite (Identity-Functor A) (G * F) F N) (left-composite {!F!} (F * G) {!Identity-Functor B!} {!E!}) == nat-tr-id F
    

