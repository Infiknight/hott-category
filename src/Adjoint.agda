{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import lib.Basics
open import Category
open import Functor
open import Natural-transformation

module Adjoint where

-- workaround for ap
module _ {A B : Precategory} where
  -- If F = F', and α is a natural transformation from F to G, then α is also a natural transformation from F' to G.
  nat-tr-comp-path-initial :  {F G F' : Functor A B} (α : F ==> G) (p : F == F') → (F' ==> G)
  nat-tr-comp-path-initial α idp = α

  -- If G = G' and α is a natural transformation from F to G, then α is also a natural transformation from F to G'.
  nat-tr-comp-path-end : {F G G' : Functor A B} (α : F ==> G) (p : G == G') → (F ==> G')
  nat-tr-comp-path-end α idp = α

  -- If α is a natural transformation from F to G, and β is a natural transformation from H to I, and G = H, then we can compose the two to get a natural transformation from F to I.
  nat-tr-comp-path-middle : {F G H I : Functor A B} (β : H ==> I) (α : F ==> G) (p : G == H) → (F ==> I)
  nat-tr-comp-path-middle β α idp = β ∘ₙ α

record Left-Adjoint {A B : Precategory} (F : Functor A B) : Set₁ where
  field
    G : Functor B A
    η : (id-functor A) ==> (G * F) -- unit
    ε : (F * G) ==> (id-functor B)  -- counit
    adj-F : (nat-tr-comp-path-end (nat-tr-comp-path-initial (nat-tr-comp-path-middle (ε *ₗ F) (F *ᵣ η) $ *-assoc F G F ) *-unit-r) *-unit-l) == nat-tr-id F
    adj-G : (nat-tr-comp-path-end (nat-tr-comp-path-initial (nat-tr-comp-path-middle (G *ᵣ ε) (η *ₗ G) $ ! (*-assoc G F G )) *-unit-l) *-unit-r) == nat-tr-id G

record Right-Adjoint {A B : Precategory} (F : Functor A B) : Set₁ where
  field
    G : Functor B A
    η : (id-functor B) ==> (F * G)
    ε : (G * F) ==> (id-functor A)
    adj-F : (nat-tr-comp-path-end (nat-tr-comp-path-initial (nat-tr-comp-path-middle (F *ᵣ ε) (η *ₗ F) $ ! (*-assoc F G F)) *-unit-l) *-unit-r) == nat-tr-id F
    adj-G : (nat-tr-comp-path-end (nat-tr-comp-path-initial (nat-tr-comp-path-middle (ε *ₗ G) (G *ᵣ η) $ *-assoc G F G ) *-unit-r) *-unit-l) == nat-tr-id G
