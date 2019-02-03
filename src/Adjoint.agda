{-# OPTIONS --without-K --rewriting --allow-unsolved-metas  --type-in-type #-}

open import lib.Basics
open import Category
open import Functor
open import Natural-transformations

record Left-Adjoint {A B : Precategory} (F : Functor A B) : Set₁ where
  field
    G : Functor B A
    N : Natural-transformation (Identity-Functor A) (G * F) -- unit
    E : Natural-transformation (F * G) (Identity-Functor B)  -- counit
    -- (EF)(FN) = Identity natural transformation from F to F
    p : Nat-tr-comp-path-end (Nat-tr-comp-path-initial (Nat-tr-comp-path-middle (right-composite (Identity-Functor A) (G * F) F N) (left-composite F (F * G) (Identity-Functor B) E) (Functor-associativity F G F)) (Id-Functor-Equality-Right F)) (Id-Functor-Equality-Left F) == nat-tr-id F
    -- (GE)(NG) = Identity natural transformation from G to G
    q : Nat-tr-comp-path-end (Nat-tr-comp-path-initial (Nat-tr-comp-path-middle (left-composite G (Identity-Functor A) (G * F) N) (right-composite (F * G) (Identity-Functor B) G E) (! (Functor-associativity G F G))) (Id-Functor-Equality-Left G)) (Id-Functor-Equality-Right G) == nat-tr-id G


record Right-Adjoint {A B : Precategory} (F : Functor A B) : Set₁ where
  field
    G : Functor B A
    N : Natural-transformation (Identity-Functor B) (F * G) -- unit
    E : Natural-transformation (G * F) (Identity-Functor A) -- counit
    -- (EG)(GN) = Identity natural transformation from G to G
    p : Nat-tr-comp-path-end (Nat-tr-comp-path-initial (Nat-tr-comp-path-middle (right-composite (Identity-Functor B) (F * G) G N) (left-composite G (G * F) (Identity-Functor A) E) (Functor-associativity G F G)) (Id-Functor-Equality-Right G)) (Id-Functor-Equality-Left G) == nat-tr-id G
    -- (FE)(NF) = Identity natural transformation from F to F
    q : Nat-tr-comp-path-end (Nat-tr-comp-path-initial (Nat-tr-comp-path-middle (left-composite F (Identity-Functor B) (F * G) N) (right-composite (G * F) (Identity-Functor A) F E) (! (Functor-associativity F G F))) (Id-Functor-Equality-Left F)) (Id-Functor-Equality-Right F) == nat-tr-id F
