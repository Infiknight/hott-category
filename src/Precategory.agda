{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics renaming (_∘_ to _after_)

module Precategory where

  record Precategory : Set₂ where
    field

      objects : Set₁
      arrows : (x y : objects) → Set₁
      id-arrow : ∀ x → arrows x x

      homs-are-hsets :  ∀ x y → is-set (arrows x y)

      _∘_ : ∀ {x y z} → (arrows y z) → (arrows x y)  → (arrows x z)
      ∘-unit-l : ∀ {x y} {f : arrows x y} → ((id-arrow y) ∘ f) == f
      ∘-unit-r : ∀ {x y} {f : arrows x y} →  (f ∘ id-arrow x) == f
      assoc : ∀ {x y z w} {f : arrows x y} {g : arrows y z} {h : arrows z w} → (h ∘ (g ∘ f)) == ((h ∘ g) ∘ f)

  module _ where
    open Precategory

    hom : (C : Precategory) → objects C → objects C → Set₁
    hom C x y = arrows C x y
    syntax hom C x y = C [ x ⇒ y ]

    obj : Precategory → Set₁
    obj = objects
    syntax obj C = [ C ]

    id-on : {C : Precategory} (x : objects C) → (arrows C x x)
    id-on {C} x = id-arrow C x

    _::_∘_ : (C : Precategory) → ∀ {x y z} → (arrows C y z) → (arrows C x y) → (arrows C x z)
    _::_∘_ C g f = Precategory._∘_ C g f
