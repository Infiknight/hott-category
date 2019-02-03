{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import lib.Basics renaming (_∘_ to _after_)
open import Precategory
open import lib.types.Sigma
open import lib.types.Pi
open import Functor

module Natural-transformations where

module nat-types {C D : Precategory} {F G : Functor C D} where
  component-type : Set₁
  component-type = (x : [ C ]) → hom D (F on-obj x) (G on-obj x)
  naturality-type : component-type → Set₀
  naturality-type = λ c → ∀ {x y} → (f : hom C x y) → (D :: (G on-arr f) ∘ (c x))  == (D :: (c y) ∘ (F on-arr f))

record Natural-transformation {C D : Precategory} (F G : Functor C D) : Set₁ where
  open nat-types {C} {D} {F} {G}
  field
    component  : component-type
    naturality : naturality-type component

open Natural-transformation

_at_ : ∀ {C D} {F G : Functor C D} → (Natural-transformation F G) → (x : [ C ]) → hom D (F on-obj x) (G on-obj x)
_at_ = component

nat-tr-id : ∀ {C D} (F : Functor C D) → Natural-transformation F F
nat-tr-id {C} {D} F = record { component = λ x → id-on {D} (F on-obj x) ; naturality = λ _ → (Precategory.∘-unit-r D) ∙ ! (Precategory.∘-unit-l D) }

_∘ₙ_ : ∀ {C D} { F G H : Functor C D} → Natural-transformation G H → Natural-transformation F G → Natural-transformation F H
_∘ₙ_ {C} {D} {F} {G} {H} β α = record { component = λ x → D :: (β at x) ∘ (α at x) ;
                                               naturality = λ {x} {y} f →
                                                let Hf = H on-arr f; Gf = G on-arr f; βx = β at x; αx = α at x
                                                    βy = β at y; αy = α at y; assoc = Precategory.assoc D in
                                                (D :: Hf ∘ (D :: βx ∘ αx)) =⟨ assoc ⟩
                                                (D :: (D :: Hf ∘ βx) ∘ αx) =⟨ ap (λ h → D :: h ∘(α at x)) (naturality β f) ⟩
                                                (D :: (D :: βy ∘ Gf) ∘ αx) =⟨ ! assoc ⟩
                                                (D :: βy ∘ (D :: Gf ∘ αx)) =⟨ ap ( D :: βy ∘_ ) (naturality α f) ⟩
                                                (D :: βy ∘ (D :: αy ∘ (F on-arr f))) =⟨  assoc ⟩
                                                (D :: ( D :: βy ∘ αy) ∘ (F on-arr f)) =∎  }

module _ {C D : Precategory} {F G : Functor C D} where
  open nat-types {C} {D} {F} {G}

  nat-type-is-prop : (c : component-type) → is-prop (naturality-type c)
  nat-type-is-prop c = Πi-level λ x → Πi-level λ y → Π-level λ f →
                          has-level-apply-instance {{ Precategory.homs-are-hsets D (F on-obj x) (G on-obj y) }}

  nat-type-has-all-paths : {c₁ c₂ : component-type} → (n₁ : naturality-type c₁) → (n₂ : naturality-type c₂) → (p : c₁ == c₂) → (n₁ == n₂ [ naturality-type ↓ p ])
  nat-type-has-all-paths {c} {.c} f g idp = prop-has-all-paths {{nat-type-is-prop c}} f g

  nat-to-Σ : Natural-transformation F G → Σ component-type naturality-type
  nat-to-Σ α = component α , naturality α

  Σ-to-nat : Σ component-type naturality-type → Natural-transformation F G
  Σ-to-nat (fst , snd) = record { component = fst ; naturality = snd }

  Σ-≃-nat :  Σ component-type naturality-type ≃ Natural-transformation F G
  Σ-≃-nat  = Σ-to-nat , is-eq Σ-to-nat nat-to-Σ (λ b → idp) (λ a → idp)

  nat= : {α β : Natural-transformation F G} → (p : component α == component β) → (q : naturality α == naturality β [ naturality-type ↓ p ])  → (α == β)
  nat= idp idp = idp

  nat-is-set : is-set (Natural-transformation F G)
  nat-is-set = equiv-preserves-level (Σ-≃-nat) {{Σ-level
                                                  (Π-level λ x → has-level-in λ x₁ y → has-level-apply-instance {{ Precategory.homs-are-hsets D (F on-obj x) (G on-obj x) }})
                                                  λ x → prop-is-set (nat-type-is-prop x) }}

  module _ (α : Natural-transformation F G) where
    ∘ₙ-unit-r : (α ∘ₙ nat-tr-id F ) == α
    ∘ₙ-unit-r = let comp= : (λ x → (D :: (α at x) ∘ (id-on {D} (F on-obj x)))) == (λ x → α at x)
                    comp= = (λ= λ x → Precategory.∘-unit-r D)
                  in nat= comp=  (nat-type-has-all-paths (naturality (α ∘ₙ (nat-tr-id F))) (naturality α) comp=)

    ∘ₙ-unit-l : ( (nat-tr-id G) ∘ₙ α ) == α
    ∘ₙ-unit-l = let comp= : (λ x → D :: (id-on {D} $ G on-obj x) ∘ (α at x) ) == (λ x → α at x)
                    comp= = (λ= λ x → Precategory.∘-unit-l D)
                in nat= comp= ( {! nat-types  !})

module _ {A B : Precategory} {F G H J : Functor A B} {α : Natural-transformation F G}
      {β : Natural-transformation G H} {γ : Natural-transformation H J} where

  ∘ₙ-assoc : (γ ∘ₙ (β ∘ₙ α)) == ((γ ∘ₙ β) ∘ₙ α)
  ∘ₙ-assoc = let assoc : (λ x → (B :: (γ at x) ∘ (B :: (β at x) ∘ (α at x)))) == (λ x → (B :: (B :: (γ at x) ∘ (β at x)) ∘ (α at x)))
                 assoc = (λ= λ x → Precategory.assoc B)
             in  nat= assoc {!   !}

functor-precategory : (A B : Precategory) → Precategory
functor-precategory A B = record { objects = Functor A B
                                  ; arrows = Natural-transformation
                                  ; id-arrow = nat-tr-id
                                  ; homs-are-hsets = λ _ _ → nat-is-set
                                  ; _∘_ = _∘ₙ_
                                  ; ∘-unit-l = λ {_} {_} {α} → ∘ₙ-unit-l α
                                  ; ∘-unit-r = λ {_} {_} {α} →  ∘ₙ-unit-r α
                                  ; assoc = λ{f} {g} {h} {j} ∘ₙ-assoc }


left-composite : ∀ {A B C} (F : Functor A B) (G H : Functor B C) (γ : Natural-transformation G H) → (Natural-transformation (G * F) (H * F))
left-composite F G H γ = record { component = λ x → γ at (F on-obj x) ; naturality = λ f → naturality γ (F on-arr f)}

right-composite : ∀ {B C D} (G H : Functor B C) (K : Functor C D) (γ : Natural-transformation G H)  → (Natural-transformation (K * G) (K * H))
right-composite G H K γ = record { component = λ x → K on-arr (γ at x) ;
                                   naturality = λ {x} {y} f → (! (Functor.respects-comp K (γ at x) (H on-arr f)) ∙ ap (on-arrows K) (naturality γ f)) ∙ respects-comp K (G on-arr f) (γ at y) }
                          where open Functor.Functor
