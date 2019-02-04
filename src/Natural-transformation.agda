{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import lib.Basics renaming (_∘_ to _after_)
open import Category
open import lib.types.Sigma
open import lib.types.Pi
open import Functor

module Natural-transformation where

open Category.Precategory

-- explicitly abstract over the types of a natural-transformation. Makes transporting for encode-decode easier
module nat-types {C D : Precategory} {F G : Functor C D} where
  component-type : Set₁
  component-type = (x : [ C ]) → hom D (F on-obj x) (G on-obj x)
  naturality-type : component-type → Set₀
  naturality-type = λ c → ∀ {x y} → (f : hom C x y) → (D :: (G on-arr f) ∘ (c x))  == (D :: (c y) ∘ (F on-arr f))

record Natural-transformation {C D : Precategory} (F G : Functor C D) : Set₁ where
  constructor nat-tr

  open nat-types {C} {D} {F} {G}
  field
    component  : component-type
    naturality : naturality-type component

open Natural-transformation

-- utility functions for easier access
module _ {C D : Precategory } where

  _==>_ : (F G : Functor C D) → Set₁
  _==>_ F G = Natural-transformation F G

  _at_ : {F G : Functor C D} → (F ==> G) → (x : [ C ]) → hom D (F on-obj x) (G on-obj x)
  _at_ = component

-- vertical composition of natural transformations
_∘ₙ_ : ∀ {C D} { F G H : Functor C D} → G ==> H → F ==> G → F ==> H
_∘ₙ_ {C} {D} {F} {G} {H} β α = record { component = λ x → D :: (β at x) ∘ (α at x) ;
                                        naturality = λ {x} {y} f →
                                        -- prove that two naturality squares considered "one above the other" commute.
                                        let Hf = H on-arr f; Gf = G on-arr f; βx = β at x; αx = α at x
                                            βy = β at y; αy = α at y; assoc = Precategory.∘-assoc D
                                         in
                                            (D :: Hf ∘ (D :: βx ∘ αx)) =⟨ assoc ⟩
                                            (D :: (D :: Hf ∘ βx) ∘ αx) =⟨ ap (λ h → D :: h ∘ αx) (naturality β f) ⟩
                                            (D :: (D :: βy ∘ Gf) ∘ αx) =⟨ ! assoc ⟩
                                            (D :: βy ∘ (D :: Gf ∘ αx)) =⟨ ap ( D :: βy ∘_ ) (naturality α f) ⟩
                                            (D :: βy ∘ (D :: αy ∘ (F on-arr f))) =⟨  assoc ⟩
                                            (D :: ( D :: βy ∘ αy) ∘ (F on-arr f)) =∎  }

-- identity natural transformation - each component is the identity arrow
nat-tr-id : ∀ {C D} (F : Functor C D) → F ==> F
nat-tr-id {C} {D} F = nat-tr (λ x → id D (F on-obj x)) $ λ _ → (∘-unit-r D) ∙ ! (∘-unit-l D)

--encode / decode and H-levels
module _ {C D : Precategory} {F G : Functor C D} where
  open nat-types {C} {D} {F} {G} renaming (component-type to 𝑪)
  open nat-types {C} {D} {F} {G} renaming (naturality-type to 𝑵)

  -- encode-decode via Σ types
  nat-to-Σ : F ==> G → Σ 𝑪 𝑵
  nat-to-Σ α = component α , naturality α

  Σ-to-nat : Σ 𝑪 𝑵 → F ==> G
  Σ-to-nat (fst , snd) = nat-tr fst snd

  Σ-≃-nat :  (Σ 𝑪 𝑵) ≃ (F ==> G)
  Σ-≃-nat  = Σ-to-nat , is-eq Σ-to-nat nat-to-Σ (λ b → idp) (λ a → idp)

  nat= : {α β : F ==> G} → (p : component α == component β) → (q : naturality α == naturality β [ naturality-type ↓ p ])  → (α == β)
  nat= idp idp = idp


  𝑵-is-prop : (c : 𝑪) → is-prop (𝑵 c)
  -- unwrap the explicit arguments
  𝑵-is-prop c = Πi-level λ x → Πi-level λ y → Π-level λ f →
                          has-level-apply-instance {{ homs-are-sets D (F on-obj x) (G on-obj y) }}

  𝑵-has-all-paths : {c₁ c₂ : 𝑪} → (n₁ : 𝑵 c₁) → (n₂ : 𝑵 c₂) → (p : c₁ == c₂) → (n₁ == n₂ [ 𝑵 ↓ p ])
  𝑵-has-all-paths {c} {.c} f g idp = prop-has-all-paths {{ 𝑵-is-prop c }} f g

  -- show that nat-transformations are a set via detour to Σ types
  nat-is-set : is-set (F ==> G)
  nat-is-set = equiv-preserves-level (Σ-≃-nat) {{Σ-level
                                                  (Π-level λ x → has-level-in λ x₁ y → has-level-apply-instance {{ homs-are-sets D (F on-obj x) (G on-obj x) }})
                                                  λ x → prop-is-set (𝑵-is-prop x) }}

  -- units for natural transformations. Use that naturality-type is prop to shortcut directly proving equality. Futhermore, such direct proof might be infeasible
  -- due to mismatch with implicit / explicit arguments
  module _ (α : F ==> G) where
    ∘ₙ-unit-r : (α ∘ₙ nat-tr-id F ) == α
    ∘ₙ-unit-r = let comp= : (λ x → (D :: (α at x) ∘ (id D (F on-obj x)))) == (λ x → α at x)
                    comp= = (λ= λ x → ∘-unit-r D)
                in nat= comp=  (𝑵-has-all-paths (naturality (α ∘ₙ (nat-tr-id F))) (naturality α) comp=)

    ∘ₙ-unit-l : ((nat-tr-id G) ∘ₙ α ) == α
    ∘ₙ-unit-l = let comp= : (λ x → D :: (id D $ G on-obj x) ∘ (α at x) ) == (λ x → α at x)
                    comp= = (λ= λ x → ∘-unit-l D)
                in nat= comp= (𝑵-has-all-paths (naturality ( (nat-tr-id G) ∘ₙ α )) (naturality α) comp=)

-- associativity. Again utilize 𝑵-has-all-paths
module _{A B : Precategory} {F G H J : Functor A B} (α : F ==> G)  (β : G ==> H) (γ : H ==> J) where

  ∘ₙ-assoc : (γ ∘ₙ (β ∘ₙ α)) == ((γ ∘ₙ β) ∘ₙ α)
  ∘ₙ-assoc = let assoc : (λ x → (B :: (γ at x) ∘ (B :: (β at x) ∘ (α at x)))) == (λ x → (B :: (B :: (γ at x) ∘ (β at x)) ∘ (α at x)))
                 assoc = (λ= λ x → Precategory.∘-assoc B)
             in nat= assoc ((𝑵-has-all-paths {_} {_} {F} {J} (naturality (γ ∘ₙ (β ∘ₙ α))) (naturality ((γ ∘ₙ β) ∘ₙ α)) assoc))

-- exponential category in cat. The objects are functors and the arrows natural transformations between them
functor-precategory : (A B : Precategory) → Precategory
functor-precategory A B = record { ob = Functor A B
                                  ; hom = Natural-transformation
                                  ; id = nat-tr-id
                                  ; homs-are-sets = λ _ _ → nat-is-set
                                  ; _∘_ = _∘ₙ_
                                  ; ∘-unit-l = λ {_} {_} {α} → ∘ₙ-unit-l α
                                  ; ∘-unit-r = λ {_} {_} {α} → ∘ₙ-unit-r α
                                  ; ∘-assoc = λ {_} {_} {_} {_} {α} {β} {γ} → ∘ₙ-assoc α β γ }

-- left and right whiskering

-- Given functors F : A → B and G, H : B → C and natural transformation N : G → H, we define the left-composite as the natural transformation from G * F to H * F,
-- given by, for each object a : A, we have the component N(Fa).
_*ₗ_ : ∀ {A B C} {G H : Functor B C} (γ : G ==> H) →  (F : Functor A B) → (G * F) ==> (H * F)
_*ₗ_ γ F = nat-tr (λ x → γ at (F on-obj x)) $ λ f → naturality γ (F on-arr f)

-- -- Given functors G, H : B → C and K : C → D and natural transformation N : G → H, we define the right composite as the natural tranformation from K * G to K * H,
-- -- given by, for object b : B, we have the component K(Nb).
_*ᵣ_ : ∀ {B C D} (K : Functor C D) → {G H : Functor B C} → (γ : G ==> H) → (K * G) ==> (K * H)
_*ᵣ_ K {G} {H} γ = nat-tr (λ x → K on-arr (γ at x)) $
                          λ {x} {y} f → (! (respects-comp K (γ at x) (H on-arr f)) ∙ ap (on-arrows K) (naturality γ f)) ∙ respects-comp K (G on-arr f) (γ at y)
                  where open Functor.Functor
