{-# OPTIONS --without-K --rewriting --type-in-type #-}

open import lib.Basics renaming (_∘_ to _after_)
open import lib.Base
open import Category
open import lib.types.Sigma
open import lib.types.Pi
open import Functor
open import lib.Funext


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


  nat2= : {α β : F ==> G} → (p : component α == component β)  → (α == β)
  nat2= {α} {β} idp = nat= {α} {β} idp (𝑵-has-all-paths {component α} {component β} (λ f → naturality α f) (λ f → naturality β f) idp)

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


index-functor : (A B C : Precategory ) → Functor (A 𝓧 B) C → (a : obj A) → Functor B C
index-functor A B C F a = record
  { on-objects = λ x → Functor.on-objects F (a , x)
  ; on-arrows = λ x → Functor.on-arrows F ((id A a) , x)
  ; respects-id = λ a₁ → Functor.respects-id F (a , a₁)
  ; respects-comp = λ {a₁} {b₁} {c₁} f g →
    Functor.on-arrows F (id A a , (B :: g ∘ f)) =⟨(ap (λ z → Functor.on-arrows F (z , (B :: g ∘ f))) (! (∘-unit-l A)))⟩
    Functor.on-arrows F ((A :: (id A a) ∘ (id A a)) , (B :: g ∘ f)) =⟨ (Functor.respects-comp F ((id A a) , f) ((id A a) , g)) ⟩
    (C :: Functor.on-arrows F (id A a , g) ∘ Functor.on-arrows F (id A a , f)) =∎
  }




curry' : {A B C : Precategory} → Functor (A 𝓧 B) C → Functor A (functor-precategory B C)
curry' {A} {B} {C} F = record
  { on-objects = λ x → index-functor A B C F x
  ; on-arrows = λ {a} {b} z → nat-tr (λ x → Functor.on-arrows F (z , id B x)) (λ {x} {y} f →
    (C :: Functor.on-arrows F (id A b , f) ∘ Functor.on-arrows F (z , id B x)) =⟨(! (Functor.respects-comp F (z , (id B x)) ((id A b) , f)))⟩
    (Functor.on-arrows F ((A 𝓧 B) :: (id A b , f) ∘ (z , id B x))) =⟨(ap (Functor.on-arrows F) idp)⟩
    (Functor.on-arrows F ( ( ( A :: (id A b) ∘ z ) , (B :: f ∘ (id B x)) ) ) ) =⟨(ap (Functor.on-arrows F) (pair×= ((Precategory.∘-unit-l A) ∙ ! (∘-unit-r A)) ((∘-unit-r B) ∙ ! (∘-unit-l B))))⟩
    (Functor.on-arrows F ( ( (A :: z ∘ (id A a)) , (B :: (id B y) ∘ f ) ) ) ) =⟨(ap (Functor.on-arrows F) idp)⟩
    (Functor.on-arrows F ((A 𝓧 B) :: (z , id B y) ∘ (id A a , f))) =⟨(Functor.respects-comp F ((id A a) , f) (z , (id B y)))⟩
    (C :: Functor.on-arrows F (z , id B y) ∘ Functor.on-arrows F (id A a , f)) =∎ )
  ; respects-id = λ a → nat2=  (λ= (λ x → (Functor.on-arrows F (id A a , id B x)) =⟨(Functor.respects-id F ((a , x)))⟩
    (id C ( Functor.on-objects F (a , x) )) =⟨(idp)⟩
    (id C (index-functor A B C F a on-obj x)) =⟨(idp)⟩
    (component (nat-tr-id (index-functor A B C F a)) x) =∎))
  ; respects-comp = λ {a} {b} {c} f g → nat2= (λ= (λ x →
      (Functor.on-arrows F ((A :: g ∘ f) , id B x)) =⟨(ap (λ z → Functor.on-arrows F ((A :: g ∘ f) , z)) (! (∘-unit-l B)))⟩
      (Functor.on-arrows F ((A :: g ∘ f) , (B :: (id B x) ∘ (id B x)) )) =⟨(Functor.respects-comp F (f , (id B x)) (g , (id B x)))⟩
      ( C :: (Functor.on-arrows F (g , id B x)) ∘ (Functor.on-arrows F (f , id B x)) ) =∎))
    }

uncurry' : {A B C : Precategory} → Functor A (functor-precategory B C) → Functor (A 𝓧 B) C
uncurry' {A} {B} {C} F = record
  { on-objects = λ x → (F on-obj (pr₁ x)) on-obj (pr₂ x)
    ; on-arrows = λ {c} {d} x → C :: (component (F on-arr (pr₁ x)) (pr₂ d)) ∘ ((F on-obj (pr₁ c)) on-arr (pr₂ x))
    ; respects-id = λ a →
      (C :: component (Functor.on-arrows F (id A (pr₁ a))) (pr₂ a) ∘ Functor.on-arrows (Functor.on-objects F (pr₁ a)) (id B (pr₂ a))) =⟨(ap (λ z → C :: component (Functor.on-arrows F (id A (pr₁ a))) (pr₂ a) ∘ z) (Functor.respects-id (F on-obj pr₁ a) (pr₂ a)))⟩
      (C :: component (Functor.on-arrows F (id A (pr₁ a))) (pr₂ a) ∘ (id C ((F on-obj (pr₁ a)) on-obj (pr₂ a) ) ) ) =⟨(ap (λ z → C :: (component z (pr₂ a)) ∘ id C (Functor.on-objects (Functor.on-objects F (pr₁ a)) (pr₂ a))) (Functor.respects-id F (pr₁ a)))⟩
      (C :: component (id (functor-precategory B C) (F on-obj (pr₁ a))) (pr₂ a) ∘ (id C ((F on-obj (pr₁ a)) on-obj (pr₂ a) ) ) ) =⟨(ap (λ z → C :: z ∘ id C ((F on-obj pr₁ a) on-obj pr₂ a)) idp)⟩
      (C :: (id C ((F on-obj (pr₁ a)) on-obj (pr₂ a) ) ) ∘ (id C ((F on-obj (pr₁ a)) on-obj (pr₂ a) ) ) ) =⟨ (∘-unit-l C) ⟩
      (id C (Functor.on-objects (Functor.on-objects F (pr₁ a)) (pr₂ a))) =∎
    ; respects-comp = λ {a} {b} {c} f g →
      (C :: component (Functor.on-arrows F (pr₁ ((A 𝓧 B) :: g ∘ f))) (pr₂ c) ∘ Functor.on-arrows (Functor.on-objects F (pr₁ a)) (pr₂ ((A 𝓧 B) :: g ∘ f))) =⟨(ap2 (λ z₁ z₂ → C :: component z₁ (pr₂ c) ∘ z₂) (Functor.respects-comp F (pr₁ f) (pr₁ g)) (Functor.respects-comp (F on-obj pr₁ a) (pr₂ f) (pr₂ g)))⟩
      (C :: component ((functor-precategory B C) :: (F on-arr (pr₁ g) ) ∘ (F on-arr (pr₁ f))) (pr₂ c) ∘ ( C :: ((F on-obj (pr₁ a)) on-arr (pr₂ g)) ∘ ((F on-obj (pr₁ a)) on-arr (pr₂ f) )) ) =⟨({!   !})⟩
      (C :: C :: component (Functor.on-arrows F (pr₁ g)) (pr₂ c) ∘ Functor.on-arrows (Functor.on-objects F (pr₁ b)) (pr₂ g) ∘ (C :: component (Functor.on-arrows F (pr₁ f)) (pr₂ b) ∘ Functor.on-arrows (Functor.on-objects F (pr₁ a)) (pr₂ f))) =∎
  }

--WIP
module OpenModality {P : Set} {pprop : is-prop P} where

  ◯ : (A : Set) → Set
  ◯ A = P → A

  ηᵒ  : {A : Set} (a : A) → ◯ A
  ηᵒ a x = a

  indₒ : {A : Set} {B : (◯ A) → Set} →
         ((a : A) → ◯ (B (ηᵒ {A} a) )) →
         ( (z : ◯ A) → ◯ (B z) )
  indₒ {A} {B} g  =
          λ z x → transport B (λ= (λ p → ap z (prop-path pprop x p))) (g (z x) x)
         --λ z x → transport B (λ= ( ηᵒ {A} (z x)) z (λ p → ap z (pprop x p)))  (g (z x) x)

  iii : {A : Set} {B : (◯ A) → Set} →
                  (f :  (a : A) → ◯ (B (ηᵒ {A} a) )) →
                  (a : A) →
                  ( indₒ {A} {B} f (ηᵒ a) == f a)
  iii {A} {B} f a = λ= (λ x →
                    (indₒ f (ηᵒ a) x) =⟨ {!   !} ⟩
                    (f a x) =∎ )

  --iii {A} {B} f a = λ= (indₒ f (ηᵒ a)) (λ p → f a p) (λ p →
  --                      (indₒ f (λ x → a) p) =〈_〉
  --                      (f a p) =∎ )
