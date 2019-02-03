{-# OPTIONS --without-K --rewriting --type-in-type --allow-unsolved-metas #-}

open import lib.Basics renaming (_∘_ to _after_)
open import lib.Function2
open import Category

open Precategory
open Isomorphisms

record Functor (C D : Precategory) : Set₁  where
  field
    on-objects : [ C ] → [ D ]
    on-arrows : ∀ {a b} → hom C a b → hom D (on-objects a) (on-objects b)
    respects-id : (a : [ C ]) → (on-arrows (id C a)) == (id D (on-objects a))
    respects-comp : ∀ {a b c} → (f : hom C a b) → (g : hom C b c ) →
                    (on-arrows (C :: g ∘ f )) == (D :: (on-arrows g) ∘ (on-arrows f))

_on-obj_ : ∀ {C D} → (Functor C D) → [ C ] → [ D ]
_on-obj_ F = Functor.on-objects F

_on-arr_ : ∀ {C D} → (F : Functor C D) → ∀ {x y} → (f : hom C x y) → hom D (F on-obj x) (F on-obj y)
_on-arr_ F f = Functor.on-arrows F f

open Functor
-- Definition of the identity functor for a given precategory A.
Identity-Functor : (A : Precategory) → (Functor A A)
Identity-Functor A = record
                       { on-objects = λ x → x
                       ; on-arrows = λ x₁ → x₁
                       ; respects-id = λ x → idp
                       ; respects-comp = λ f g → idp
                       }

-- Definition of Functor composition.
_*_ : {A B C : Precategory} (G : Functor B C) (F : Functor A B) → (Functor A C)
_*_  G F = record { on-objects = λ x → G on-obj (F on-obj x)
                   ; on-arrows = λ f →  G on-arr (F on-arr f)
                   ; respects-id = λ x → ap (λ f → G on-arr f) (respects-id F x) ∙ respects-id G ( F on-obj x)
                   ; respects-comp = λ f g → ap (λ f → G on-arr f) (respects-comp F f g) ∙ respects-comp G (F on-arr f) (F on-arr g) }

-- Given a functor F : A → B, we have that F * (Identity-Functor A) = F.
Id-Functor-Equality-Right : {A B : Precategory} (F : Functor A B) → ((F * (Identity-Functor A)) == F)
Id-Functor-Equality-Right F = idp

-- Given a functor F : A → B, we have (Identity-Functor B) * F = F.
Id-Functor-Equality-Left : {A B : Precategory} (F : Functor A B) → (((Identity-Functor B) * F) == F)
Id-Functor-Equality-Left record { on-objects = on-objects ; on-arrows = on-arrows ; respects-id = respects-id ; respects-comp = respects-comp } = {! !}

-- The part of a functor which assigns objects in one precategory to objects in another is associative.
Functor-on-obj-associativity : {A B C D : Precategory} (H : Functor C D) (G : Functor B C) (F : Functor A B) → (( on-objects H) after (( on-objects G) after ( on-objects F))) ==  (((on-objects H) after (on-objects G)) after  (on-objects F))
Functor-on-obj-associativity H G F = λ= λ x → idp

-- The part of a functor which assigns arrows in one precategory to arrows in another is associative.
Functor-on-arr-associativity : {A B C D : Precategory} (H : Functor C D) (G : Functor B C) (F : Functor A B) → (( on-objects H) after (( on-objects G) after ( on-objects F))) ==  (((on-objects H) after (on-objects G)) after  (on-objects F))
Functor-on-arr-associativity H G F = λ= λ x → idp

Functor-associativity : {A B C D : Precategory} (H : Functor C D) (G : Functor B C) (F : Functor A B) → ((H * (G * F)) == ((H * G) * F))
Functor-associativity H G F = {! !}

-- If F = F', and N is a natural transformation from F to G, then N is also a natural transformation from F' to G.

-- A Functor F is faithful if for all objects a b, the function F' : Hom(a, b) → Hom(Fa, Fb), such that for all f ∈ Hom(a, b), f ↦ F(f); is injective.
Is-Faithful : {A B : Precategory} (F : Functor A B) → Set₁
Is-Faithful {A} {B} F = (a b : obj A) → is-inj (on-arrows F {a} {b})

-- A functor is full if the above function is surjective.
Is-Full : {A B : Precategory} (F : Functor A B) → Set₁
Is-Full {A} {B} F = (a b : obj A) → is-surj (on-arrows F {a} {b})

-- A functor is fully faithful if it is full and faithful.
Is-Fully-Faithful : {A B : Precategory} (F : Functor A B) → Σ Set₁ (λ x → Set₁)
Is-Fully-Faithful F = (Is-Faithful F) , (Is-Full F)

Is-Essentially-Surjective : {A B : Precategory} (F : Functor A B) → Set₁
Is-Essentially-Surjective {A} {B} F = (b : obj B) → is-prop (Σ (obj A) λ a → (B ≅ (F on-obj a)) b)

-- Here we define the hom set functor. Currying Aᵒᵖ by Lemma 9.5.3 would yield the yoneda functor 𝒚 : A → 𝓢𝓮𝓽ᴬᵒᵖ.
hom-func : (A : Precategory) → Functor ((A ᵒᵖ) 𝓧 A) 𝓢𝓮𝓽
hom-func A = record
               { on-objects = λ { (a , b) → (hom A a b , homs-are-sets A a b) }
               ; on-arrows = λ { (f , f') → λ g → A :: (A :: f' ∘ g) ∘ f }
               ; respects-id = λ { (a , b) → ! (
                                       (λ g → g) =⟨ λ= (λ x → ! (∘-unit-l A)) ⟩
                            (λ g → (id A b) ⊚ g) =⟨ λ= (λ x → ! (∘-unit-r A)) ⟩
                 (λ g → ((id A b) ⊚ g) ⊚ id A a) =∎
                 )}
               ; respects-comp = λ { (g , g') (f , f') →
                 (λ h → ((f' ⊚ g') ⊚ h) ⊚ (g ⊚ f)) =⟨ λ= (λ x → ∘-assoc A) ⟩
                 (λ h → (((f' ⊚ g') ⊚ h) ⊚ g) ⊚ f) =⟨ λ= (λ x → ap (λ x₁ → (x₁ ⊚ g) ⊚ f) (! (∘-assoc A))) ⟩
                 (λ h → ((f' ⊚ (g' ⊚ h)) ⊚ g) ⊚ f) =⟨ λ= (λ x → ap (λ x₁ → x₁ ⊚ f) (! (∘-assoc A))) ⟩
                 (λ h → (f' ⊚ ((g' ⊚ h) ⊚ g)) ⊚ f) =∎
                 }
               }
               where
                 _⊚_ : ∀ {a b c} → (hom A b c) → (hom A a b) → hom A a c
                 g ⊚ f = (A :: g ∘ f)
