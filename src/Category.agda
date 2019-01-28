{-# OPTIONS --without-K --rewriting #-}

open import Agda.Primitive renaming (Level to ULevel)

open import lib.types.Sigma
open import lib.Basics renaming (_∘_ to _after_; ap3 to app3; ap4 to app4)

π₁ : {A : Set} {B : A → Set} → Σ A B → A
π₁ (fst , snd) = fst

π₂ : {A : Set} {B : A → Set} → (ab : Σ A B) → B (π₁ ab)
π₂ (fst , snd) = snd

record PreCategory : Set₁ where
    field
      Objects : Set
      Hom : (x y : Objects) → Set
      Homs-are-hsets : (x y : Objects) → has-level 0 (Hom x y)
      identity : (x : Objects) →  Hom x x
      _∘_ : {x y z : Objects} → (g : Hom y z) → (f : Hom x y)  → (Hom x z)
      equality_right : {x y : Objects} → (f : Hom x y) → (((identity y) ∘ f) == f)
      equality_left : {x y : Objects} → (f : Hom x y) →  ((f ∘ (identity x)) == f)
      composition : {x y z w : Objects} → (f : Hom x y) → (g : Hom y z) → (h : Hom z w) → ((h ∘ (g ∘ f)) == ((h ∘ g) ∘ f))

record is-iso (X : PreCategory) (x y : PreCategory.Objects X) (f : PreCategory.Hom X x y) : Set where
  open PreCategory X
  field
    g : (Hom y x)
    a : ( g ∘ f ) == (identity x)
    b : (f ∘ g) == (identity y)

module encode-decode {X : PreCategory} {x y : PreCategory.Objects X} {f : PreCategory.Hom X x y}  where
  open PreCategory X

  record is-iso-eq (i j : is-iso X x y f): Set where
    field
      fst-eq : (is-iso.g i == is-iso.g j)
      snd-eq : (transport (λ z → (z ∘ f) == (identity x)) fst-eq (is-iso.a i)) == (is-iso.a j)
      trd-eq : (transport (λ z → (f ∘ z) == (identity y)) fst-eq (is-iso.b i)) == (is-iso.b j)

  encode : (i j : is-iso X x y f) → (i == j) → is-iso-eq i j
  encode i .i idp = record { fst-eq = idp ; snd-eq = idp ; trd-eq = idp }

  decode : (i j : is-iso X x y f) → is-iso-eq i j → (i == j)
  decode record { g = g ; a = a ; b = b } record { g = .g ; a = .a ; b = .b } record { fst-eq = idp ; snd-eq = idp ; trd-eq = idp } = idp

module _ (X : PreCategory) where
  open PreCategory X
  open encode-decode

  ap3 : {x y z : Objects } (g g' : Hom x y) (f : Hom y z) (p : g == g') → ( (f ∘ g) == (f ∘ g'))
  ap3 g .g f idp = idp

  ap4 : {x y z : Objects} (g : Hom x y) (f f' : Hom y z) (p : f == f') → ((f ∘ g) == (f' ∘ g))
  ap4 g f .f idp = idp

  Lemma913a : (x y : Objects) (f : Hom x y) → has-all-paths (is-iso X x y f)
  Lemma913a x y f iso-f iso-f' = let g-eq-g' = Lemma1 x y f iso-f iso-f'
                                     g-f-eq-idx = has-level-apply (Homs-are-hsets x x) ((is-iso.g iso-f') ∘ f) (identity x)
                                     g-f-eq-idy = has-level-apply (Homs-are-hsets y y) (f ∘ (is-iso.g iso-f')) (identity y) in
                decode iso-f iso-f'
                 (record { fst-eq = g-eq-g';
                           snd-eq = prop-has-all-paths {{g-f-eq-idx}} (transport (λ a → (a ∘ f) == (identity x)) g-eq-g' (is-iso.a iso-f)) (is-iso.a iso-f') ;
                           trd-eq = prop-has-all-paths {{g-f-eq-idy}} (transport (λ a → (f ∘ a) == (identity y)) g-eq-g' (is-iso.b iso-f)) (is-iso.b iso-f') })
    where
      Lemma1 : (x y : Objects ) (f : Hom x y) (i j : is-iso X x y f) → is-iso.g i == is-iso.g j
      Lemma1  x y f i j = ! (equality_right (is-iso.g i)) ∙ (ap4 (is-iso.g i) (identity x) (is-iso.g j ∘ f) (! (is-iso.a j)) ∙ (! (composition (is-iso.g i) f (is-iso.g j))  ∙ (ap3 (f ∘ is-iso.g i) (identity y) (is-iso.g j) (is-iso.b i) ∙ equality_left (is-iso.g j))))


  Lemma913a' : (x y : Objects) (f : Hom x y) → has-level (-1) (is-iso X x y f)
  Lemma913a' x y f = all-paths-is-prop (Lemma913a x y f)

  _≅_ : Objects → Objects → Set
  _≅_ a b = Σ (Hom a b) (is-iso X a b)

  Lemma913b : (a b : Objects) → has-level 0 (a ≅ b)
  Lemma913b a b = Σ-level (Homs-are-hsets a b) (λ x → raise-level -1 (Lemma913a' a b x))

  idtoiso : (a b : Objects) → (p : a == b) → a ≅ b
  idtoiso a .a idp = record{fst = identity a ; snd = record{g = identity a ; a = equality_right (identity a) ; b = equality_right (identity a)}}

