{-# OPTIONS --without-K #-}

open import lib.Naturals
open import lib.Equality
open import lib.SetsandPropositionsSolutions

open import Agda.Primitive renaming (Level to ULevel)

record PreCategory : Set₁ where
    field
      Objects : Set
      Hom : (x y : Objects) → Set
      Homs-are-hsets : (x y : Objects) → is-hset(Hom x y)
      identity : (x : Objects) →  Hom x x
      _∘_ : {x y z : Objects} → (g : Hom y z) → (f : Hom x y)  → (Hom x z)
      equality_right : {x y : Objects} → (f : Hom x y) → (((identity y) ∘ f) == f)
      equality_left : {x y : Objects} → (f : Hom x y) →  ((f ∘ (identity x)) == f)
      composition : {x y z w : Objects} → (f : Hom x y) → (g : Hom y z) → (h : Hom z w) → ((h ∘ (g ∘ f))== ((h ∘ g) ∘ f))


--test = Category Set (λ t₁ t₂ → (t₁ → t₂))
--postulate Homs-are-hsets : {X : PreCategory} {x y : PreCategory.Objects X} → is-hset(PreCategory.Hom X x y)

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
      snd-eq : (transport {Hom y x} (λ z → (z ∘ f) == (identity x)) fst-eq (is-iso.a i)) == (is-iso.a j)
      trd-eq : (transport {Hom y x} (λ z → (f ∘ z) == (identity y)) fst-eq (is-iso.b i)) == (is-iso.b j)

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


  Lemma913a : (x y : Objects) (f : Hom x y) → is-hprop(is-iso X x y f)
  Lemma913a x y f iso-f iso-f' = let g-eq-g' = Lemma1 x y f iso-f iso-f'
                                     g-f-eq-idx = (Homs-are-hsets x x) ((is-iso.g iso-f') ∘ f) (identity x)
                                     g-f-eq-idy = (Homs-are-hsets y y) (f ∘ (is-iso.g iso-f')) (identity y) in
                decode iso-f iso-f'
                 (record { fst-eq = g-eq-g';
                           snd-eq = g-f-eq-idx (transport (λ a → (a ∘ f) == (identity x)) g-eq-g' (is-iso.a iso-f)) (is-iso.a iso-f') ;
                           trd-eq = g-f-eq-idy (transport (λ a → (f ∘ a) == (identity y)) g-eq-g' (is-iso.b iso-f)) (is-iso.b iso-f') })
    where
      Lemma1 : (x y : Objects ) (f : Hom x y) (i j : is-iso X x y f) → is-iso.g i == is-iso.g j
      Lemma1  x y f i j = ! (equality_right (is-iso.g i)) ∙ (ap4 (is-iso.g i) (identity x) (is-iso.g j ∘ f) (! (is-iso.a j)) ∙ (! (composition (is-iso.g i) f (is-iso.g j))  ∙ (ap3 (f ∘ is-iso.g i) (identity y) (is-iso.g j) (is-iso.b i) ∙ equality_left (is-iso.g j))))

      --Lemma2 : (x y : Objects) (f : Hom x y) (i j : is-iso X x y f)


  _≅_ : Objects → Objects → Set
  _≅_ a b = Σ (Hom a b) (is-iso X a b)

  Lemma913b : (a b : Objects) → is-hset (a ≅ b)
  Lemma913b a b = all-hprops-are-hsets λ x y → {! !}


  idtoiso : (a b : Objects) → (p : a == b) → a ≅ b
  idtoiso a .a idp = record{fst = identity a ; snd = record{g = identity a ; a = equality_right (identity a) ; b = equality_right (identity a)}}



is-Category : (X : PreCategory) → Set
is-Category X = (x y : PreCategory.Objects X)  → is-equiv (idtoiso X x y)

{-
record Functor : Set₁ where
  field
    source : PreCategory
    target : PreCategory
    F-objects : (x : PreCategory.Objects source) → PreCategory.Objects target
    F-arrows : {x y : PreCategory.Objects source} (f : PreCategory.Hom source x y) → (PreCategory.Hom target (F-objects x) (F-objects y))
    F-identity : (x : PreCategory.Objects source) → (F-arrows (PreCategory.identity source x) == PreCategory.identity target (F-objects x))
    F-composition : {x y z : PreCategory.Objects source} (f : PreCategory.Hom source x y) (g : PreCategory.Hom source y z) → F-arrows (PreCategory._∘_ source g f) == PreCategory._∘_ target (F-arrows g) (F-arrows f)

record natural-transformation (F G : Functor) : Set₁ where
  field
    source-identity : Functor.source F == Functor.source G
    target-identity : Functor.target F == Functor.target G

-}
record Functor (C D : PreCategory) : Set  where
  field
    F-objects : (x : PreCategory.Objects C) → PreCategory.Objects D
    F-arrows : {x y : PreCategory.Objects C} (f : PreCategory.Hom C x y) → (PreCategory.Hom D (F-objects x) (F-objects y))
    F-identity : (x : PreCategory.Objects C) → (F-arrows (PreCategory.identity C x) == PreCategory.identity D (F-objects x))
    F-composition : {x y z : PreCategory.Objects C} (f : PreCategory.Hom C x y) (g : PreCategory.Hom C y z) → F-arrows (PreCategory._∘_ C g f) == PreCategory._∘_ D (F-arrows g) (F-arrows f)

record natural-transformation {C D : PreCategory} (F : Functor C D) (G : Functor C D) : Set  where
  field
    component : (x : PreCategory.Objects C) → PreCategory.Hom D (Functor.F-objects F x) (Functor.F-objects G x)
    naturality : {x y : PreCategory.Objects C} (f : PreCategory.Hom C x y) →
                  PreCategory._∘_ D (Functor.F-arrows G f ) (component x ) == PreCategory._∘_ D (component y) (Functor.F-arrows F f)

open natural-transformation
functor-PreCategory : (A B : PreCategory) → PreCategory
functor-PreCategory A B = record
                            { Objects =   Functor A B
                            ; Hom = λ F G → natural-transformation F G
                            ; Homs-are-hsets = {! !}
                            ; identity = λ F → record{component = λ x → PreCategory.identity B (Functor.F-objects F x) ; naturality = λ f → PreCategory.equality_left B (Functor.F-arrows F f) ∙ ! (PreCategory.equality_right B (Functor.F-arrows F f))}
                            ; _∘_ = λ g f → record { component = λ x → PreCategory._∘_ B (component g x) (component f x) ;
                                naturality = λ h → {!   !} }
                            ; equality_right = {! !}
                            ; equality_left = {! !}
                            ; composition = {! !}
                            }
