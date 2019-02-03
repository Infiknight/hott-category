{-# OPTIONS --without-K --rewriting --type-in-type #-}

-- We rename some common symbols to reserve them for operations on morphisms.
open import lib.Basics renaming (_∘_ to _after_;  _⁻¹ to inv)
open import lib.types.Sigma
open import lib.types.Pi

module Category where

-- Small workaround, ignore this module. 
module _ where
  -- Some definition of projection functions of product types. 
  pr₁ : {A B : Set} → A × B → A
  pr₁ (a , b) = a
  pr₂ : {A B : Set} → A × B → B
  pr₂ (a , b) = b
  π₁ : {A : Set₁} {B : A → Set₁} → Σ A B → A
  π₁ (fst , snd) = fst
  π₂ : {A : Set₁} {B : A → Set₁} → (ab : Σ A B) → B (π₁ ab)
  π₂ (fst , snd) = snd

  -- A definition of a Precategory, in accordance with Definition 9.1.1.
  record Precategory : Set₂ where
    field
      ob : Set₁
      hom : (x y : ob) → Set₁
      id : ∀ x → hom x x
      homs-are-sets :  ∀ x y → is-set (hom x y)
      _∘_ : ∀ {x y z} → (hom y z) → (hom x y)  → (hom x z)
      ∘-unit-l : ∀ {x y} {f : hom x y} → (id y ∘ f) == f
      ∘-unit-r : ∀ {x y} {f : hom x y} → (f ∘ id x) == f
      ∘-assoc : ∀ {x y z w} {f : hom x y} {g : hom y z} {h : hom z w} → (h ∘ (g ∘ f)) == ((h ∘ g) ∘ f)

  -- The definition of a category (as opposed to a precategory) involves the concept of
  -- isomorphims between objects in a category. Hence we first open a module to
  -- develop these concepts before continuing to with this definition.
  module Isomorphisms (A : Precategory) where
    open Precategory A

    -- A record type containing the data witnessing the fact that an arrow f
    -- is an isomorphism, as described in Definition 9.1.2.
    record is-iso {x y : ob} (f : hom x y) : Set₁ where
      field
        g : (hom y x)
        a : (g ∘ f) == (id x)
        b : (f ∘ g) == (id y)

    -- Since is-iso is a kind of dependent pair type we require an encode-decode
    -- method to show that two instances of this type are equal. 
    module encode-decode {x y : ob} {f : hom x y} where
      record is-iso-eq (i j : is-iso f): Set₁ where
        field
          fst-eq : (is-iso.g i == is-iso.g j)
          snd-eq : (transport (λ z → (z ∘ f) == (id x)) fst-eq (is-iso.a i)) == (is-iso.a j)
          trd-eq : (transport (λ z → (f ∘ z) == (id y)) fst-eq (is-iso.b i)) == (is-iso.b j)

      -- The required maps are easily constructed using path induction.
      encode : (i j : is-iso f) → (i == j) → is-iso-eq i j
      encode i .i idp = record { fst-eq = idp ; snd-eq = idp ; trd-eq = idp }
      decode : (i j : is-iso f) → is-iso-eq i j → (i == j)
      decode record { g = g ; a = a ; b = b } record { g = .g ; a = .a ; b = .b } record { fst-eq = idp ; snd-eq = idp ; trd-eq = idp } = idp

    -- Next we will use this encode-decode method to prove Lemma9.1.3. 
    open encode-decode

    -- First we abbreviate the pre- and post-composition functions.
    _∘─ : ∀ {a b c} (f : hom b c) → hom a b → hom a c
    f ∘─ = λ g → f ∘ g
    ─∘_ : ∀ {a b c} (f : hom a b) → hom b c → hom a c
    ─∘ f = λ g → g ∘ f

    -- Next we show that 'is-iso has all paths', as this is equivalent to saying it has level -1. 
    Lemma913a' : {x y : ob} (f : hom x y) → has-all-paths (is-iso f)
    Lemma913a' {x} {y} f iso-f iso-f' = let g-eq-g' = Lemma x y f iso-f iso-f'
                                            g-f-eq-idx = has-level-apply (homs-are-sets x x) ((is-iso.g iso-f') ∘ f) (id x)
                                            g-f-eq-idy = has-level-apply (homs-are-sets y y) (f ∘ (is-iso.g iso-f')) (id y) in
                   decode iso-f iso-f'
                   (record { fst-eq = g-eq-g';
                             snd-eq = prop-has-all-paths {{g-f-eq-idx}} (transport (λ a → (a ∘ f) == (id x)) g-eq-g' (is-iso.a iso-f)) (is-iso.a iso-f') ;
                             trd-eq = prop-has-all-paths {{g-f-eq-idy}} (transport (λ a → (f ∘ a) == (id y)) g-eq-g' (is-iso.b iso-f)) (is-iso.b iso-f') })
               where
                 Lemma : (x y : ob ) (f : hom x y) (i j : is-iso f) → is-iso.g i == is-iso.g j
                 Lemma  x y f i j = ! (∘-unit-l) ∙ (ap (─∘ (is-iso.g i)) (! (is-iso.a j)) ∙ (! (∘-assoc)  ∙ (ap ((is-iso.g j) ∘─) (is-iso.b i) ∙ ∘-unit-r)))

    -- Now obtaining the lemma is a simple application of applying this equivalence. 
    Lemma913a : (x y : ob) (f : hom x y) → has-level (-1) (is-iso f)
    Lemma913a x y f = all-paths-is-prop (Lemma913a' f)

    -- The type of identity morphisms is akin to equivalences in the type universe:
    -- an isomorphism is a morphism dependently paired with a witness of this property. 
    _≅_ : ob → ob → Set₁
    _≅_ a b = Σ (hom a b) is-iso

    -- If two isomorphisms have equal underlying morphisms then they are equal as isomorphisms.
    -- This is because 'begin an isomorphism' is a mere proposition.
    mor-eq-is-iso-eq : ∀ {a b} (f₁ f₂ : a ≅ b) → (π₁ f₁ == π₁ f₂) → f₁ == f₂
    mor-eq-is-iso-eq (f , f-is-iso₁) (.f , f-is-iso₂) idp = pair= idp (Lemma913a' f f-is-iso₁ f-is-iso₂)

    -- Defining the inverse operation on isomorphisms.
    _⁻¹ : ∀ {a b} → (a ≅ b) → (b ≅ a)
    (f , f-is-iso) ⁻¹ = is-iso.g f-is-iso , record { g = f ;
                                                     a = is-iso.b f-is-iso ;
                                                     b = is-iso.a f-is-iso }

    -- Composing an isomorphism with its inverse yields the identity morphism.
    ⁻¹-r-cancel : ∀ {a b} (fi : a ≅ b) → (π₁ fi ∘ π₁ (fi ⁻¹)) == (id b)
    ⁻¹-r-cancel fi = is-iso.b (π₂ fi)
    ⁻¹-l-cancel : ∀ {a b} (fi : a ≅ b) → (π₁ (fi ⁻¹) ∘ π₁ fi) == (id a)
    ⁻¹-l-cancel fi = is-iso.a (π₂ fi)

    -- A concatenation operation for isomorphisms, but with the input output position reversed...
    _∘ᵢ_ : ∀ {a b c} → a ≅ b → b ≅ c → a ≅ c
    _∘ᵢ_ {a} {b} {c} fi gi = (g ∘ f) , record {
      g = f⁻¹ ∘ g⁻¹ ;
      a = (f⁻¹ ∘ g⁻¹) ∘ (g ∘ f) =⟨ ∘-assoc ⟩
          ((f⁻¹ ∘ g⁻¹) ∘ g) ∘ f =⟨ ap (─∘ f) (! ∘-assoc) ⟩
          (f⁻¹ ∘ (g⁻¹ ∘ g)) ∘ f =⟨ ap (λ x → ((f⁻¹ ∘ x) ∘ f)) (⁻¹-l-cancel gi) ⟩
               (f⁻¹ ∘ id b) ∘ f =⟨ ap (─∘ f) ∘-unit-r ⟩
                        f⁻¹ ∘ f =⟨ ⁻¹-l-cancel fi ⟩
                           id a =∎ ;        
      b = (g ∘ f) ∘ (f⁻¹ ∘ g⁻¹) =⟨ ∘-assoc ⟩
          ((g ∘ f) ∘ f⁻¹) ∘ g⁻¹ =⟨ ap (─∘ g⁻¹) (! ∘-assoc) ⟩
          (g ∘ (f ∘ f⁻¹)) ∘ g⁻¹ =⟨ ap (λ x → ((g ∘ x) ∘ g⁻¹)) (⁻¹-r-cancel fi)⟩
               (g ∘ id b) ∘ g⁻¹ =⟨ ap (─∘ g⁻¹) ∘-unit-r ⟩
                        g ∘ g⁻¹ =⟨ ⁻¹-r-cancel gi ⟩
                           id c =∎
      }
      where
        f : hom a b
        f = π₁ fi
        f⁻¹ : hom b a
        f⁻¹ = π₁ (fi ⁻¹)
        g : hom b c
        g = π₁ gi
        g⁻¹ : hom c b
        g⁻¹ = π₁ (gi ⁻¹)

    -- It is easy to show that identity morphisms are isomorphisms. 
    id-iso : (a : ob) → a ≅ a
    id-iso a  = ((id a) , (record { g = id a ; a = ∘-unit-l ; b = ∘-unit-l }))

    -- Using the aforementioned fact with path induction we show that identities
    -- give rise to isomorphisms; this map is called idtoiso in accordance with Lemma 9.1.4. 
    -- A category is a precategory in which this map is an equivalence of types.
    Lemma914 : {a b : ob} → a == b → a ≅ b
    Lemma914 {a} {.a} idp = id-iso a
    idtoiso : {a b : ob} → a == b → a ≅ b
    idtoiso = Lemma914

  -- Defining the precategory of all sets as per Example 9.1.5.
  -- We have tried different ways to define hom for this category but
  -- ran into persistent type level related errors, so ultimately we
  -- decided to start using type-in-type rather than going back and editing
  -- type level information into our definitions.
  𝓢𝓮𝓽 : Precategory
  𝓢𝓮𝓽 = record { ob = Σ Set (is-set)
                          ; hom = λ x y → (π₁ x) → (π₁ y)
                          ; id = λ x x₁ → x₁
                          ; homs-are-sets = Lem
                          ; _∘_ = λ f g → f after g
                          ; ∘-unit-l = idp   
                          ; ∘-unit-r = idp   
                          ; ∘-assoc = idp    }
                            where
                              Lem : (a b : Σ Set (is-set)) → has-level 0 (π₁ a → π₁ b)
                              Lem (fst₁ , snd₁) (fst₂ , snd₂) = Π-level (λ x → has-level-in (λ x₁ y → has-level-apply-instance {{snd₂}}))

  -- Having defined precategories and the map idtoiso we can define categories
  -- in accordance with Definition 9.1.6.
  record Category : Set₂ where
    field
      PC : Precategory
    open Isomorphisms PC
    open Precategory PC
    field
      idtoiso-is-equiv : ∀ {a b} → is-equiv (idtoiso {a} {b})

  -- We conclude this document with some syntactic sugar and constructions on categories. 
  module _ where
    open Precategory

    -- An alternative syntax for the objects of a precategory. 
    obj : Precategory → Set₁
    obj = ob
    syntax obj C = [ C ]

    -- An alternative notation of the composition of two arrows in a precategory. 
    _::_∘_ : (C : Precategory) → ∀ {x y z} → (hom C y z) → (hom C x y) → (hom C x z)
    C :: g ∘ f = _∘_ C g f

    -- Definition 9.5.1 of the opposite category. 
    _ᵒᵖ : (A : Precategory) → Precategory
    A ᵒᵖ = record
             { ob = [ A ]
             ; hom = λ a b → hom A b a
             ; id = id A
             ; homs-are-sets = λ a b → homs-are-sets A b a
             ; _∘_ = λ a b → A :: b ∘ a
             ; ∘-unit-l = ∘-unit-r A
             ; ∘-unit-r = ∘-unit-l A
             ; ∘-assoc = ! (∘-assoc A)
             } 

    -- Definition 9.5.2 of a product of categories.
    _x_ : (A B : Precategory) → Precategory
    A x B = record
              { ob = [ A ] × [ B ]
              ; hom = λ { (a , b) (a' , b') → hom A a a' × hom B b b' }
              ; id = λ { (a , b) → (id A a , id B b) }
              ; homs-are-sets = λ { (a , b) (a' , b') → ×-level (homs-are-sets A a a') (homs-are-sets B b b') }
              ; _∘_ = λ { (f , g) (f' , g') → ((A :: f ∘ f') , (B :: g ∘ g')) }
              ; ∘-unit-l = pair×= (∘-unit-l A) (∘-unit-l B)
              ; ∘-unit-r = pair×= (∘-unit-r A) (∘-unit-r B)
              ; ∘-assoc = pair×= (∘-assoc A) (∘-assoc B)
              }
