{-# OPTIONS --without-K --rewriting --type-in-type #-}

-- We rename some common symbols to reserve them for operations on morphisms.
open import Agda.Primitive renaming (Level to ULevel)
open import lib.Base renaming (_∘_ to _after2_)
open import lib.types.Sigma
open import lib.Basics renaming (_∘_ to _after_; _⁻¹ to inv)
open import Category

-- In this file we prove a number of lemma's on identities regarding isomorphisms and paths.
-- In particular we show that a ≅ b is a set for any objects a, b in a given category A, that
-- thus ob(A) is a 1-type, and that equations 9.1.10 through 9.1.13 hold.

-- Before proceeding we fix a category C.
module _ (C : Category) where
  open Category.Category C
  open Precategory PC
  open Isomorphisms PC

  -- Lemma 9.1.3 contains the secondary statement that the type a ≅ b is a set, which we dub Lemma 9.1.3.b.
  Lemma913b : (a b : [ PC ]) → has-level 0 (a ≅ b)
  Lemma913b a b = Σ-level (homs-are-sets a b) (λ x → raise-level -1 (Lemma913a a b x))

  -- From the category's equivalence statement we distill idtoiso's inverse (as defined in Category.agda).
  isotoid : {a b : ob} → a ≅ b → a == b
  isotoid {a} {b} = is-equiv.g idtoiso-is-equiv

  -- Lemma 9.1.8. follows directly from Lemma 9.1.3.b and the fact that equivalences preserve levels.
  -- The fact that (a ≅ b) ≃ (a == b) is immediate from the definition of a category and the definition of isotoid.
  Lemma918 : {a b : ob} → has-level 1 ob
  Lemma918 {a} {b} = has-level-in (λ a b → equiv-preserves-level (Lemma) {{(Lemma913b a) b}})
    where
      Lemma : ∀ {a b} → (a ≅ b) ≃ (a == b)
      Lemma = isotoid , is-equiv-inverse idtoiso-is-equiv

  -- To make lemma919i more readable we first introduce a simple type family.
  P : ob × ob → Set₁
  P (a , b) = hom a b

  -- Next we use this to show the desired equality (9.1.10).
  -- N.B. the book keeps the notation informal and alternates between using ∘ to denote morphism composition
  -- and isomorphism composition. There is a subtle difference in that isomorphisms are morphisms paired with
  -- certain witnesses. In our proofs we distinguish between the two by writing ∘ᵢ when we are composing isomorphisms.
  Lemma919i : ∀ {a b a' b'} (f : hom a b) (p : a == a') (q : b == b') → (transport P (pair×= p q) f) == (((π₁ (idtoiso q)) ∘ f) ∘ π₁ (idtoiso p ⁻¹))
  {- Using path induction on p and q the goal reduces via normalization to
                f = (id b) ∘ f ∘ (id a),
     hence the following equational reasoning.
  -}
  Lemma919i {a} {b} {.a} {.b} f idp idp = f =⟨ ! ∘-unit-l ⟩
                                   id b ∘ f =⟨ ! ∘-unit-r ⟩
                          (id b ∘ f) ∘ id a =∎

  -- Next we prove 9.1.11 by a simple induction on paths, and our lemma on morphism equality.
  Lemma919ii : ∀ {a b} (p : a == b) → idtoiso (! p) == (idtoiso p ⁻¹)
  Lemma919ii idp = mor-eq-is-iso-eq (idtoiso idp) (idtoiso idp ⁻¹) idp

  -- A very similar argument suffices for 9.1.12, but note the use of ∘ᵢ.
  Lemma919iii : ∀ {a b c} (p : a == b) (q : b == c) → idtoiso (p ∙ q) == (idtoiso p ∘ᵢ idtoiso q)
  Lemma919iii idp idp = mor-eq-is-iso-eq (idtoiso idp) (idtoiso idp ∘ᵢ idtoiso idp) (! ∘-unit-l)

  -- For 9.1.13 we use equational reasoning an application of equation 9.1.12 (note also that this again concerns isomorphism composition).
  Lemma919iv : ∀ {a b c} (fi : a ≅ b) (ei : b ≅ c) → isotoid (fi ∘ᵢ ei) == (isotoid fi ∙ isotoid ei)
  Lemma919iv fi ei =                   (isotoid (fi ∘ᵢ ei)) =⟨ ap (λ x → isotoid (x ∘ᵢ ei)) (! (is-equiv.f-g idtoiso-is-equiv fi)) ⟩
                       isotoid (idtoiso (isotoid fi) ∘ᵢ ei) =⟨ ap (λ x → isotoid (idtoiso (isotoid fi) ∘ᵢ x)) (! (is-equiv.f-g idtoiso-is-equiv ei)) ⟩
     isotoid (idtoiso (isotoid fi) ∘ᵢ idtoiso (isotoid ei)) =⟨ ap isotoid (! (Lemma919iii (isotoid fi) (isotoid ei))) ⟩
                isotoid (idtoiso (isotoid fi ∙ isotoid ei)) =⟨ is-equiv.g-f idtoiso-is-equiv (isotoid fi ∙ isotoid ei) ⟩
                                    isotoid fi ∙ isotoid ei =∎
