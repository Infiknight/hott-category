
open import Naturals
open import Equality
open import SetsandPropositionsSolutions


--data Hom {Objects : Set} (x y : Objects) : Set


record PreCategory : Set₁ where
    field
      Objects : Set
      Hom : (x y : Objects) → Set
      Homs-are-hsets : {x y : Objects} → is-hset(Hom x y)
      identity : (x : Objects) →  Hom x x
      _∘_ : {x y z : Objects} → (g : Hom y z) → (f : Hom x y)  → (Hom x z)
      equality_right : {x y : Objects} → (f : Hom x y) → (((identity y) ∘ f) == f)
      equality_left : {x y : Objects} → (f : Hom x y) →  ((f ∘ (identity x)) == f)
      composition : {x y z w : Objects} → (f : Hom x y) → (g : Hom y z) → (h : Hom z w) → ((h ∘ (g ∘ f))== ((h ∘ g) ∘ f))


--test = Category Set (λ t₁ t₂ → (t₁ → t₂))
--postulate Homs-are-hsets : {X : PreCategory} {x y : PreCategory.Objects X} → is-hset(PreCategory.Hom X x y)

record is-iso (X : PreCategory) (x y : PreCategory.Objects X)  (f : PreCategory.Hom X x y) : Set where
  open PreCategory X
  field
    g : (Hom y x)
    a : ( g ∘ f ) == (identity x)
    b : (f ∘ g) == (identity y)

module _ (X : PreCategory) where
  open PreCategory X

  ap3 : {x y z : Objects } (g g' : Hom x y) (f : Hom y z) (p : g == g') → ( (f ∘ g) == (f ∘ g'))
  ap3 g .g f idp = idp

  ap4 : {x y z : Objects} (g : Hom x y) (f f' : Hom y z) (p : f == f') → ((f ∘ g) == (f' ∘ g))
  ap4 g f .f idp = idp
 

  
  Lemma913a : {x y : Objects} (f : Hom x y) → is-hprop(is-iso X x y f)
  Lemma913a f x y = {!!}
    where
      Lemma1 : (x y : Objects ) (f : Hom x y) (i j : is-iso X x y f) → is-iso.g i == is-iso.g j
      Lemma1  x y f i j = ! (equality_right (is-iso.g i)) ∙ (ap4 (is-iso.g i) (identity x) (is-iso.g j ∘ f) (! (is-iso.a j)) ∙ (! (composition (is-iso.g i) f (is-iso.g j))  ∙ (ap3 (f ∘ is-iso.g i) (identity y) (is-iso.g j) (is-iso.b i) ∙ equality_left (is-iso.g j))))
      Lemma2 : (x y : Objects) (f : Hom x y) (i j : is-iso X x y f) → is-iso.a i == is-iso.a i
      Lemma2 x y f i j = {!!}
      
      



{-Lemma2 : (X : PreCategory) (x y : PreCategory.Objects X) (f : PreCategory.Hom X x y) (i j : is-iso X x y f) → is-iso.a i == is-iso.a j
    Lemma2 X x y f i j = {!!}


-}
    

{-
idtoiso : (X : PreCategory) (x y : PreCategory.Objects X) → (p : x == y) → Set
idtoiso X x .x idp = is-iso X x x (identity x) 
  where
    open PreCategory X


is-Category : (X : PreCategory) → Set
is-Category X = (x y : Objects)  → is-equiv (idtoiso X x y)
  where
    open PreCategory X
-}
