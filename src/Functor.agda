{-# OPTIONS --without-K --rewriting #-}
{-# OPTIONS --allow-unsolved-metas #-}
open import lib.Basics renaming (_∘_ to _after_)
open import Precategory
open import lib.Function2
open import PropositionsAsTypes
open import Category

record Functor (C D : Precategory) : Set₁  where
  field
    on-objects : [ C ] → [ D ]
    on-arrows : ∀ {x y} → hom C x y → hom D (on-objects x) (on-objects y)
    respects-id : (x : [ C ]) → (on-arrows (id-on {C} x)) == (id-on {D} (on-objects x))
    respects-comp : ∀ {x y z} → (f : hom C x y) → (g : hom C y z ) →
                    (on-arrows (C :: g ∘ f )) == (D :: (on-arrows g) ∘ (on-arrows f))

-- The part of a functor that assigns objects in one precategory to objects in another.
_on-obj_ : ∀ {C D} → Functor C D → [ C ] → [ D ]
_on-obj_ F x = Functor.on-objects F x

-- The part of a functor that assigns arrows in one precategory to arrows in another.
_on-arr_ : ∀ {C D} (F : Functor C D) → {x y : [ C ]} → (f : hom C x y) → hom D (F on-obj x) (F on-obj y)
_on-arr_ F f = Functor.on-arrows F f

-- Definition of the identity functor for a given precategory A.
Identity-Functor : (A : Precategory) → (Functor A A)
Identity-Functor A = record
                       { on-objects = λ x → x
                       ; on-arrows = λ x₁ → x₁
                       ; respects-id = λ x → idp
                       ; respects-comp = λ f g → idp
                       }




record Natural-transformation {C D : Precategory} (F G : Functor C D) : Set₁  where
   field
     component : (x : [ C ]) → hom D (F on-obj x) (G on-obj x)
     naturality : ∀ {x y} → (f : hom C x y) →
                  (D :: (G on-arr f) ∘ (component x)) == (D :: (component y) ∘ (F on-arr f))

open Functor
open Natural-transformation

_at_ : ∀ {C D} {F G : Functor C D} → (Natural-transformation F G) → (x : [ C ]) → hom D (F on-obj x) (G on-obj x)
_at_ = component

-- Definition of the identity natural transformation which assigns each object x, the identity arrow of x.
nat-tr-id : ∀ {C D} (F : Functor C D) → Natural-transformation F F
nat-tr-id {C} {D} F = record { component = λ x → id-on {D} (F on-obj x) ; naturality = λ F → Precategory.∘-unit-r D ∙ ! (Precategory.∘-unit-l D) }

nat-tr-comp : ∀ {C D} { F G H : Functor C D} → Natural-transformation F G → Natural-transformation G H → Natural-transformation F H
nat-tr-comp {C} {D} {F} {G} {H} α β =
  record { component = λ x → D :: (β at x) ∘ (α at x) ;
           naturality = λ {x} {y} f → {! ap (λ h → D :: (β at y) ∘ h) (naturality α f) !} }



functor-precategory : (A B : Precategory) → Precategory
functor-precategory A B = record { objects = Functor A B
                                  ; arrows = λ F G → Natural-transformation F G
                                  ; id-arrow = nat-tr-id
                                  ; homs-are-hsets = {!   !}
                                  ; _∘_ = λ α β → record { component = λ x → B :: (α at x) ∘ (β at x) ;
                                                           naturality = λ f → {!   !} }
                                  ; ∘-unit-l = {!   !}
                                  ; ∘-unit-r = {!   !}
                                  ; assoc = {!   !} }


-- Definition of Functor composition.
_*_ : {A B C : Precategory} (G : Functor B C) (F : Functor A B) → (Functor A C)
_*_  G F = record
                             { on-objects = λ x → G on-obj (F on-obj x) 
                             ; on-arrows = λ f →  G on-arr (F on-arr f)
                             ; respects-id = λ x → ap (λ f → G on-arr f) (respects-id F x) ∙ respects-id G ( F on-obj x)
                             ; respects-comp = λ f g → ap (λ f → G on-arr f) (respects-comp F f g) ∙ respects-comp G (F on-arr f) (F on-arr g)
                             }


-- Given a functor F : A → B, we have that F * (Identity-Functor A) = F.
Id-Functor-Equality-Right : {A B : Precategory} (F : Functor A B) → ((F * (Identity-Functor A)) == F)
Id-Functor-Equality-Right F = idp

-- Given a functor F : A → B, we have (Identity-Functor B) * F = F.
Id-Functor-Equality-Left : {A B : Precategory} (F : Functor A B) → (((Identity-Functor B) * F) == F)
Id-Functor-Equality-Left record { on-objects = on-objects ; on-arrows = on-arrows ; respects-id = respects-id ; respects-comp = respects-comp } = {!!}

-- Given functors F : A → B and G, H : B → C and natural transformation N : G → H, we define the left-composite as the natural transformation from G * F to H * F,
-- given by, for each object a : A, we have the component N(Fa).
left-composite : {A B C : Precategory} (F : Functor A B) (G H : Functor B C) (N : Natural-transformation G H) → (Natural-transformation (G * F) (H * F))
left-composite F G H N = record { component = λ x → N at (F on-obj x) ; naturality = λ f → naturality N (F on-arr f) }

-- Given functors G, H : B → C and K : C → D and natural transformation N : G → H, we define the right composite as the natural tranformation from K * G to K * H,
-- given by, for object b : B, we have the component K(Nb).
right-composite : {B C D : Precategory} (G H : Functor B C) (K : Functor C D) (N : Natural-transformation G H)  → (Natural-transformation (K * G) (K * H))
right-composite G H K N = record { component = λ x → K on-arr (component N x) ; naturality = λ {x} {y} f →  (! (respects-comp K (component N x) (H on-arr f)) ∙ ap (_on-arr_ K) (naturality N f)) ∙ respects-comp K (G on-arr f) (component N y)}

-- The part of a functor which assigns objects in one precategory to objects in another is associative.
Functor-on-obj-associativity : {A B C D : Precategory} (H : Functor C D) (G : Functor B C) (F : Functor A B) → (( on-objects H) after (( on-objects G) after ( on-objects F))) ==  (((on-objects H) after (on-objects G)) after  (on-objects F))
Functor-on-obj-associativity H G F = λ= λ x → idp

-- The part of a functor which assigns arrows in one precategory to arrows in another is associative.
Functor-on-arr-associativity : {A B C D : Precategory} (H : Functor C D) (G : Functor B C) (F : Functor A B) → (( on-objects H) after (( on-objects G) after ( on-objects F))) ==  (((on-objects H) after (on-objects G)) after  (on-objects F))
Functor-on-arr-associativity H G F = λ= λ x → idp


Functor-associativity : {A B C D : Precategory} (H : Functor C D) (G : Functor B C) (F : Functor A B) → ((H * (G * F)) == ((H * G) * F))
Functor-associativity H G F = {!!}



-- If F = F', and N is a natural transformation from F to G, then N is also a natural transformation from F' to G.
Nat-tr-comp-path-initial : {A B : Precategory} {F G F' : Functor A B} (N : Natural-transformation F G) (p : F == F') → (Natural-transformation F' G)
Nat-tr-comp-path-initial N idp = N

-- If G = G' and N is a natural transformation from F to G, then N is also a natural transformation from F to G'.
Nat-tr-comp-path-end : {A B : Precategory} {F G G' : Functor A B} (N : Natural-transformation F G) (p : G == G') → (Natural-transformation F G')
Nat-tr-comp-path-end N idp = N

-- If N is a natural transformation from F to G, and M is a natural transformation from H to I, and G = H, then we can compose the two to get a natural transformation from F to I.
Nat-tr-comp-path-middle : {A B : Precategory} {F G H I : Functor A B} (N : Natural-transformation F G) (M : Natural-transformation H I) (p : G == H) → (Natural-transformation F I)
Nat-tr-comp-path-middle N M idp = nat-tr-comp N M



-- A Functor F is faithful if for all objects a b, the function F' : Hom(a, b) → Hom(Fa, Fb), such that for all f ∈ Hom(a, b), f ↦ F(f); is injective.
Is-Faithful : {A B : Precategory} (F : Functor A B) → Set₁
Is-Faithful {A} {B} F = (a b : obj A) → is-inj (on-arrows F {a} {b})

-- A functor is full if the above function is surjective.
Is-Full : {A B : Precategory} (F : Functor A B) → Set₁
Is-Full {A} {B} F = (a b : obj A) → is-surj (on-arrows F {a} {b})

-- A functor is fully faithful if it is full and faithful.
Is-Fully-Faithful : {A B : Precategory} (F : Functor A B) → Pair Set₁ Set₁
Is-Fully-Faithful F = (Is-Faithful F) , (Is-Full F)

Is-Essentially-Surjective : {A B : Precategory} (F : Functor A B) → Set₁
Is-Essentially-Surjective {A} {B} F = (b : obj B) → is-prop (Σ (obj A) λ a → ({!B!} ≅ {!F on-obj a!}) {!b!})
