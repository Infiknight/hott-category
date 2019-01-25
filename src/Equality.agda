{-# OPTIONS --without-K #-}

{- This file has been adjusted to be "universe polymorphic." The
   first thing to do is import the library Agda.Primitive. (This
   is built in to agda, so you don't need any extra files.)
-}
open import Agda.Primitive renaming (Level to ULevel)

{- The module takes a universe level α as an implicit parameter. -}
module Equality where

{- Equality is given as an inductive definition. If X is a type
   at level α, then the equality type is also at level α.
-}
data _==_ {α : ULevel} {X : Set α} (x : X) : X → Set α where
  idp : x == x

infix 30 _==_

{- ap is short for action on paths -}
ap : {α β : ULevel} {X : Set α} {Y : Set β} (f : X → Y) {x y : X} (p : x == y) → (f x == f y)
ap f idp =  idp


{- Transitivity of equality. We can visualise this as the concatenation
   of two paths. -}
_∙_ : ∀ {α} {X : Set α} {x y z : X} (p : x == y) (q : y == z) → (x == z)
p ∙ idp = p

infix 50 _∙_

transport : ∀ {X : Set} (Y : X → Set) {x y : X}
            (p : x == y) → (Y x) → (Y y)
transport Y idp y = y

{- We construct a function from x == y to y == x by pattern matching.
   Note that we have written .x for the second argument. These is referred to
   as a "dot pattern" or "inaccessible pattern." It signifies that the second
   argument is forced to be equal to x by the other arguments, in this case
   because the third argument is idp, it is forced to be equal to the second
   argument.
 -}
symmetric : ∀ {α} {X : Set α} (x y : X) → (x == y) → (y == x)
symmetric x .x idp = idp

{- We often use the following notation for symmetric.
   We think of this as reversing the direction of a path.
   Note that we have now made x and y into implicit arguments, when
   they weren't implicit for the function symmetric. This
   is often more useful in practice.
-}
! : ∀ {α} {X : Set α} {x y : X} → (x == y) → (y == x)
! {α} {X} {x} {y} p = symmetric x y p


{- The induction principle for equality is the function J defined
   below. This is called ind= in the HoTT book. -}
J : ∀ {α} {X : Set α} (C : (x : X) → (y : X) → (p : x == y) → Set)
    (c : (x : X) → (C x x idp)) → (x y : X) → (p : x == y) → C x y p
J C c x .x idp = c x

{- There is also a stronger version of J known as based path induction
   (in the HoTT book) or Paulin-Mohring J rule. -}
J' : ∀ {α} {X : Set α} (x : X) (C : (y : X) → (p : x == y) → Set α)
     (c : C x idp) → (y : X) → (p : x == y) → C y p
J' x C c .x idp = c


-- NB: In practice we can usually use pattern matching directly instead of J or J'


{- Transitivity -}
transitive : ∀ {α} {X : Set α} {x y z : X} → (x == y) → (y == z) → (x == z)
transitive {α} {X} {x} {y} {.y} p idp = p


{- Proofs that idp is a unit for ∙. -}
∙-unit-l : ∀ {α} {X : Set α} {x y : X} (p : x == y) → idp ∙ p == p
∙-unit-l idp = idp

{- Note that in the definition of transitive we only did pattern matching
   on the second argument and left p as it is. This allows us to use idp
   here.
-}
∙-unit-r : ∀ {α} {X : Set α} {x y : X} (p : x == y) → p ∙ idp == p
∙-unit-r p = idp


{- Note that any type has an identity type, even identity types themselves. -}

{- We show that composing a path p with its inverse is equal to idp -}
!-inv-l : ∀ {α} {X : Set α} {x y : X} (p : x == y) → (((! p) ∙ p) == idp )
!-inv-l idp = idp

!-inv-r : ∀ {α} {X : Set α} {x y : X} (p : x == y) → (p ∙ ! p == idp)
!-inv-r idp = idp

{- If two functions are equal then they have equal values at every point -}
app= : ∀ {α} {A : Set α} {B : A → Set α} (f g : (a : A) → B a) →
           (f == g) → ((a : A) → f a == g a)
app= f .f idp = λ a → idp
