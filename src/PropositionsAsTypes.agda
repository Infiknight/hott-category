{-# OPTIONS --without-K #-}

open import Equality
open import Bool
open import Agda.Primitive renaming (_⊔_ to lmax)

module PropositionsAsTypes where

{- Recall from last time that we can define True and False as the types ⊤ and ⊥ below. -}
data ⊥ : Set where

data ⊤ : Set where
  unit : ⊤

data _⊔_ {α β : Level} (X : Set α) (Y : Set β) : Set (lmax α β) where
  inl : (x : X) → X ⊔ Y
  inr : (y : Y) → X ⊔ Y

{- The recursion principle for coproducts -}
⊔-rec : {X Y Z : Set} → (X → Z) → (Y → Z) → (X ⊔ Y) → Z
⊔-rec f g (inl x) = f x
⊔-rec f g (inr y) = g y

infix 20 _⊔_


{- The definition of pair types.
   In the HoTT book products are written A × B
-}
record Pair {α β : Level} (A : Set α) (B : Set β) : Set (lmax α β) where
  constructor _,_
  field
    fst : A
    snd : B

{- Products can also be written using ⊓ (\sqcap) or × (\times) -}
_⊓_ : {α β : Level} (A : Set α) (B : Set β) → Set (lmax α β)
A ⊓ B = Pair A B

_×_ : {α β : Level} (A : Set α) (B : Set β) → Set (lmax α β)
A × B = Pair A B


{- Also recall that we can define the function exfalso from ⊥ into any type -}
exfalso : {α : Level} {X : Set α} → ⊥ → X
exfalso ()


{- We define negation below. This says that X is false (viewed as a proposition)
   or empty (viewed as a set).
-}
¬ : {α : Level} → Set α → Set α
¬ X = X → ⊥

{- From X → Y, prove its contraposition -}
modus-tollens : {X Y : Set} → (X → Y) → (¬ Y → ¬ X)
modus-tollens f = λ z z₁ → z (f z₁)

{- If p or q is true and q is false, then p is true. This is known
   as the disjunction syllogism.
-}
disj-syllogism : {P Q : Set} → (P ⊔ Q) → ¬ Q → P
disj-syllogism (inl x) y = x
disj-syllogism (inr y₁) y = exfalso (y y₁)


{- We use the following special notation for not equal
   (≠ is written using \neq)
-}
_≠_ : {α : Level} {X : Set α} (x y : X) → Set α
x ≠ y = ¬ (x == y)

infix 30 _≠_


{- Showing that true is not equal to false, is another example where we
   can use absurd pattern matching. (Exercise: Think about why this is!)
-}
true-≠-false : true ≠ false
true-≠-false ()

