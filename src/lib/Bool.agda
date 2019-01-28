{-# OPTIONS --without-K #-}

module lib.Bool where

{- The type of booleans. There are two booleans: true and false -}
data Bool : Set where
  true : Bool
  false : Bool

{- conjunction (and), written '\wedge' -}
_∧_ : Bool → Bool → Bool
true ∧ true = true
true ∧ false = false
false ∧ true = false
false ∧ false = false

{- disjunction (or), written '\vee' -}
_∨_ : Bool → Bool → Bool
true ∨ q = true
false ∨ true = true
false ∨ false = false
