{-# OPTIONS --without-K #-}

module Naturals where

{- The definition of the natural numbers in agda -}
data ℕ : Set where
  zero : ℕ     -- zero
  succ : ℕ → ℕ -- successor

{- The next line tells Agda to expand the numerals 0,1,2,...
   to terms of type ℕ -}
{-# BUILTIN NATURAL ℕ #-}

{- The definition of addition using mixfix notation -}
_+_ : ℕ → ℕ → ℕ
n + zero = n
n + (succ m) = succ (n + m)

{- This sets the precedence of an infix operator -}
infix 70 _+_


{- Multiplication -}
times : ℕ → ℕ → ℕ
times n zero = zero
times n (succ m) = (times n m) + n

_×_ : ℕ → ℕ → ℕ
n × m = times n m


infix 80 _×_

double : ℕ → ℕ
double zero = zero
double (succ n) = succ (succ (double n))

{- Sometimes it is necessary or more convenient to use recursion terms 
   instead of pattern matching -}
{- We define the recursion term for ℕ as follows -}
ℕ-rec : (X : Set) (x : X) (s : ℕ → X → X) → ℕ → X
ℕ-rec X x s zero = x
ℕ-rec X x s (succ n) = s n (ℕ-rec X x s n)

{- Iteration. This repeated applies the function s n times to the element x of X -}
iter : (X : Set) (x : X) (s : X → X) → ℕ → X
iter X x s zero = x
iter X x s (succ n) = s (iter X x s n)

{- Recall that we defined is-even as an inductive definition with
   parameters. -}
data is-even : ℕ → Set where
  ie : (n : ℕ) → is-even (double n)
