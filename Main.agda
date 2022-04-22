module Main where

import Relation.Binary.PropositionalEquality
  as Eq
open Eq
  using (_≡_; refl; trans; sym; cong)
open Eq.≡-Reasoning
  using (begin_; step-≡; _∎)

open import Data.Nat
  using (ℕ; zero; suc; _+_)

data Vect (A : Set) : ℕ → Set where
  [] : Vect A zero
  _∷_ : ∀ {n} (x : A) (xs : Vect A n)
        → Vect A (suc n)
infixr 4 _∷_

data List (A : Set) : Set where
  [] : List A
  _∷_ : ∀ (x : A) (xs : List A) → List A

_append_ : ∀ {A : Set} (xs ys : List A) → List A
[] append ys = ys
(x ∷ xs) append ys = x ∷ (xs append ys)

_++_ : ∀ {A} {n m} (xs : Vect A n) (ys : Vect A m) → Vect A (n + m)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where
{-
even : ∀ (n : ℕ) → Set
odd  : ∀ (n : ℕ) → Set
even zero = ⊤
even (suc n) = odd n
odd zero = ⊥
odd (suc n) = even n
-}
data even : ℕ → Set
data odd  : ℕ → Set
data even where
  even-zero : even zero
  odd-suc : ∀ (n : ℕ) → odd n → even (suc n)
data odd where
  even-suc : ∀ (n : ℕ) → even n → odd (suc n)
  λ
  
