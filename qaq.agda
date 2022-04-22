
import Relation.Binary.PropositionalEquality
  as Eq

open Eq
  using (_≡_; refl; sym; cong)

data ℕ : Set where
  zero : ℕ
  succ : ∀ (n : ℕ) → ℕ 

infixl 6 _+_
_+_ : ∀ (m n : ℕ) → ℕ
zero      + n = n
succ m + n = succ (m + n)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero        n p = refl
+-assoc (succ m) n p rewrite +-assoc m n p = refl



+-identity : ∀ (n : ℕ) → n ≡ n + zero
+-identity zero = refl
+-identity (succ n) rewrite sym (+-identity n) = refl

+-succ : ∀ (m n : ℕ) → succ (n + m) ≡ n + succ m
+-succ m zero rewrite sym (+-identity m) = refl
+-succ m (succ n) rewrite (+-succ m n) = cong succ refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n rewrite sym (+-identity n)= refl
+-comm (succ m) n rewrite sym (+-succ m n) | +-comm m n = refl
