module Nat where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + zero = zero
suc x + zero = suc x
zero + suc y = suc y
suc x + suc y = suc (suc (x + y))

_+_c_ : ℕ -> ℕ -> ℕ -> ℕ
zero + x₁ c x₂ = zero
suc x + x₁ c x₂ = suc ( x + x₁ c x₂ )

data EqNat : ℕ → ℕ → Set where
  EqZ : EqNat zero zero
  EqS : ∀ {n m : ℕ} → (EqNat n m) → EqNat (suc n) (suc m)

data QEq : Set → Set → Set where
  refl : ∀ {A : Set} → QEq A A

data T : Set where
  tt : T

data F : Set where

even : ℕ → Set
even zero = T
even (suc zero) = F
even (suc (suc x)) = even x

odd : ℕ → Set
odd n = even (suc n)

go : ∀ m c  → even m → odd c → odd (m + c c m)
go zero (suc n) x y = y
go (suc (suc m)) (suc zero) x y = x
go (suc (suc m)) (suc (suc n)) x y = go m n x y
