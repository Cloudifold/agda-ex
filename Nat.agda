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

data Prod (A B : Set) : Set where
  pair : A → B  → Prod A B

car : ∀ {A B : Set} → Prod A B → A
car (pair a b) = a

cdr : ∀ {A B : Set} → Prod A B → B
cdr (pair  a b) = b

{-
non-terminating exp1
add2 : Prod ℕ ℕ → ℕ
add2 x with (car x)
... | zero = cdr x
... | (suc n) = suc (add2 (pair n (cdr x)))
-}

h : ℕ → ℕ → ℕ
h zero zero = zero
h zero (suc y) = h zero y
h (suc x) y = h x y

g : ℕ → ℕ → ℕ
f : ℕ → ℕ → ℕ
f zero y = zero
f (suc x) zero = zero
f (suc x) (suc y) = h (g x  y) (f (suc (suc x)) y)

g zero y = zero
g (suc x) zero = zero
g (suc x) (suc y) = h (f  x y) (g x (suc (suc y)))
