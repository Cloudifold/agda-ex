import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; map; foldl; foldr)
open import Data.Fin using (Fin; #_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Bool.Base using (Bool; true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤?_; z≤n; s≤s; _+_; _*_; ⌊_/2⌋; pred)
open import Relation.Nullary using (¬_)
-- open import Relation.Nullary.Decidable using (True; toWitness)\


data PR : ℕ -> Set where
  cons : (k : ℕ) -> ℕ -> PR k
  succ : PR 1
  proj : (k : ℕ) -> Fin k -> PR k
  comp : ∀ {k : ℕ} {m : ℕ} -> PR m -> Vec (PR k) m -> PR k
  prec : (k : ℕ) -> (g : PR k) -> (h : PR (suc (suc k))) -> PR (suc k)

cp : ∀ {n m : ℕ} -> (fs : Vec (PR n) m) -> Vec ℕ n -> Vec ℕ m

pr : ∀ {k : ℕ} -> PR k -> Vec ℕ k -> ℕ
pr (cons _ n) xs = n
pr succ (n ∷ []) = suc n
pr (proj k i) xs = lookup xs i
pr (comp {k} h gs) xs = pr h (cp gs xs)
pr (prec k g h) = f
  where
    f : Vec ℕ (suc k) -> ℕ
    f (zero ∷ xs) = pr g xs
    f (suc y ∷ xs) = pr h (y ∷ (f (y ∷ xs)) ∷ xs)

cp [] xs = []
cp (f ∷ fs) xs = pr f xs ∷ (cp fs xs)


record Enc (A : Set) : Set where
  field
    enc : A -> ℕ
    dec : ℕ -> A
    id-r : ∀ {n : ℕ} -> n ≡ enc (dec n)
    id-l : ∀ {a : A} -> a ≡ dec (enc a)


_even : ℕ -> Bool
zero even = true
(suc zero) even = false
(suc (suc a)) even = a even

invdiagonal : ℕ × ℕ -> ℕ
invdiagonal (a , zero) with a even
... | true   = pred (⌊ ((suc a) * (suc a) + (suc a)) /2⌋)
... | false  = ⌊ (a * a + a) /2⌋
invdiagonal (a , suc b) = invdiagonal (suc (a + b) , zero)

anti : (f : ℕ -> ℕ) -> ℕ -> ℕ -> ℕ
anti f n k = {!!}

diagonal : ℕ -> ℕ × ℕ
diagonal a = {!!}


