import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong)
open import Data.Vec using (Vec; []; _∷_; lookup)

open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)


open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; suc; _<_; _≤_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
-- open import Relation.Nullary.Decidable using (True; toWitness)

sn≤x→n≤x : ∀ {n x : ℕ} -> (suc n ≤ x) -> (n ≤ x)
sn≤x→n≤x {n = ℕ.zero} (s≤s z≤n) = z≤n
sn≤x→n≤x {n = suc n} {x = suc x} (s≤s y) = s≤s (sn≤x→n≤x y)



data PrimRec : ℕ ->  Set where
  const : (k : ℕ) -> (n : ℕ) -> PrimRec k
  succ  : PrimRec (suc ℕ.zero)
  proj  : (k : ℕ) -> (i : ℕ) -> ((suc i) ≤ k) -> PrimRec k
  comp  : ∀ {k : ℕ} -> {m : ℕ} -> PrimRec m -> Vec (PrimRec k) m -> PrimRec k
  prec  : (k : ℕ) -> (g : PrimRec k) -> (h : PrimRec (suc (suc k))) -> PrimRec (suc k)

parteval : ∀ {k : ℕ} -> PrimRec (suc k) -> ℕ -> PrimRec k
parteval {k} h n = comp {k} {suc k} h vec 
  where
    veck : ∀ (k : ℕ) -> (m : ℕ) -> (m ≤ (suc k)) -> Vec (PrimRec k) (m)
    veck k ℕ.zero x = []
    veck k (suc ℕ.zero) x = (const k n) ∷ []
    veck k (suc (suc m)) (s≤s x) = (proj k m x) ∷ veck k (suc m) (s≤s (sn≤x→n≤x x))
    
    ua : ∀ {k : ℕ} -> (suc k) ≤ (suc k)
    ua {ℕ.zero} = s≤s z≤n
    ua {ℕ.suc k} = s≤s (ua {k}) 
    vec = veck k (suc k) ua


select : ∀ {A : Set} {n : ℕ} -> Vec A n -> (i : ℕ) -> i < n -> A
select (x ∷ xs) ℕ.zero i<n = x
select (x ∷ xs) (suc i) (s≤s i<n) = select xs i i<n

vecApp : ∀ {A : Set} {B : Set} {n : ℕ} -> Vec (A -> B) n -> Vec A n -> Vec B n
vecApp [] [] = []
vecApp (x ∷ xs) (a ∷ as) = (x a) ∷ vecApp xs as

vecAppCons : ∀ {A : Set} {B : Set} {n : ℕ} -> Vec (A -> B) n -> A -> Vec B n
vecAppCons [] a = []
vecAppCons (x ∷ xs) a = (x a) ∷ vecAppCons xs a

vecMap : ∀ {A : Set} {B : Set} {n : ℕ} -> (A -> B) -> Vec A n -> Vec B n
vecMap f [] = []
vecMap f (x ∷ xs) = (f x) ∷ vecMap f xs

-- vecMapCons : ∀ {A : Set} {B : Set} {k : ℕ} {m : ℕ} -> 

_∘_ : ∀ {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
(f ∘ g) x = f (g x)

multiComp : ∀ {A : Set} {k : ℕ} {m : ℕ} -> (Vec A m -> A) -> Vec (Vec A k -> A) m  -> (Vec A k -> A)
multiComp h gs xs = h (vecMap (app xs) gs)
  where
    app : ∀ {A : Set} {n : ℕ} -> (Vec A n)-> (Vec A n -> A) -> A
    app xs f =  f xs
    
primRecFunc : ∀ {k : ℕ} -> PrimRec k -> (Vec ℕ k -> ℕ)
primRecFunc (const _ n) xs = n
primRecFunc succ (x ∷ []) = suc x
primRecFunc (proj k i i<k) xs = select xs i i<k
primRecFunc (comp {k} {m} h gs) = multiComp (primRecFunc h) (vecMap primRecFunc gs)
-- stucks termination checker

    
primRecFunc (prec k g h) = {!!}
  {-f
  where
    f : Vec ℕ (suc k) -> ℕ
    f (ℕ.zero ∷ xs) = primRecFunc g xs
    f (suc y  ∷ xs) = primRecFunc h (y ∷ (f (y ∷ xs)) ∷ xs)
    -}


data PrimRec2 : ℕ ->  Set where
  const2 : (k : ℕ) -> (n : ℕ) -> PrimRec2 k
  succ2  : PrimRec2 (suc ℕ.zero)
  proj2  : (k : ℕ) -> (i : ℕ) -> ((suc i) ≤ k) -> PrimRec2 k
  comp2  : ∀ {k : ℕ} -> PrimRec2 (suc (suc ℕ.zero)) -> PrimRec2 k -> PrimRec2 k -> PrimRec2 k
  prec2  : (k : ℕ) -> (g : PrimRec2 k) -> (h : PrimRec2 (suc (suc k))) -> PrimRec2 (suc k)

primRec2Func : ∀ {k : ℕ} -> PrimRec2 k -> (Vec ℕ k -> ℕ)
primRec2Func (const2 _ n) xs = n
primRec2Func succ2 (x ∷ []) = suc x
primRec2Func (proj2 k i i<k) xs = select xs i i<k
primRec2Func (comp2 h g f) xs = primRec2Func h ((primRec2Func g xs) ∷ (primRec2Func f xs) ∷ []) 
primRec2Func (prec2 k g h) = f
  where
    f : Vec ℕ (suc k) -> ℕ
    f (ℕ.zero ∷ xs) = primRec2Func g xs
    f (suc y  ∷ xs) = primRec2Func h (y ∷ (f (y ∷ xs)) ∷ xs)
