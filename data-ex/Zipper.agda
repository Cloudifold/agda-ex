open import Data.Product
open import Data.Nat
open import Data.Sum
open import Data.List
open import Data.Empty
open import Data.Unit
import Relation.Binary.PropositionalEquality as Eq
open Eq

Poly :  Set₁
Poly = List Set


addPoly : Poly → Poly → Poly
addPoly P₁ [] = P₁
addPoly [] (x ∷ xs) = x ∷ xs
addPoly (p₁ ∷ p₁s) (p₂ ∷ p₂s) = (p₁ ⊎ p₂) ∷ addPoly p₁s p₂s

eval :  Poly → Set → Set
eval [] Y = ⊥
eval (A0 ∷ P) Y = A0 ⊎ ((eval P Y) × Y)

data Fix (P : Poly) : Set where
  fix : (eval P (Fix P)) → Fix P

A = ⊤ ∷ ⊤ ∷ []

toℕ : Fix A → ℕ
toℕ (fix (inj₁ tt)) = zero
toℕ (fix (inj₂ (inj₁ tt , snd))) = suc (toℕ snd)

fromℕ : ℕ → Fix A
fromℕ zero = fix (inj₁ tt)
fromℕ (suc x) = fix (inj₂ (inj₁ tt , (fromℕ x)))


L : ∀ (X : Set) → Poly
L X = ⊤ ∷ X ∷ []

toList : ∀ {X : Set} → Fix (L X) → List X
toList (fix (inj₁ tt)) = []
toList (fix (inj₂ (inj₁ x , snd))) = x ∷ (toList snd)

fromList : ∀ {X : Set} → List X → Fix (L X)
fromList [] = (fix (inj₁ tt))
fromList (x ∷ xs) = fix (inj₂ (inj₁ x , fromList xs))

data Poly2 : Set₁ where
  cons : Set → Poly2
  varX : Poly2
  varY : Poly2
  add : Poly2 → Poly2 → Poly2
  mul : Poly2 → Poly2 → Poly2

HoleX : Poly2 → Poly2
HoleX (cons x) = cons ⊥ 
HoleX (varX) = cons ⊤
HoleX (varY) = cons ⊥
HoleX (add a b) = add (HoleX a) (HoleX b)
HoleX (mul a b) = add (mul (HoleX a) b) (mul a (HoleX b))

HoleY : Poly2 → Poly2
HoleY (cons x) = cons ⊥
HoleY varX = cons ⊥
HoleY varY = cons ⊤
HoleY (add a b) = add (HoleY a) (HoleY b)
HoleY (mul a b) = add (mul (HoleY a) b) (mul a (HoleY b))


eval2 : Poly2 → Set → Set → Set
eval2 (cons A) X Y = A
eval2 varX X Y = X
eval2 varY X Y = Y
eval2 (add P Q) X Y = (eval2 P X Y) ⊎ (eval2 Q X Y)
eval2 (mul P Q) X Y = (eval2 P X Y) × (eval2 Q X Y)

data FixY (P : Poly2) (X : Set) : Set where
  fixY : (eval2 P X (FixY P X)) → FixY P X

1+XY : Poly2
1+XY = add (cons ⊤) (mul (varX) (varY))

qvq : ∀ {X Y} → (eval2 (HoleX (1+XY)) X Y) → Y
qvq (inj₂ (inj₁ (tt , snd))) = snd



1+XY→List : ∀ {X} → FixY 1+XY X → List X
1+XY→List (fixY (inj₁ tt)) = []
1+XY→List (fixY (inj₂ (fst , snd))) = fst ∷ (1+XY→List snd)

List→1+XY : ∀ {X} → List X → FixY 1+XY X
List→1+XY [] = (fixY (inj₁ tt))
List→1+XY (x ∷ xs) = fixY ((inj₂ (x , (List→1+XY xs))))

data Zipper (P : Poly2) (X : Set) : Set where
  current : (eval2 (HoleX P) X (FixY P X)) → Zipper P X
  move    : (eval2 (HoleY P) X (FixY P X)) → (Zipper P X) → Zipper P X

data Zlist (X : Set) : Set where
  zcons : List X → List X → Zlist X

zproj₁ : ∀ {X} → Zlist X → List X
zproj₁ (zcons a b) = a

zproj₂ : ∀ {X} → Zlist X → List X
zproj₂ (zcons a b) = b

zmove : ∀ {X} → Zlist X → X → Zlist X
zmove (zcons a b) x = zcons a (x ∷ b)

toZlist : ∀ {X} → Zipper 1+XY X → Zlist X
toZlist (current (inj₂ (inj₁ (tt , fx)))) = zcons [] (1+XY→List fx)
toZlist (move (inj₂ (inj₂ (x , tt))) zx) = zmove (toZlist zx) x

fromProdlist : ∀ {X} → List X → List X → Zipper 1+XY X
fromProdlist [] b = current (inj₂ (inj₁ (tt , (List→1+XY b))))
fromProdlist (x ∷ a) b  = move (inj₂ (inj₂ (x , tt))) (fromProdlist a (x ∷ b))

Zlist→Prodlist : ∀ {X} → Zlist X → (List X × List X)
Zlist→Prodlist (zcons a b) = a , b



data Nat : Set where
  z : Nat
  s : Nat → Nat

addNat : Nat → Nat → Nat
addNat z x₁ = x₁
addNat (s x) x₁ = s (addNat x x₁)







