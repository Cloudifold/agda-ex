
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)


infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infix  5 μ_
infixl 7 _∙_
infix  8 `suc_
infix  9 `_
infix  9 S_
infix  9 #_


data Type : Set where
  `⊤ : Type
  `ℕ : Type
  _⇒_ : Type → Type → Type


data Context : Set where
  ∅ : Context
  _,_ : Context → Type → Context


-- Intrinsic typing : Term Associated with types


{-
 example :
 _ : Context
 _ = ∅ , `ℕ ⇒ `ℕ , `ℕ
 -}

data _∋_ : Context → Type → Set where
  {- lookup judgment -}
  Z : ∀ {Γ A}
     -----------
    → Γ , A ∋ A
  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ----------
    → Γ , B ∋ A



{-  for terms which in context Γ have type A.
    The judgement is formalised by a datatype indexed by a context and a type.
 -}

data _⊢_ : Context → Type → Set where

  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  ƛ_  : ∀ {Γ A B}
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ A ⇒ B

  _∙_ : ∀ {Γ A B}
    → Γ ⊢ A ⇒ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B

  `tt : ∀ {Γ}
    → Γ ⊢ `⊤

  `zero : ∀ {Γ}
      ---------
    → Γ ⊢ `ℕ

  `suc_ : ∀ {Γ}
    → Γ ⊢ `ℕ
      ------
    → Γ ⊢ `ℕ

  case : ∀ {Γ A}
    → Γ ⊢ `ℕ
    → Γ ⊢ A
    → Γ , `ℕ ⊢ A
      ----------
    → Γ ⊢ A

  μ_ : ∀ {Γ A}
    → Γ , A ⊢ A
      ---------
    → Γ ⊢ A



length : Context → ℕ
length ∅       = zero
length (Γ , A) = suc (length Γ)

{- select a type from a context -}
lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
lookup {Γ , A} {zero}  (s≤s z≤n) = A
lookup {Γ , A} {suc n} (s≤s p)   = lookup {Γ} {n} p
{-
 Γ  = ∅ , A , B , C
 n  =     2   1   0
 lookup = A   B   C
 -}


count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup {n = n} p
count {_ , _} {zero}  (s≤s z≤n)  =  Z
count {Γ , _} {suc n} (s≤s p)    =  S (count p)

{-
 Γ = ∅ , `ℕ ⇒ `ℕ , `ℕ , `ℕ
          (S S Z)
             2
 a : count {Γ} {suc (suc zero)} ((s≤s (s≤s (s≤s z≤n)))) ≡ S (S Z)
 a = refl
 -}

{-
 lambda       : λ ƛ ƛ ƛ (# 3 ∙ # 2 ∙ # 1 ∙ # 0)
 context      : ∅
 -->
 lambda       : ƛ ƛ ƛ (# 3 ∙ # 2 ∙ # 1 ∙ # 0)
 context      : ∅ , T3
 -->
 lambda       : ƛ ƛ (# 3 ∙ # 2 ∙ # 1 ∙ # 0)
 context      : ∅ , T3 , T2
 -->
 lambda       : ƛ (# 3 ∙ # 2 ∙ # 1 ∙ # 0)
 context      : ∅ , T3 , T2 , T1

 -}



{-
 Function #_ takes an implicit argument n∈Γ that
 provides evidence for n to be within the context’s bounds.
 (dbi)
 -}
#_ : ∀ {Γ}
  → (n : ℕ)
  → {n∈Γ : True (suc n ≤? length Γ)}
    --------------------------------
  → Γ ⊢ lookup (toWitness n∈Γ)
#_ n {n∈Γ}  =  ` count {n = n} (toWitness n∈Γ)



Ch : Type → Type
Ch A  =  (A ⇒ A) ⇒ A ⇒ A

{-
 Church numeral :
 
 oneᶜ   : f ↦ f
 twoᶜ   : f ↦ f ∘ f
 threeᶜ : f ↦ f ∘ f ∘ f

 plusᶜ  : ( nᶜ : (f ↦ f^n) , mᶜ (f ↦ f^m) ) ↦ (f ↦ (nᶜ f) ∘ (mᶜ f))

 mulᶜ   : ( nᶜ : (f ↦ f^n) , mᶜ (f ↦ f^m) ) ↦ (f ↦ (nᶜ (mᶜ f)))

 -}

twoᶜ : ∀ {Γ A} → Γ ⊢ Ch A
twoᶜ = ƛ ƛ (# 1 ∙ (# 1 ∙ # 0))


plusᶜ : ∀ {Γ A} → Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A
plusᶜ = ƛ ƛ ƛ ƛ (# 3 ∙ # 1 ∙ (# 2 ∙ # 1 ∙ # 0))

mulᶜ :  ∀ {Γ A} → Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A
mulᶜ =  ƛ ƛ ƛ ƛ (# 3 ∙ (# 2 ∙ # 1) ∙ # 0)
-- mulᶜ  nᶜ    mᶜ    f      x   =   (nᶜ ∙ (mᶜ f)) ∙ x
--     Ch A  Ch A  A ⇒ A   A   =         A
-- mulᶜ  nᶜ    mᶜ    f          =   (nᶜ ∙ (mᶜ f))
--     Ch A  Ch A  A ⇒ A       =      A ⇒ A


sucᶜ : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ
sucᶜ = ƛ `suc (# 0)

2+2ᶜ : ∀ {Γ} → Γ ⊢ `ℕ
2+2ᶜ = plusᶜ ∙ twoᶜ ∙ twoᶜ ∙ sucᶜ ∙ `zero

{-
 qwq
 -}


ext : ∀ {Γ Δ}
  → (∀ {A}   →     Γ ∋ A  →     Δ ∋ A)
    -------------------------------------
  → (∀ {A B} → Γ , B ∋ A  → Δ , B ∋ A)
-- extenstion lemmma

-- ext Q x = ?
{-
 Q : Γ ∋ A → Δ ∋ A
 x : Γ , B ∋ A

 example

  Γ , B    Γ                 Δ    Δ , B
   
                            # 3 -- # 4
   # 3 -- # 2  |            # 2 -- # 3
   # 2 -- # 1  |-- Q -->    # 1 -- # 2
   # 1 -- # 0  |            # 0 -- # 1

   # 0 -- # 0  --- Z -->    # 0 -- # 0


 -}
-- case split x
ext Q Z     = Z
ext Q (S y) = S (Q y)
-- y : Γ ∋ A

{-
 _ : ext {∅ , `ℕ ⇒ `ℕ} {∅ , `ℕ ⇒ `ℕ , `ℕ} S_ {`ℕ} Z ≡ Z
 _ = refl

 _ : (ext {∅ , `ℕ ⇒ `ℕ , `ℕ} {∅ , `ℕ ⇒ `ℕ , `ℕ , `ℕ} S_) {`ℕ} {`ℕ} (S Z) ≡ S (S Z)
 _ = refl
 -}


rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
-- renaming
{-
 If variables in one context map to variables in another,
 then terms in the first context map to terms in the second

 special context morphism

 -}
rename qwq (` x)        = ` (qwq x)
rename qwq (ƛ x)        = ƛ (rename (ext qwq) x)
rename qwq (x ∙ y)      = (rename qwq x) ∙ (rename qwq y)
rename qwq `tt          = `tt
rename qwq `zero        = `zero
rename qwq (`suc x)     = `suc (rename qwq x)
rename qwq (case z y x) = case (rename qwq z) (rename qwq y) (rename (ext qwq) x)
rename qwq (μ x)        = μ (rename (ext qwq) x)


{-
 X₀ : ∅ , `ℕ ⇒ `ℕ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
 X₀ = ƛ ƛ (# 1 ∙ (# 2 ∙ # 0))

 X₁ : ∅ , `ℕ ⇒ `ℕ , `ℕ  ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
 X₁ = ƛ ƛ (# 1 ∙ (# 3 ∙ # 0))

 _ : rename S_ X₀ ≡ X₁
 _ = refl


 M₀ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
 M₀ = ƛ (# 1 ∙ (# 1 ∙ # 0))

 M₁ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ ⇒ `ℕ
 M₁ = ƛ (# 2 ∙ (# 2 ∙ # 0))

 _ : rename S_ M₀ ≡ M₁
 _ = refl

 rename S_ M₀ = ƛ (rename (ext S_) (# 1 ∙ (# 1 ∙ # 0)))
              = ƛ ( 
                    rename (ext S_) (# 1)
                    ∙
                    rename (ext S_) (# 1 ∙ # 0)
                  )
              = ƛ ( 
                    rename (ext S_) (# 1)
                    ∙
                    (
                      rename (ext S_) (# 1)
                      ∙
                      rename (ext S_) (# 0)
                    )
                  )
              = ƛ ( 
                    (# 2)
                    ∙
                    (
                      (# 2)
                      ∙
                      (# 0)
                    )
                  )
 -}



{-
 Because de Bruijn indices free us of concerns with renaming,
 it becomes easy to provide a definition of substitution
 that is more general than the one considered previously.
 Instead of substituting a closed term for a single variable,
 it provides a map that takes each free variable of the original term to another term.
 Further, the substituted terms are over an arbitrary context, and need not be closed.
 -}

exts : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ⊢ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

{-
 context morphsim σ :  Γ  → Δ
 induces
 context morphsim (exts σ) :  Γ , B  → Δ , B

 rename {Γ = Δ} {Δ = Δ , B} S_ (σ x)    x : Γ ∋ A 
                                      σ x : Δ ∋ A
                                      S_  : ∀ {A} → Δ ∋ A → Δ , B ∋ A
 -}




subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ A)
    -----------------------
  → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
{-
 substitution 
 σ : (∀ {A} → Γ ∋ A → Δ ⊢ A)
 context morphism
 variables (types) in Γ → terms in Δ
   
 so we have terms in Γ → terms in Δ (substitution)

 -}

subst σ (` k)          =  σ k
subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
subst σ (L ∙ M)        =  (subst σ L) ∙ (subst σ M)
subst σ (`tt)          =  `tt
subst σ (`zero)        =  `zero
subst σ (`suc M)       =  `suc (subst σ M)
subst σ (case L M N)   =  case (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (μ N)          =  μ (subst (exts σ) N)


_[_] : ∀ {Γ A B}
  → Γ , B ⊢ A
  → Γ ⊢ B
    ---------
  → Γ ⊢ A
-- Single substitution
{-
 substitute variable(type) B with a term of type B
 -}

_[_] {Γ} {A} {B} x y = (subst {Γ , B} {Γ} σ) {A} x 
  where
    σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
    σ Z     = y
    σ (S z) = ` z
    {-
     Z    : Γ , B ∋ B
     Goal : Γ ⊢ B
     S z  : Γ , B ∋ A
       z  : Γ     ∋ A
      `_  : Γ ∋ A → Γ ⊢ A
     -}

data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
      ---------------------------
    → Value (ƛ N)

  V-tt : ∀ {Γ}
      ----------------
    → Value (`tt {Γ})

  V-zero : ∀ {Γ}
      -----------------
    → Value (`zero {Γ})

  V-suc : ∀ {Γ} {V : Γ ⊢ `ℕ}
    → Value V
      --------------
    → Value (`suc V)


infix 2 _—→_

data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  ξ-∙-l : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
    → L —→ L′
      ---------------
    → L ∙ M —→ L′ ∙ M

  ξ-∙-r : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
    → Value V
    → M —→ M′
      ---------------
    → V ∙ M —→ V ∙ M′

  β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
    → Value W
      --------------------
    → (ƛ N) ∙ W —→ N [ W ]

  ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
    → M —→ M′
      -----------------
    → `suc M —→ `suc M′

  ξ-case : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → L —→ L′
      -------------------------
    → case L M N —→ case L′ M N

  β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
      -------------------
    → case `zero M N —→ M

  β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
    → Value V
      ----------------------------
    → case (`suc V) M N —→ N [ V ]

  β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
      ----------------
    → μ N —→ N [ μ N ]



infix  2 _—↠_
infix  1 begin_
infixr 2 _—→⟨_⟩_
infix  3 _∎

data _—↠_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : (M : Γ ⊢ A)
      ------
    → M —↠ M

  _—→⟨_⟩_ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L —→ M
    → M —↠ N
      ------
    → L —↠ N

begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M —↠ N
begin M—↠N = M—↠N


V¬—→ : ∀ {Γ A} {V : Γ ⊢ A} {N} → (Value V) → ¬ (V —→ N)
V¬—→ (V-suc Val) (ξ-suc V—→N) = V¬—→ Val V—→N


data Progress {A} (M : ∅ ⊢ A) : Set where
  step : ∀ {N : ∅ ⊢ A}
    → M —→ N
      -----------
    → Progress M

  done :
       Value M
    → Progress M


progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
-- empty because well-typed term have no free var
progress (ƛ M)     = done V-ƛ
progress (M ∙ N)   with progress M
... | step x       = step (ξ-∙-l x) 
... | done V-ƛ       with progress N
...   | step y       = step (ξ-∙-r V-ƛ y)
...   | done y       = step (β-ƛ y)
progress `tt       = done V-tt
progress `zero     = done V-zero
progress (`suc M)  with progress M
... | step x       = step (ξ-suc x)
... | done x       = done (V-suc x)
progress (case M N O) with progress M
... | step x          = step (ξ-case x) 
... | done V-zero     = step β-zero
... | done (V-suc x)  = step (β-suc  x)
progress (μ M)     = step β-μ



record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished {Γ A} (N : Γ ⊢ A) : Set where
   done :
       Value N
       ----------
     → Finished N

   out-of-gas :
       ----------
       Finished N


data Steps {A} : ∅ ⊢ A → Set where

  steps : {L N : ∅ ⊢ A}
    → L —↠ N
    → Finished N
      ----------
    → Steps L


eval : ∀ {A}
  → Gas
  → (L : ∅ ⊢ A)
    -----------
  → Steps L
eval (gas zero)    L                     =  steps (L ∎) out-of-gas
eval (gas (suc m)) L with progress L
... | done VL                            =  steps (L ∎) (done VL)
... | step {M} L—→M with eval (gas m) M
...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin


-- mul

2*2ᶜ : ∅ ⊢ `ℕ
2*2ᶜ =  mulᶜ ∙ twoᶜ ∙ twoᶜ ∙ sucᶜ ∙ `zero
4ᶜ : ∅ ⊢ `ℕ
4ᶜ   =  `suc (`suc (`suc (`suc `zero)))



_ : eval (gas 100) 2*2ᶜ ≡
  steps
    (
      (
        ( ƛ ƛ ƛ ƛ (# 3 ∙ (# 2 ∙ # 1) ∙ # 0) )
        ∙
        ( ƛ ƛ (# 1 ∙ (# 1 ∙ # 0)) )
        ∙
        ( ƛ ƛ (# 1 ∙ (# 1 ∙ # 0)) )
        ∙
        ( ƛ (`suc # 0) )
        ∙
        `zero
      )
      —→⟨ ξ-∙-l (ξ-∙-l (ξ-∙-l (β-ƛ V-ƛ))) ⟩
      {-
        first partial evaluation
        (mulᶜ ∙ twoᶜ) —→  ƛ ƛ ƛ (# 3 ∙ (# 2 ∙ # 1) ∙ # 0) [ twoᶜ ]
        by β-ƛ {N = ƛ ƛ ƛ (# 3 ∙ (# 2 ∙ # 1) ∙ # 0)} V-ƛ {twoᶜ}

        ƛ ƛ ƛ (# 3 ∙ (# 2 ∙ # 1) ∙ # 0) : ∅ , Ch A ⊢ Ch A ⇒ Ch A 
        twoᶜ :  ∅ ⊢ Ch A

        ƛ ƛ ƛ (# 3 ∙ (# 2 ∙ # 1) ∙ # 0) [ ƛ ƛ (# 1 ∙ (# 1 ∙ # 0)) ] {Γ = ∅} {A = Ch A ⇒ Ch A} (B = Ch A)
        
        =  
        
        (subst {∅ , Ch A} {∅} σ) {Ch A} (ƛ ƛ ƛ (# 3 ∙ (# 2 ∙ # 1) ∙ # 0))
          where
            σ  context morphism
               variables (types) in Γ → terms in Δ
            σ : ∀ {C} → ∅ , Ch A ∋ C → ∅ ⊢ C
            σ Z     = ƛ ƛ (# 1 ∙ (# 1 ∙ # 0))
            -- σ (S z) = ` z 
            -- not matched

            σ : Ch A  ↦ twoᶜ
            σ : other ↦ ` other

          exts σ : ∀ {A B} {C} → ∅ , Ch A , B ∋ C → ∅ , B ⊢ C 

          (exts σ) Z     = ‵ Z
                      B ↦ B
          (exts σ) (S Z) = rename {Γ = ∅} {Δ = ∅ , B} S_ (σ Z)
                         = (ƛ ƛ (# 1 ∙ (# 1 ∙ # 0)))
                   Ch A ↦ (ƛ ƛ (# 1 ∙ (# 1 ∙ # 0)))

          exts (exts σ) : ∀ {A B D} {C} → ∅ , Ch A , B , D ∋ C → ∅ , B , D ⊢ C 

          (exts (exts σ)) Z         = ` Z
                          D        ↦  D
          (exts (exts σ)) (S Z)     = rename {Γ = ∅ , B} {Δ = ∅ , B , D} S_ ((exts σ) Z)
                                    = rename {Γ = ∅ , B} {Δ = ∅ , B , D} S_ `Z
                                    = ` (S Z)
                            B      ↦   B
          (exts (exts σ)) (S (S Z)) = rename {Γ = ∅ , B} {Δ = ∅ , B , D} S_ ((exts σ) (S Z))
                                    = rename {Γ = ∅ , B} {Δ = ∅ , B , D} S_ (ƛ ƛ (# 1 ∙ (# 1 ∙ # 0)))
                                    = (ƛ ƛ (# 1 ∙ (# 1 ∙ # 0)))
                             Ch A  ↦ (ƛ ƛ (# 1 ∙ (# 1 ∙ # 0)))
                      

        =

        λ (  subst (exts σ) (ƛ ƛ (# 3 ∙ (# 2 ∙ # 1) ∙ # 0)) )

        =

        λ ƛ (  subst (exts (exts σ)) ( ƛ (# 3 ∙ (# 2 ∙ # 1) ∙ # 0)) )

        = 

        λ ƛ ƛ (  subst (exts (exts (exts σ))) (# 3 ∙ (# 2 ∙ # 1) ∙ # 0)  )
         
        ( by subst σ (ƛ N)  =  ƛ (subst (exts σ) N) )

        =
      
        λ ƛ ƛ (
                ( subst (exts (exts (exts σ))) # 3 )
                ∙
                (
                  ( subst (exts (exts (exts σ)))  # 2 )
                  ∙
                  ( subst (exts (exts (exts σ)))  # 1 )
                )
                ∙
                ( subst (exts (exts (exts σ))) # 0 )
                
              )
        
        ( by subst σ (L ∙ M)  =  (subst σ L) ∙ (subst σ M) )

        =
    
        ƛ ƛ ƛ (twoᶜ ∙ (# 2 ∙ # 1) ∙ # 0)
      
        ( by subst σ (` k) = σ k )   
        
      -}
      (
        ( ƛ ƛ ƛ (twoᶜ ∙ (# 2 ∙ # 1) ∙ # 0) )
        ∙
        ( ƛ ƛ (# 1 ∙ (# 1 ∙ # 0)) )-- twoᶜ
        ∙
        ( ƛ (`suc # 0) ) 
        ∙
        `zero
      )
      —→⟨ ξ-∙-l (ξ-∙-l (β-ƛ V-ƛ)) ⟩
      (
        ( ƛ ƛ (twoᶜ ∙ (twoᶜ ∙ # 1) ∙ # 0) )
        ∙
        ( ƛ (`suc # 0) )-- sucᶜ 
        ∙
        `zero
      )
      —→⟨ ξ-∙-l (β-ƛ V-ƛ) ⟩
      (
        ( ƛ (twoᶜ ∙ (twoᶜ ∙ sucᶜ) ∙ # 0) )
        ∙
        `zero
      )
      —→⟨ β-ƛ V-zero ⟩
      (twoᶜ ∙ (twoᶜ ∙ sucᶜ)) ∙ `zero
      —→⟨ ξ-∙-l (ξ-∙-r V-ƛ (β-ƛ V-ƛ)) ⟩
      (twoᶜ ∙ (ƛ (sucᶜ ∙ (sucᶜ ∙ # 0)))) ∙ `zero
      —→⟨ ξ-∙-l (β-ƛ V-ƛ) ⟩
      (ƛ ((ƛ (sucᶜ ∙ (sucᶜ ∙ # 0))) ∙ ((ƛ (sucᶜ ∙ (sucᶜ ∙ # 0))) ∙ # 0))) ∙ `zero
      —→⟨ β-ƛ V-zero ⟩
      (ƛ (sucᶜ ∙ (sucᶜ ∙ # 0))) ∙ ((ƛ (sucᶜ ∙ (sucᶜ ∙ # 0))) ∙ `zero)
      —→⟨ ξ-∙-r V-ƛ (β-ƛ V-zero) ⟩
      (ƛ (sucᶜ ∙ (sucᶜ ∙ # 0))) ∙ (sucᶜ ∙ ((ƛ (`suc # 0)) ∙ `zero))
      —→⟨ ξ-∙-r V-ƛ (ξ-∙-r V-ƛ (β-ƛ V-zero)) ⟩
      (ƛ (sucᶜ ∙ (sucᶜ ∙ # 0))) ∙ (sucᶜ ∙ `suc `zero)
      —→⟨ ξ-∙-r V-ƛ (β-ƛ (V-suc V-zero))⟩
      (ƛ (sucᶜ ∙ (sucᶜ ∙ # 0))) ∙ `suc (`suc `zero)
      —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
      sucᶜ ∙ (sucᶜ ∙ `suc (`suc `zero))
      —→⟨ ξ-∙-r V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
      sucᶜ ∙ `suc (`suc (`suc `zero))
      —→⟨ β-ƛ (V-suc (V-suc (V-suc V-zero))) ⟩
      `suc (`suc (`suc (`suc `zero)))
      ∎  
    )
    (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
_ = refl


data _Eq_ : ∀ {A : Set} -> A -> Set where
  re : ∀ {A : Set} {a : A} -> a Eq a
