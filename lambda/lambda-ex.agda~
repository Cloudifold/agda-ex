module lambda-ex where

open import Data.Bool using (T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; _∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; _≟_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋; False; toWitnessFalse)
open import Relation.Nullary.Negation using (¬?)
open import Relation.Binary.PropositionalEquality 
  as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂)
{-
 open Eq.≡-Reasoning
   using (begin_; _≡⟨⟩_; step-≡; _∎)
 -}

Id : Set
Id = String

_∘_ : ∀ {A : Set} {B : Set} {C : Set}
    → (A → B)
    → (B → C)
    → (A → C)
(f ∘ g) x = g (f x)

infix 5 Lam
-- lambda
infix 5 Mu
-- μ
infixl 7 _∙_
-- application
infix 8 Tsuc
-- suc in Term
infix 9 Var


data Term : Set where
  Var : Id → Term
  Lam : Id → Term → Term
  _∙_ : Term → Term → Term
  Tzero : Term
  Tsuc : Term → Term
  Case : Term → Term → Id → Term → Term
  {-
   Case _
        [ zero → _ | suc _( : Id) → _ ]
   -}
  Mu : Id → Term → Term

two : Term
two = Tsuc (Tsuc Tzero)

plus : Term
plus = Mu "+" (
              Lam "m" (
                      Lam "n" (
                              Case m
                                 {- zero  → _ -}   n
                                 {- suc _ → _ -}   "m" (Tsuc (+ ∙ m ∙ n )))))
    where m = (Var "m")
          n = (Var "n")
          + = (Var "+")


data Value : Term → Set where
  {-
   A value is a term that corresponds to an answer.
   ( 'Canonical' form of term )
   -}
  V-Lam : ∀ {x N}
        → Value (Lam x N)

  V-zero : Value Tzero
 
  V-suc : ∀ {N}
        → Value N
        → Value (Tsuc N)

infix 10 _[_:=_]



_[_:=_] : Term → Id → Term → Term
{-
 Substituting one term for a variable in another term. 
 -}
Var x [ y := F ] with x ≟ y
... | yes _          = F
... | no  _          = Var x

Lam x Z [ y := F ] with x ≟ y
... | yes _          = Lam x Z
... | no  _          = Lam x (Z [ y := F ])
(X ∙ Z) [ y := F ] = X [ y := F ] ∙ Z [ y := F ]

Tzero [ y := F ] = Tzero
Tsuc X [ y := F ] = Tsuc (X [ y := F ])

Case C Z x S [ y := F ] with x ≟ y
{-
 Case C
      zero   →  Z
      suc x  →  S
 -}
... | yes _                 = Case (C [ y := F ]) (Z [ y := F ]) x S
... | no  _                 = Case (C [ y := F ]) (Z [ y := F ]) x (S [ y := F ])

Mu x Z [ y := F ] with x ≟ y
... | yes _             = Mu x Z
... | no  _             = Mu x (Z [ y := F ])



{-
 To reduce an application,
 first we reduce the left-hand side until it becomes a value (which must be an abstraction);
 then we reduce the right-hand side until it becomes a value;
 and finally we substitute the argument for the variable in the abstraction.
 -}


infix 4 _—→_

data _—→_ : Term → Term → Set where
  {-
   A —→ B 
   A reduce to B
   -}
  xi-r : ∀ {A B C}
       → A —→ B
       → A ∙ C —→ B ∙ C

  xi-l : ∀ {A B C}
       → Value C
       → A —→ B
       → C ∙ A —→ C ∙ B
  
  beta-Lam : ∀ {x N V}
       → Value V
       → (Lam x N) ∙ V —→ N [ x := V ]
  {-
   (λ x . N) V —→ N [ x := V ]
   beta reduction

  Value (f x)  -- 
   Value ((Value f) x) or Value (f Value(x))
   
   for deterministivity,
   we should choose one
   -}
  xi-suc : ∀ {B C}
       → B —→ C
       → Tsuc B —→ Tsuc C

  xi-case : ∀ {A B Z x Y}
       → A —→ B
       → Case A Z x Y —→ Case B Z x Y

  beta-zero : ∀ {x Z Y}
       → Case Tzero Z x Y —→ Z

  beta-suc : ∀ {x V Z Y}
       → Value V
       → Case (Tsuc V) Z x Y —→ Y [ x := V ]

  beta-mu : ∀ {x F}
       → Mu x F —→ F [ x := (Mu x F) ]
  {-
   μ dose not have canonical form?
   -}
  

infix  2 _—↠_
infix  1 begin'_
infixr 2 _—→⟨_⟩_
infix  3 _∎'

data _—↠_ : Term → Term → Set where
  {-
   refl and trans closure of _—→_
   -}
  _∎' : ∀ X
      ---------
    → X —↠ X

  _—→⟨_⟩_ : ∀ L {X Y}
    → L —→ X
    → X —↠ Y
      ---------
    → L —↠ Y

begin'_ : ∀ {X Y}
  → X —↠ Y
    ---------
  → X —↠ Y
begin' X—↠Y = X—↠Y

{-
 PLFA : 

 data _—↠′_ : Term → Term → Set where

   step′ : ∀ {M N}
     → M —→ N
       -------
     → M —↠′ N

   refl′ : ∀ {M}
      -------
     → M —↠′ M

   trans′ : ∀ {L M N}
     → L —↠′ M
     → M —↠′ N
       -------
     → L —↠′ N

 —↠≲—↠′

 First notion of reflexive and transitive closure above embeds into the second.
 Why are they not isomorphic?


 Cause trans′ cannot be constructed from _—↠_ 
 -}

{-
 Confluence : 
 L : Term
 If L —→ X and L —→ Y
 Then exist P such that X —→ P and Y —→ P
  
  L --> Y
  |     |
  V     V
  X --> P
  
 -}

{-
postulate
  confluence : ∀ {L M N}
    → ((L —↠ M) × (L —↠ N))
      --------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))

  diamond : ∀ {L M N}
    → ((L —→ M) × (L —→ N))
      --------------------
    → ∃[ P ] ((M —↠ P) × (N —↠ P))

  deterministic : ∀ {L M N}
    → L —→ M
    → L —→ N
      ------
    → M ≡ N
 -}

-- **Typing**

infixr 7 _⇒_

data Type : Set where
  _⇒_ : Type → Type → Type
  Nat : Type

infixl 5 _,_∶_

data Context : Set where
  {-
   While reduction considers only closed terms,
   typing must consider terms with free variables.
   To type a term, we must first type its subterms,
   and in particular in the body of an abstraction its bound variable may appear free.

   A context associates variables with types. We let Γ and Δ range over contexts.
   We write ∅ for the empty context,
   and Γ , x ⦂ A for the context that extends Γ by mapping variable x to type A. For example,
   -}
  ∅ : Context
  _,_∶_ : Context → Id → Type → Context

-- Context ≅ List (Id × Type)


-- **Lookup judgment**


{-
 Γ ∋ x : A
 in context Γ that variable x has type A
 <lookup judgment>
 -}

infix 4 _∋_∶_

data _∋_∶_ : Context → Id → Type → Set where

  Z : ∀ {Γ x A}
    → Γ , x ∶ A ∋ x ∶ A

  S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ∶ A
    → Γ , y ∶ B ∋ x ∶ A

-- **Typing judgement**

{-
 Γ ⊢ M ∶ A
 in context Γ term M has type A
 <typing judgment>
 -}

infix 4 _⊢_∶_

data _⊢_∶_ : Context → Term → Type → Set where

  -- Axiom
  ⊢Var : ∀ {Γ x A}
       → Γ ∋ x ∶ A
         ---------------
       → Γ ⊢ Var x ∶ A

  -- ⇒-I
  ⊢Lam : ∀ {Γ x N A B}
       → Γ , x ∶ A ⊢ N ∶ B
         ---------------------
       → Γ ⊢ Lam x N ∶ A ⇒ B

  -- ⇒-E
  ⊢∙ : ∀ {Γ F X A B}
       → Γ ⊢ F ∶ A ⇒ B
       → Γ ⊢ X ∶ A
         ---------------
       → Γ ⊢ F ∙ X ∶ B

  -- Nat-I-zero
  ⊢zero : ∀ {Γ}
       → Γ ⊢ Tzero ∶ Nat
       
  -- Nat-I-suc
  ⊢suc  : ∀ {Γ X}
       → Γ ⊢ X ∶ Nat
         ------------------
       → Γ ⊢ Tsuc X ∶ Nat

  -- Nat-E
  ⊢case : ∀ {Γ L Z x Y A}
       → Γ ⊢ L ∶ Nat
       → Γ ⊢ Z ∶ A
       → Γ , x ∶ Nat ⊢ Y ∶ A
         ------------------------
       → Γ ⊢ Case L Z x Y ∶ A

  ⊢mu  : ∀ {Γ x Z A}
       → Γ , x ∶ A ⊢ Z ∶ A
       → Γ ⊢ Mu x Z ∶ A

∋-inj : ∀ {Γ x A B} → Γ ∋ x ∶ A → Γ ∋ x ∶ B → A ≡ B
{- look up judgement is injective -}
∋-inj Z Z = refl
∋-inj Z (S x≢ _) = ⊥-elim (x≢ refl)
{-
 Z : ∀ {Γ x A}
    → Γ , x ∶ A ∋ x ∶ A

 S : ∀ {Γ x y A B}
    → x ≢ y
    → Γ ∋ x ∶ A
    → Γ , y ∶ B ∋ x ∶ A
 
 S x≢ _ : Γ ∋ x ∶ B
 ------------------
 Γ  = Γ' , y ∶ C
 _  : Γ' ∋ x ∶ B
 x≢ : x ≢ y
 
 x≢ : x ≢ y
 x ≢ y = (x ≡ y → ⊥)
 refl : x ≡ y
 
 data _≡_ : {ℓ} {A : Set ℓ} : A → Set a where
   instance refl : x ≡ x

  
 ⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever
 ⊥-elim ( )
         
 -}
∋-inj (S x≢ _) Z = ⊥-elim (x≢ refl)
∋-inj (S _ x) (S _ y) = ∋-inj x y
 {-
  recusive step
  decrease the length of Γ
  -}

V¬—→ : ∀ {M N}
  → Value M
    ----------
  → ¬ (M —→ N)
V¬—→ V-Lam      ()
V¬—→ V-zero     ()
V¬—→ (V-suc VM) (xi-suc M—→N) = V¬—→ VM M—→N


infix 4 Canonical_∶_
{-
 canonical form : value with type
 -}
data Canonical_∶_ : Term → Type → Set where
  C-Lam : ∀ {x A N B}
        → ∅ , x ∶ A ⊢ N ∶ B
          ------------------
        → Canonical (Lam x N) ∶ (A ⇒ B)
        
  C-zero :
          ----------------------
           Canonical Tzero ∶ Nat

  C-suc : ∀ {N}
        → Canonical N ∶ Nat
          -----------------------
        → Canonical Tsuc N ∶ Nat


canonical : ∀ {V A}
  → ∅ ⊢ V ∶ A
  → Value V
  → Canonical V ∶ A
{-  well typed value in empty context is canonical form -}

canonical (⊢Lam x) V-Lam = C-Lam x
canonical ⊢zero V-zero = C-zero
canonical (⊢suc x) (V-suc x₁) = C-suc (canonical x x₁)



value : ∀ {W A}
  → Canonical W ∶ A
  → Value W
{- canonical form is value -}


value (C-Lam x) = V-Lam
value C-zero = V-zero
value (C-suc x) = V-suc (value x)

typed : ∀ {Z A}
  → Canonical Z ∶ A
  → ∅ ⊢ Z ∶ A
{- canonical form is well typed in empty context -}

typed (C-Lam x) = ⊢Lam x
typed C-zero = ⊢zero
typed (C-suc x) = ⊢suc (typed x)


data Progress (M : Term) : Set where

  step : ∀ {N}
    → M —→ N
      -----------
    → Progress M

  done :
       Value M
    → Progress M

{- Progress : ∅ ⊢ M ∶ A → M is value or ∃ N, M —→ N 
   it is a property of Terms
 -}


progress : ∀ {M A}
  → ∅ ⊢ M ∶ A
  → Progress M
{- well typed in empty context → progress -}

progress (⊢Lam x) = done V-Lam
progress (⊢∙ x y) with progress x
... | step x—→w              = step (xi-r x—→w) 
... | done vx with progress y
...   | step y—→w            = step (xi-l vx y—→w)
...   | done vy with canonical x vx
...     | C-Lam _              = step (beta-Lam vy)
progress ⊢zero = done V-zero
progress (⊢suc x) with progress x
... | step x—→w              = step (xi-suc x—→w)
... | done vx                  = done (V-suc vx)
progress (⊢case x y z) with progress x
... | step x—→o              = step (xi-case x—→o)
... | done vx with canonical x vx
...   | C-zero                 = step beta-zero
...   | C-suc  a               = step (beta-suc (value a))
progress (⊢mu x) = step beta-mu


{-
 Renaming 
 -}

ext : ∀ {Γ Δ}
  → (∀ {x A}     → Γ ∋ x ∶ A         →   Δ ∋ x ∶ A)
    --------------------------------------------------------
  → (∀ {x y A B} → Γ , y ∶ B ∋ x ∶ A → Δ , y ∶ B ∋ x ∶ A)
{- context extension lemma -}

ext x Z = Z
ext x (S z≠y p) = S z≠y (x p)


rename : ∀ {Γ Δ}
  → (∀ {x A} → Γ ∋ x ∶ A → Δ ∋ x ∶ A)
     -----------------------------------
  → (∀ {M A} → Γ ⊢ M ∶ A → Δ ⊢ M ∶ A)
{- Γ ⊂ Δ → ( Γ ⊢ A ∶ A → Δ ⊢ M ∶ A ) -}

rename p (⊢Var x) = ⊢Var (p x)
rename p (⊢Lam x) = ⊢Lam (rename (ext p) x)
rename p (⊢∙ x y) = ⊢∙ (rename p x) (rename p y)
rename p ⊢zero = ⊢zero
rename p (⊢suc x) = ⊢suc (rename p x)
rename p (⊢case x y z) = ⊢case (rename p x) (rename p y) (rename (ext p) z)
rename p (⊢mu x) = ⊢mu (rename (ext p) x)


weaken : ∀ {Γ M A}
  → ∅ ⊢ M ∶ A
  → Γ ⊢ M ∶ A
{- ∅ ⊢ M ∶ A → Γ ⊢ M ∶ A -}

weaken {Γ} a = rename p a
  where
  p : ∀ {z C}
    → ∅ ∋ z ∶ C
    → Γ ∋ z ∶ C
  p ()
  {-  ∅ ∋ z ∶ C doesn't have constructors  -}


drop : ∀ {Γ x M A B C}
  → Γ , x ∶ A , x ∶ B ⊢ M ∶ C
  → Γ , x ∶ B ⊢ M ∶ C

drop {Γ} {x} {M} {A} {B} {C} Y = rename p Y
  where
  p : ∀ {z C}
    → Γ , x ∶ A , x ∶ B ∋ z ∶ C
    → Γ , x ∶ B ∋ z ∶ C
  p Z = Z
  p (S x Z) = ⊥-elim (x refl)
  p (S x (S x₁ x₂)) = S x x₂



swap : ∀ {Γ x y M A B C}
  → x ≢ y
  → Γ , y ∶ B , x ∶ A ⊢ M ∶ C
    --------------------------
  → Γ , x ∶ A , y ∶ B ⊢ M ∶ C
  
swap {Γ} {x} {y} {M} {A} {B} {C} x≢y ⊢M = rename ρ ⊢M
  where
  ρ : ∀ {z C}
    → Γ , y ∶ B , x ∶ A ∋ z ∶ C
      --------------------------
    → Γ , x ∶ A , y ∶ B ∋ z ∶ C
  ρ Z                   =  S x≢y Z
  ρ (S z≢x Z)           =  Z
  ρ (S z≢x (S z≢y ∋z))  =  S z≢y (S z≢x ∋z)


substi : ∀ {Γ x N V A B}
  → ∅ ⊢ V ∶ A
  → Γ , x ∶ A ⊢ N ∶ B
    ---------------------
  → Γ ⊢ N [ x := V ] ∶ B
{-
 substitution preserves types

 more generally,    Δ ⊢ V ∶ A
                 → Γ , x ∶ A ⊢ N ∶ B
                   -------------------------
                 → Γ + Δ ⊢ N [ x := V ] ∶ B ?
-}

substi {x = x} ⊢V (⊢Var {x = y} Z)          with y ≟ x
... | yes _                           = weaken ⊢V
... | no  qaq                         = ⊥-elim (qaq refl)
substi {x = x} ⊢V (⊢Var {x = y} (S x≢y z))  with y ≟ x
... | yes refl                        =  ⊥-elim (x≢y refl)
... | no  qwq                         =  ⊢Var z
substi {x = x} ⊢V (⊢Lam {x = y} z)          with y ≟ x
{- x ≟ y  have problem in Goal  -}
... | yes refl                        = ⊢Lam (drop z)
... | no  y≢x                         = ⊢Lam (substi ⊢V (swap y≢x z))
substi ⊢V (⊢∙ z w) = ⊢∙ (substi ⊢V z) (substi ⊢V w)
substi ⊢V ⊢zero = ⊢zero
substi ⊢V (⊢suc y) = ⊢suc (substi ⊢V y)
substi {x = x} ⊢V (⊢case {x = y} ⊢L ⊢M ⊢N)  with y ≟ x
... | yes refl                        = ⊢case (substi ⊢V ⊢L) (substi ⊢V ⊢M) (drop ⊢N)
... | no  qvq                         = ⊢case (substi ⊢V ⊢L) (substi ⊢V ⊢M) (substi ⊢V (swap qvq ⊢N))
substi {x = x} ⊢V (⊢mu {x = y} ⊢M)          with y ≟ x
... | yes refl                        = ⊢mu (drop ⊢M)
... | no  awa                         = ⊢mu (substi ⊢V (swap awa ⊢M))



preserve : ∀ {M N A}
  → ∅ ⊢ M ∶ A
  → M —→ N
    -----------
  → ∅ ⊢ N ∶ A
{- reduction preserve types -}

preserve (⊢∙ x x₂) (xi-r x₁)                  = ⊢∙ (preserve x x₁) x₂
preserve (⊢∙ x x₂) (xi-l x₁ x₃)               = ⊢∙ x (preserve x₂ x₃)
preserve (⊢∙ (⊢Lam x) x₂) (beta-Lam x₁)       = substi x₂ x
preserve (⊢suc x) (xi-suc x₁)                 = ⊢suc (preserve x x₁)
preserve (⊢case x x₂ x₃) (xi-case x₁)         = ⊢case (preserve x x₁) x₂ x₃
preserve (⊢case ⊢zero x₂ x₃) beta-zero        = x₂
preserve (⊢case (⊢suc x) x₂ x₃) (beta-suc x₁) = substi x x₃
preserve (⊢mu x) beta-mu                      = substi (⊢mu x) x


{-
 can evaluate well-typed terms

 evaluation may not terminating
 so bound on the number of reduction steps
-}

record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished (N : Term) : Set where
  done :
       Value N
    → Finished N
    
  out-of-gas :
    Finished N


data Steps (L : Term) : Set where

  steps : ∀ {N}
    → L —↠ N
    → Finished N
      ------------
    → Steps L
{- Given a term L of type A, the evaluator will, for some N, return a reduction sequence from L to N -}

eval : ∀ {L A}
  → Gas
  → ∅ ⊢ L ∶ A
  → Steps L
  
eval {L} (gas zero)         ⊢L = steps (L ∎') out-of-gas
eval {L} (gas (suc amount)) ⊢L with progress ⊢L
... | done VL                    = steps (L ∎') (done VL)
... | step {N} L—→N   with eval (gas amount) (preserve ⊢L L—→N)
...    | steps N—↠M qaq          = steps (L —→⟨ L—→N ⟩ N—↠M ) qaq
{-
 Term L steps to another term M.
 Preservation provides evidence that M is also well typed,
 and we recursively invoke eval on the remaining gas.
 The result is evidence that M —↠ N,
 together with evidence that N is well typed and an indication of whether reduction finished.
 We combine the evidence that L —→ M and M —↠ N to return evidence that L —↠ N,
 together with the other relevant evidence.
 -}

Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

twoᶜ : Term
twoᶜ =  Lam "s" ( Lam "z"  (( Var "s") ∙ ((Var "s") ∙ (Var "z")) ) )

S′ : ∀ {Γ x y A B}
   → {x≢y : False (x ≟ y)}
   → Γ ∋ x ∶ A
     ------------------
   → Γ , y ∶ B ∋ x ∶ A

S′ {x≢y = x≢y} x = S (toWitnessFalse x≢y) x

⊢twoᶜ : ∀ {Γ A} → Γ ⊢ twoᶜ ∶ Ch A
⊢twoᶜ = ⊢Lam (⊢Lam (⊢∙ (⊢Var ∋s) (⊢∙ (⊢Var ∋s) (⊢Var ∋z))))
  where
  ∋s = S′ Z
  ∋z = Z

q = Lam "z" (Var "z")

nope₁ : ∀ {A} → ¬ (∅ ⊢ (Tzero ∙ Tsuc Tzero) ∶ A)
nope₁ (⊢∙ () _)
{-
   ⊢∙ : ∀ {Γ F X A B}
       → Γ ⊢ F ∶ A ⇒ B
       → Γ ⊢ X ∶ A
         ---------------
       → Γ ⊢ F ∙ X ∶ B
  
 -}


nooop : ∀ {A} → ¬ (∅ ⊢ (Case Tzero Tzero "w" (Tzero ∙ Tsuc Tzero)) ∶ A)
nooop (⊢case ⊢zero ⊢zero (⊢∙ ()  _))

subj-exp-counter₁ : ¬ (∀ {M N A} → (∅ ⊢ N ∶ A)  → (M —→ N) → ∅ ⊢ M ∶ A )
{- counterexample of subject expansion -}
  
subj-exp-counter₁ subj-exp = nooop {A = Nat} (subj-exp ⊢zero (beta-zero))


p = Lam "x" Tzero

pa =  (p ∙ (Lam "z" (Tzero ∙ Tzero)))

noop : ∀ {A} →  ¬ (∅ ⊢ pa ∶ A)
noop {A} (⊢∙ _ (⊢Lam (⊢∙ () _)))
       
subj-exp-counter₂ : ¬ (∀ {M N A} → (∅ ⊢ N ∶ A)  → (M —→ N) → ∅ ⊢ M ∶ A )
subj-exp-counter₂  subj-exp = noop (subj-exp ⊢zero ( beta-Lam V-Lam))
{-
 pa —→ Tzero
 -}



em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ k → k (inj₂ (λ x → k (inj₁ x)))




Normal : Term → Set
Normal M = ∀ {N} → ¬ (M —→ N)
{- A term is normal if it cannot reduce -}



ProgressIsNormal : ∀ {X}
  → Progress X
  → Normal X ⊎ ¬ Normal X
ProgressIsNormal {X} (step {N} x) = inj₂ qwq
  where
    qwq : ¬ Normal X
    qwq norx = norx {N = N} x
ProgressIsNormal (done x)         = inj₁ (V¬—→ x)

isNormal : ∀ {X A}
  → ∅ ⊢ X ∶ A
  → Normal X ⊎ ¬ Normal X
isNormal = progress ∘ ProgressIsNormal


Stuck : Term → Set
Stuck  M = Normal M × ¬ Value M 
{- A term is stuck if it is normal and not a value -}

tztz = Tzero ∙ Tzero

nor-tztz : Normal tztz
nor-tztz (xi-r ())
nor-tztz (xi-l V-zero ())

n-v-tztz : ¬ Value tztz
n-v-tztz ()

stuck-tztz : Stuck tztz
stuck-tztz = ⟨ nor-tztz , n-v-tztz ⟩

progunstuck : ∀ {M}
  → Progress M
  → ¬ (Stuck M)
progunstuck {M} (step x) ⟨ fst , snd ⟩ = qwq fst
  where
    qwq : ¬ Normal M
    qwq nor = nor x
progunstuck (done x) ⟨ fst , snd ⟩ = snd x

unstuck : ∀ {M A}
  → ∅ ⊢ M ∶ A
    -----------
  → ¬ (Stuck M)
{- no well-typed term is stuck -}

unstuck (⊢Lam x) ⟨ nor , nv ⟩ = nv V-Lam
unstuck (⊢∙ x y) ⟨ nor , nv ⟩  with progress x
... | step z                   = nor (xi-r z) 
... | done z                     with progress y
...   | step w                    = nor (xi-l z w)
...   | done w                     with z
...     | V-Lam                    = nor (beta-Lam w)
unstuck ⊢zero ⟨ nor , nv ⟩         = nv V-zero
unstuck (⊢suc x) ⟨ nor , nv ⟩      = unstuck x ⟨ xi-suc ∘ nor , V-suc ∘ nv ⟩
unstuck (⊢case x y z) ⟨ nor , nv ⟩ with progress x
... | step qvq                     = nor (xi-case qvq)
... | done w                         with w
... | V-zero                         = nor beta-zero
... | V-suc qaq                      = nor (beta-suc qaq)
unstuck (⊢mu x) ⟨ nor , nv ⟩ = nor beta-mu

unstuck₂ : ∀ {M A}
  → ∅ ⊢ M ∶ A
  → ¬ (Stuck M)
unstuck₂ =  progress ∘ progunstuck


preserves : ∀ {M N A}
  → ∅ ⊢ M ∶ A
  → M —↠ N
    ---------
  → ∅ ⊢ N ∶ A
-- after any number of steps, a well-typed term remains well typed

preserves x (_ ∎') = x
preserves ⊢M (_ —→⟨ M—→X ⟩ X—↠N) = preserves ⊢X X—↠N  
  where
    ⊢X = preserve ⊢M M—→X


wttdgs : ∀ {M N A}
  → ∅ ⊢ M ∶ A
  → M —↠ N
    -----------
  → ¬ (Stuck N)
-- starting from a well-typed term,
-- taking any number of reduction steps leads to a term that is not stuck

wttdgs ⊢M M—↠N = unstuck (preserves ⊢M M—↠N)


cong₄ : ∀ {A B C D E : Set} (f : A → B → C → D → E)
  {s w : A} {t x : B} {u y : C} {v z : D}
  → s ≡ w → t ≡ x → u ≡ y → v ≡ z → f s t u v ≡ f w x y z
cong₄ f refl refl refl refl = refl

det : ∀ {M N L}
  → (M —→ N)
  → (M —→ L)
    --------
  → N ≡ L
{- reduction is deterministic -}

det (xi-r x) (xi-r y)          = cong₂ _∙_ (det x y) refl
det (xi-r x) (xi-l y z)        = ⊥-elim ((V¬—→ y) x)
det (xi-l x z) (xi-r y)        = ⊥-elim ((V¬—→ x) y)
det (xi-l x z) (xi-l y w)      = cong₂ _∙_ refl (det z w)
det (xi-l x z) (beta-Lam y)    = ⊥-elim ((V¬—→ y) z)
det (beta-Lam x) (xi-l y z)    = ⊥-elim ((V¬—→ x) z)
det (beta-Lam x) (beta-Lam y)  = refl
det (xi-suc x) (xi-suc y)      = cong Tsuc (det x y)
det (xi-case x) (xi-case y)    = cong₄ Case (det x y) refl refl refl
det (xi-case x) (beta-suc y)   = ⊥-elim ((V¬—→ (V-suc y)) x)
det beta-zero beta-zero        = refl
det (beta-suc x) (xi-case y)   = ⊥-elim ((V¬—→ (V-suc x)) y)
det (beta-suc x) (beta-suc y)  = refl
det beta-mu beta-mu            = refl
