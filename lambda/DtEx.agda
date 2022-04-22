 
module DtEx where

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

Id = String

TyVar = Id

TmVar = Id

infix 7 _⇒_
infix 7 ƛ_⦂_,_
infix 8 _∙_
infix 7 Λ_,_
infix 8 _∘_

data Ty : Set where
  tyVar : TyVar -> Ty
  _⇒_   : Ty -> Ty -> Ty
  Pi    : TyVar -> Ty -> Ty

data Tm : Set where
  tmVar : TmVar -> Tm
  ƛ_⦂_,_ : TmVar -> Ty -> Tm -> Tm
  _∙_   : Tm -> Tm -> Tm
  Λ_,_  : TyVar -> Tm -> Tm
  _∘_   : Tm -> Ty -> Tm

data Subst : Set where
  id : Subst
  _comp_ : Subst -> Subst -> Subst
  Tm⟨_,_≔_⟩ : Subst -> TmVar -> Tm -> Subst
  Ty⟨_,_≔_⟩ : Subst -> TyVar -> Ty -> Subst

data Cxt : Set where
  nil : Cxt
  tyv : Cxt -> TyVar ->  Cxt -- ty(pe) v(ariable)
  tmv : Cxt -> TmVar -> Ty -> Cxt -- t(er)m v(ariable)

infix 4 _∋Ty_
infix 4 _∋Tm_

-- lookup type variable
data _∋Ty_ : Cxt -> TyVar -> Set where
  Z∋Ty : ∀ {Γ X}
    -> tyv Γ X ∋Ty X
  S∋Ty : ∀ {Γ X Y}
    -> X ≢ Y
    -> Γ ∋Ty X
    -> tyv Γ Y ∋Ty X

-- lookup term variable
data _∋Tm_ : Cxt -> TmVar -> Set where
  Z∋Tm : ∀ {Γ x A}
    -> tmv Γ x A ∋Tm x
  S∋Tm : ∀ {Γ x y B}
    -> x ≢ y
    -> Γ ∋Tm x
    -> tmv Γ y B ∋Tm x

data _∌Ty_ : Cxt -> TyVar -> Set where
  Z∌Ty : ∀ {X}
    -> nil ∌Ty X
  S∌Ty : ∀ {Γ X Y}
    -> X ≢ Y
    -> Γ ∌Ty X
    -> tyv Γ Y ∌Ty X


data _∌Tm_ : Cxt -> TmVar -> Set where
  Z∌Tm : ∀ {x}
    -> nil ∌Tm x
  S∌Tm : ∀ {Γ x y S}
    -> x ≢ y
    -> Γ ∌Tm x
    -> tmv Γ y S ∌Tm x

    
-- find type of given term variable
data _⟨_⟩=_ : Cxt -> TmVar -> Ty -> Set where
  Z⟨⟩= : ∀ {Γ x A}
    -> (tmv Γ x A) ⟨ x ⟩= A
  S⟨⟩= : ∀ {Γ x y A B}
    -> x ≢ y
    -> Γ ⟨ x ⟩= A
    -> (tmv Γ y B) ⟨ x ⟩= A


infix 3.4 _⊢_

-- well-formed types
data _⊢_ : Cxt ->  Ty -> Set where
  ⊢∋Ty : ∀ {Γ X}
         -> Γ ∋Ty X
         → Γ ⊢ tyVar X
  ⊢⇒  : ∀ {Γ S T}
         -> Γ ⊢ S
         -> Γ ⊢ T
         -> Γ ⊢ S ⇒ T
  ⊢Pi  : ∀ {Γ X T}
         -> tyv Γ X ⊢ T
         -> Γ ⊢ Pi X T


-- well-formed contexts
data ⊢C : Cxt -> Set where
  ⊢C-nil : ⊢C nil
  ⊢C-extTy : ∀ {Γ X}
             -> ⊢C Γ
             -> ⊢C (tyv Γ X)
  ⊢C-extTm : ∀ {Γ x S}
             -> ⊢C Γ
             -> Γ ⊢ S
             -> ⊢C (tmv Γ x S)
             
infix 3.2 _⊢T_⦂_
infix 3 _⊢S_⦂_


infix 4.5 _Ty[_≔_]
infix 4.5 _Tm[_≔_]
infix 4.5 _Tm[_≔Ty_] 
infix 4.3 _Ty[_]
infix 4.3 _Tm[_]

-- substitute one type for a type variable in another type
_Ty[_≔_] : Ty -> TyVar -> Ty -> Ty
tyVar Y Ty[ X ≔ S ] with Y ≟ X
... | yes _         = S
... | no  _         = tyVar Y
(T ⇒ T') Ty[ X ≔ S ] = (T Ty[ X ≔ S ]) ⇒ (T' Ty[ X ≔ S ])
Pi Y T Ty[ X ≔ S ]  with Y ≟ X
... | yes _         = Pi Y T
... | no  _         = Pi Y (T Ty[ X ≔ S ])

_Tm[_≔_] : Tm -> TmVar -> Tm -> Tm
tmVar y Tm[ x ≔ s ] with y ≟ x
... | yes _         = s
... | no  _         = tmVar y
ƛ y ⦂ A , t Tm[ x ≔ s ] with y ≟ x
... | yes _         = ƛ y ⦂ A , t
... | no  _         = ƛ y ⦂ A , (t Tm[ x ≔ s ])
t ∙ t' Tm[ x ≔ s ]  = (t Tm[ x ≔ s ]) ∙ (t' Tm[ x ≔ s ])
Λ X , t Tm[ x ≔ s ] with X ≟ x
... | yes _         = Λ X , t
... | no  _         = Λ X , (t Tm[ x ≔ s ])
r ∘ S Tm[ x ≔ s ] = (r Tm[ x ≔ s ]) ∘ S

_Tm[_≔Ty_] : Tm -> TyVar -> Ty -> Tm
tmVar y Tm[ X ≔Ty S ] with y ≟ X
... | yes _         = tmVar y
... | no  _         = tmVar y
ƛ y ⦂ A , t Tm[ X ≔Ty S ] with y ≟ X
... | yes _         = ƛ y ⦂ (A Ty[ X ≔ S ]) , (t Tm[ X ≔Ty S ])
... | no  _         = ƛ y ⦂ (A Ty[ X ≔ S ]) , (t Tm[ X ≔Ty S ])
t ∙ t' Tm[ X ≔Ty S ]  = (t Tm[ X ≔Ty S ]) ∙ (t' Tm[ X ≔Ty S ])
Λ Y , t Tm[ X ≔Ty S ] with Y ≟ X
... | yes _         = Λ Y , t
... | no  _         = Λ Y , (t Tm[ X ≔Ty S ])
r ∘ T Tm[ X ≔Ty S ] = (r Tm[ X ≔Ty S ]) ∘ (T Ty[ X ≔ S ])

_Ty[_] : Ty -> Subst -> Ty
T Ty[ id ] = T
T Ty[ σ comp τ ] = (T Ty[ τ ]) Ty[ σ ]
T Ty[ Tm⟨ σ , x ≔ s ⟩ ] = T Ty[ σ ]
T Ty[ Ty⟨ σ , X ≔ S ⟩ ] = T Ty[ X ≔ S ] Ty[ σ ]

_Tm[_] : Tm -> Subst -> Tm
t Tm[ id ] = t
t Tm[ σ comp τ ] = (t Tm[ τ ]) Tm[ σ ]
t Tm[ Tm⟨ σ , x ≔ s ⟩ ] = t Tm[ x ≔ s ] Tm[ σ ] 
t Tm[ Ty⟨ σ , X ≔ S ⟩ ] = t Tm[ X ≔Ty S ] Tm[ σ ]


data _⊢S_⦂_ : Cxt -> Subst -> Cxt -> Set

-- Tying
data _⊢T_⦂_ : Cxt -> Tm -> Ty -> Set where
  ⊢T-⟨⟩= : ∀ {Γ x S}
           -> ⊢C Γ
           -> Γ ⟨ x ⟩= S
           -> Γ ⊢T tmVar x ⦂ S
  ⊢T-ƛ   : ∀ {Γ x S t T}
           -> tmv Γ x S ⊢T t ⦂ T

  ⊢T-∙   : ∀ {Γ r S T s}
           -> Γ ⊢T r ⦂ S ⇒ T
           -> Γ ⊢T s ⦂ S
           -> Γ ⊢T r ∙ s ⦂ T
  ⊢T-Λ   : ∀ {Γ X t T}
           -> tyv Γ X ⊢T t ⦂ T
           -> Γ ⊢T Λ X , t ⦂ Pi X T
  ⊢T-∘   : ∀ {Γ r X T S}
           -> Γ ⊢T r ⦂ Pi X T
           -> Γ ⊢ S
           -> Γ ⊢T r ∘ S ⦂ T Ty[ X ≔ S ]
  ⊢T-Sb  : ∀ {Γ σ Δ t T}
           -> Γ ⊢S σ ⦂ Δ
           -> Δ ⊢T t ⦂ T
           -> Γ ⊢T t Tm[ σ ] ⦂ T Ty[ σ ]


infix 3.1 _≤C_ 
-- Context extension 
data _≤C_ : Cxt -> Cxt -> Set where
  ≤C-id  : ∀ {Γ}
           -> Γ ≤C Γ
  ≤C-extTy  : ∀ {Γ' Γ X}
              -> Γ' ≤C Γ
              -> tyv Γ' X ≤C Γ
  ≤C-extTm  : ∀ {Γ' Γ x S}
              -> Γ' ≤C Γ
              -> Γ' ⊢ S
              -> tmv Γ' x S ≤C Γ
  ≤C-conTy  : ∀ {Γ' Γ X}
              -> Γ' ≤C Γ
              -> tyv Γ' X ≤C tyv Γ X
  ≤C-conTm  : ∀ {Γ' Γ x S}
              -> Γ' ≤C Γ
              -> Γ ⊢ S
              -> tmv Γ' x S ≤C tmv Γ x S
             

-- Substitution typing
data _⊢S_⦂_ where
  ⊢S-id   : ∀ {Γ}
            -> Γ ⊢S id ⦂ Γ
  ⊢S-comp : ∀ {Γ₁ Γ₂ Γ₃ τ σ}
            -> Γ₁ ⊢S τ ⦂ Γ₂
            -> Γ₂ ⊢S σ ⦂ Γ₃
            -> Γ₁ ⊢S σ comp τ ⦂ Γ₃
  ⊢S-≤C   : ∀ {Γ σ Δ' Δ}
            -> Γ ⊢S σ ⦂ Δ'
            -> Δ' ≤C Δ
            -> Γ ⊢S σ ⦂ Δ
  ⊢S-TmSb : ∀ {Γ σ Δ S s x}
            -> Γ ⊢S σ ⦂ Δ
            -> Δ ⊢ S
            -> Γ ⊢T s ⦂ S Ty[ σ ]
            -> Γ ⊢S Tm⟨ σ , x ≔ s ⟩ ⦂ tmv Δ x S
  ⊢S-TySb : ∀ {Γ σ Δ S X}
            -> Γ ⊢S σ ⦂ Δ
            -> Γ ⊢ S
            -> Γ ⊢S Ty⟨ σ , X ≔ S ⟩ ⦂ tyv Δ X


infix 2.4 _⊢Eq_≡_⦂_

data _⊢Eq_≡_⦂_ : Cxt -> Tm -> Tm -> Ty -> Set where
  ⊢Eq-Tmβ : ∀ {Γ x S t T s}
            -> tmv Γ x S ⊢T t ⦂ T
            -> Γ ⊢T s ⦂ S
            -> Γ ⊢Eq (ƛ x ⦂ S , t) ∙ s ≡ t Tm[ x ≔ s ] ⦂ T
  ⊢Eq-Tyβ : ∀ {Γ X t T S}
            -> tyv Γ X ⊢T t ⦂ T
            -> Γ ⊢ S
            -> Γ ⊢Eq (Λ X , t) ∘ S ≡ t Tm[ Ty⟨ id , X ≔ S ⟩ ] ⦂ T Ty[ Ty⟨ id , X ≔ S ⟩ ]
  ⊢Eq-Tmη : ∀ {Γ t S T x}
            -> Γ ∌Tm x
            -> Γ ⊢T t ⦂ S ⇒ T
            -> Γ ⊢Eq t ≡ (ƛ x ⦂ S , t) ∙ (tmVar x) ⦂ S ⇒ T
  ⊢Eq-Tyη : ∀ {Γ t X T}
            -> Γ ∌Ty X
            -> Γ ⊢T t ⦂ Pi X T
            -> Γ ⊢Eq t ≡ (Λ X , t) ∘ (tyVar X) ⦂ Pi X T

data Nf : Set

data Ne : Set where
  neVar : TmVar -> Ne
  ne-∙  : Ne -> Nf -> Ne
  ne-∘  : Ne -> Ty -> Ne

data Nf where
  nfNe  : Ne -> Nf
  nf-ƛ_⦂_,_  : TmVar -> Ty -> Tm -> Nf
  nf-Λ_,_    : TyVar -> Tm -> Nf

data D : Set
data Dne : Set
data Dnf : Set
data Env : Set

data D where
  cl-ƛ : TmVar -> Ty ->  Tm -> Env -> D
  cl-Λ : TyVar -> Tm -> Env -> D
  ↑Ne  : Ty -> Dne -> D

data Dne where
  dneVar : TmVar -> Dne
  dne-∙  : Dne -> Dnf -> Dne
  dne-∘  : Dne -> Ty  -> Dne

data Dnf where
     ↓Nf : Ty -> D -> Dnf

data Env where
  empty : Env
  ⟨_,_/N_⟩ : Env -> Dnf -> TmVar -> Env
  ⟨_,_/T_⟩ : Env -> Ty -> TyVar ->  Env

infix 1.8 _⋆_
infix 1.8 _⋆'_
infix 2 ⦅_⦆_

Dnf2Tm : Dnf -> Tm
Dnf2Tm (↓Nf T (cl-ƛ x S x₁ x₂)) = {!!}
Dnf2Tm (↓Nf T (cl-Λ x x₁ x₂)) = {!!}
Dnf2Tm (↓Nf T (↑Ne x x₁)) = {!!}

Env2Sb : Env -> Subst
Env2Sb empty = id
Env2Sb ⟨ η , d /N x ⟩ = {!Tm⟨ Env2Sb η , x ≔  ⟩!}
Env2Sb ⟨ η , S /T X ⟩ = Ty⟨ Env2Sb η , X ≔ S ⟩

_⋆_ : D -> D -> D
_⋆'_ : D -> Ty -> D
⦅_⦆_ : Tm -> Env -> D
{-# TERMINATING #-}

⦅ tmVar x ⦆ η = {!!}
⦅ ƛ x ⦂ S , t ⦆ η = cl-ƛ x S t η
⦅ r ∙ s ⦆ η = ⦅ r ⦆ η ⋆ ⦅ s ⦆ η 
⦅ Λ X , t ⦆ η = cl-Λ X t η
⦅ r ∘ S ⦆ η = ⦅ r ⦆ η ⋆' S Ty[ Env2Sb η ]


cl-ƛ x S t η ⋆ a = ⦅ t ⦆ ⟨ η , ↓Nf S a /N x ⟩
cl-Λ x x₁ x₂ ⋆ a = {!!}
↑Ne (tyVar x) e ⋆ a = {!!}
↑Ne (x ⇒ x₁) e ⋆ a = {!!}
↑Ne (Pi x x₁) e ⋆ a = {!!}
