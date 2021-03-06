 
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open import Data.Vec.Base using (Vec; []; _∷_; lookup)
-- open import Data.Empty using (⊥; ⊥-elim)
-- open import Data.Nat using (ℕ; suc; _<_; _≤?_; z≤n; s≤s)
-- open import Relation.Nullary using (¬_)
-- open import Relation.Nullary.Decidable using (True; toWitness)



{-
record Monoid  : Set₁ where
  infix 7 _∙_
  field
    M : Set
    e : M
    _∙_ : M → M → M
    e-idᵣ : ∀ {x : M} → x ≡ e ∙ x
    e-idₗ : ∀ {x : M} → e ∙ x ≡ x
    assoc : ∀ {x y z : M} → (x ∙ y) ∙ z ≡  x ∙ (y ∙ z)

record Group : Set₁ where
  field
    Mon : Monoid
    inv : Monoid.M Mon → Monoid.M Mon
    inv-idᵣ : ∀ {x : Monoid.M Mon} → (Monoid._∙_ Mon) (inv x) x ≡ Monoid.e Mon
    inv-idₗ : ∀ {x : Monoid.M Mon} → (Monoid._∙_ Mon) x (inv x) ≡ Monoid.e Mon

record CommGroup : Set₁ where
  field
    Grp : Group
    ∙-comm : ∀ {x y : Monoid.M (Group.Mon Grp)} → (Monoid._∙_ (Group.Mon Grp)) x y ≡ (Monoid._∙_ (Group.Mon Grp)) y x
-}



module alg-ex-nested where

  data Nat : Set where
    Z : Nat
    S : Nat → Nat

  data Fin : Nat → Set where
    Z : {n : Nat} → Fin (S n)
    S : {n : Nat} (i : Fin n) → Fin (S n)

  record Monoid (M : Set) : Set₁ where
    field
      e   : M
      _∙_ : M → M → M
    field
      e-idᵣ : ∀ {x : M} → x ∙ e ≡ x
      e-idₗ : ∀ {x : M} → e ∙ x ≡ x
      assoc : ∀ {x y z : M} → (x ∙ y) ∙ z ≡  x ∙ (y ∙ z)

  record Group (G : Set) : Set₁ where
    field
      Mon : Monoid G
    open Monoid Mon
    field
      inv : G → G
    field
      inv-idᵣ : ∀ {x : G} → x ∙ (inv x) ≡ e
      inv-idₗ : ∀ {x : G} → (inv x) ∙ x ≡ e

  record AbGroup (G : Set) : Set₁ where
    field
      Grp : Group G
    open Group Grp
    open Monoid Mon
    field
      comm-∙ : ∀ {x y : G} → x ∙ y ≡ y ∙ x

  record Ring (R : Set) : Set₁ where
    field
      +-AbGrp : AbGroup R
      ∙-Monoid : Monoid R
    open AbGroup +-AbGrp renaming (comm-∙ to comm-+)
    open Group Grp renaming (inv to -_)
    open Monoid Mon renaming (_∙_ to _+_; e to zero)
    open Monoid ∙-Monoid
    field
      ∙-distrib-+ᵣ : ∀ {x y z : R} → (x ∙ (y + z)) ≡ (x ∙ y) + (x ∙ z)
      ∙-distrib-+ₗ : ∀ {x y z : R} → ((x + y) ∙ z) ≡ (x ∙ z) + (y ∙ z)
      zero-idᵣ : ∀ {x : R} → zero ∙ x ≡ zero
      zero-idₗ : ∀ {x : R} → x ∙ zero ≡ zero

  record CommRing (R : Set) : Set₁ where
    field
      Ring-R : Ring R
    open Ring Ring-R
    open Monoid ∙-Monoid
    field
      comm-∙ : ∀ {x y : R} → x ∙ y ≡ y ∙ x

  data Without (F : Set) (z : F) : Set where
    intro : (x : F) → x ≢ z → Without F z

  record RealWithout (F : Set) (z : F) : Set where
    field
      WithoutFz : Without F z
    field
      embed : (x : Without F z) → F
      elim  : (x : Without F z) → embed x ≢ z
      embed-intro-id : ∀ {x : Without F z} → x ≡ intro (embed x) (elim x)
      intro-embed-id : ∀ {x : F} → (x≢z : x ≢ z) → embed (intro x x≢z) ≡ x

  
  record Field (F : Set) : Set₁ where
    field
      CRing-F : CommRing F
    open CommRing CRing-F
    open Ring Ring-R
    open AbGroup +-AbGrp renaming (comm-∙ to comm-+)
    open Group Grp renaming (inv to -_; inv-idᵣ to -idᵣ; inv-idₗ to -idₗ)
    open Monoid Mon renaming (_∙_ to _+_; e to zero)
    field
      inv : Without F zero → F
      Real : RealWithout F zero
    open Monoid ∙-Monoid
    open RealWithout Real
    field
      inv-idᵣ : ∀ {x : Without F zero} →  (embed x) ∙ (inv x) ≡ e
      inv-idₗ : ∀ {x : Without F zero} →  (inv x) ∙ (embed x) ≡ e
  {-
  Define Field By multiplication subgroup
  record Field (F : Set) : Set₁ where
    field
      CRing-F : CommRing F
    open CommRing CRing-F
    open Ring Ring-R
    open AbGroup +-AbGrp renaming (comm-∙ to comm-+)
    open Group Grp renaming (inv to -_; inv-idᵣ to -idᵣ; inv-idₗ to -idₗ)
    open Monoid Mon renaming (_∙_ to _+_; e to zero)
    field
      Real : RealWithout F zero
    open Monoid ∙-Monoid
    open RealWithout Real
    field
      ∙-Grp : Group (Without F zero)
      z : Group.Mon ∙-Grp ≡ ∙-Monoid
    -}


  data Poly-x (R : Set) : Set where
    inj : R → Poly-x R
    x   : Poly-x R
    _^_ : Poly-x R → Nat → Poly-x R
    

  record Polyno-x (R : Set) (CR : CommRing R) : Set₁ where
    open CommRing CR
    open Ring Ring-R
    open AbGroup +-AbGrp renaming (comm-∙ to comm-+)
    open Group Grp renaming (inv to -_; inv-idᵣ to -idᵣ; inv-idₗ to -idₗ)
    open Monoid Mon renaming (_∙_ to _+R_; e to zero)
    open Monoid ∙-Monoid renaming (_∙_ to _∙R_)
    field
      _+_ : Poly-x R → Poly-x R → Poly-x R
      _∙_ : Poly-x R → Poly-x R → Poly-x R
      ^-inj : ∀ {r : R} {n : Nat} → inj r ^ S n ≡ inj (r ∙R r) ^ n
      +-inj : ∀ {r s : R} → inj r + inj s ≡ inj (s +R r)
      ∙-inj : ∀ {r s : R} → inj r ∙ inj s ≡ inj (s ∙R r)
      ^-x   : ∀ {n : Nat} → x ^ S n ≡ x ∙ (x ^ n)

  PolyisCRing : ∀ {R CR}
              → Polyno-x R CR
              → CommRing (Poly-x R)
  Monoid.e (Group.Mon (AbGroup.Grp (Ring.+-AbGrp (CommRing.Ring-R (PolyisCRing {R} {CR} record { _+_ = _+_ ; _∙_ = _∙_ ; ^-inj = ^-inj ; +-inj = +-inj ; ∙-inj = ∙-inj ; ^-x = ^-x }))))) = inj (Monoid.e (Group.Mon (AbGroup.Grp (Ring.+-AbGrp (CommRing.Ring-R CR)))))
  Monoid._∙_ (Group.Mon (AbGroup.Grp (Ring.+-AbGrp (CommRing.Ring-R (PolyisCRing {R} {CR} record { _+_ = _+_ ; _∙_ = _∙_ ; ^-inj = ^-inj ; +-inj = +-inj ; ∙-inj = ∙-inj ; ^-x = ^-x }))))) = _+_
  Monoid.e-idᵣ (Group.Mon (AbGroup.Grp (Ring.+-AbGrp (CommRing.Ring-R (PolyisCRing {R} {CR} record { _+_ = _+_ ; _∙_ = _∙_ ; ^-inj = ^-inj ; +-inj = +-inj ; ∙-inj = ∙-inj ; ^-x = ^-x }))))) {x₁} = {!!}
  Monoid.e-idₗ (Group.Mon (AbGroup.Grp (Ring.+-AbGrp (CommRing.Ring-R (PolyisCRing {R} {CR} record { _+_ = _+_ ; _∙_ = _∙_ ; ^-inj = ^-inj ; +-inj = +-inj ; ∙-inj = ∙-inj ; ^-x = ^-x }))))) = {!!}
  Monoid.assoc (Group.Mon (AbGroup.Grp (Ring.+-AbGrp (CommRing.Ring-R (PolyisCRing {R} {CR} record { _+_ = _+_ ; _∙_ = _∙_ ; ^-inj = ^-inj ; +-inj = +-inj ; ∙-inj = ∙-inj ; ^-x = ^-x }))))) = {!!}
  Group.inv (AbGroup.Grp (Ring.+-AbGrp (CommRing.Ring-R (PolyisCRing {R} {CR} record { _+_ = _+_ ; _∙_ = _∙_ ; ^-inj = ^-inj ; +-inj = +-inj ; ∙-inj = ∙-inj ; ^-x = ^-x })))) = {!!}
  Group.inv-idᵣ (AbGroup.Grp (Ring.+-AbGrp (CommRing.Ring-R (PolyisCRing {R} {CR} record { _+_ = _+_ ; _∙_ = _∙_ ; ^-inj = ^-inj ; +-inj = +-inj ; ∙-inj = ∙-inj ; ^-x = ^-x })))) = {!!}
  Group.inv-idₗ (AbGroup.Grp (Ring.+-AbGrp (CommRing.Ring-R (PolyisCRing {R} {CR} record { _+_ = _+_ ; _∙_ = _∙_ ; ^-inj = ^-inj ; +-inj = +-inj ; ∙-inj = ∙-inj ; ^-x = ^-x })))) = {!!}
  AbGroup.comm-∙ (Ring.+-AbGrp (CommRing.Ring-R (PolyisCRing {R} {CR} record { _+_ = _+_ ; _∙_ = _∙_ ; ^-inj = ^-inj ; +-inj = +-inj ; ∙-inj = ∙-inj ; ^-x = ^-x }))) = {!!}
  Monoid.e (Ring.∙-Monoid (CommRing.Ring-R (PolyisCRing {R} {CR} record { _+_ = _+_ ; _∙_ = _∙_ ; ^-inj = ^-inj ; +-inj = +-inj ; ∙-inj = ∙-inj ; ^-x = ^-x }))) = inj ( Monoid.e (Ring.∙-Monoid (CommRing.Ring-R CR)))
  Monoid._∙_ (Ring.∙-Monoid (CommRing.Ring-R (PolyisCRing {R} {CR} record { _+_ = _+_ ; _∙_ = _∙_ ; ^-inj = ^-inj ; +-inj = +-inj ; ∙-inj = ∙-inj ; ^-x = ^-x }))) = {!!}
  Monoid.e-idᵣ (Ring.∙-Monoid (CommRing.Ring-R (PolyisCRing {R} {CR} record { _+_ = _+_ ; _∙_ = _∙_ ; ^-inj = ^-inj ; +-inj = +-inj ; ∙-inj = ∙-inj ; ^-x = ^-x }))) = {!!}
  Monoid.e-idₗ (Ring.∙-Monoid (CommRing.Ring-R (PolyisCRing {R} {CR} record { _+_ = _+_ ; _∙_ = _∙_ ; ^-inj = ^-inj ; +-inj = +-inj ; ∙-inj = ∙-inj ; ^-x = ^-x }))) = {!!}
  Monoid.assoc (Ring.∙-Monoid (CommRing.Ring-R (PolyisCRing {R} {CR} record { _+_ = _+_ ; _∙_ = _∙_ ; ^-inj = ^-inj ; +-inj = +-inj ; ∙-inj = ∙-inj ; ^-x = ^-x }))) = {!!}
  Ring.∙-distrib-+ᵣ (CommRing.Ring-R (PolyisCRing {R} {CR} record { _+_ = _+_ ; _∙_ = _∙_ ; ^-inj = ^-inj ; +-inj = +-inj ; ∙-inj = ∙-inj ; ^-x = ^-x })) = {!!}
  Ring.∙-distrib-+ₗ (CommRing.Ring-R (PolyisCRing {R} {CR} record { _+_ = _+_ ; _∙_ = _∙_ ; ^-inj = ^-inj ; +-inj = +-inj ; ∙-inj = ∙-inj ; ^-x = ^-x })) = {!!}
  Ring.zero-idᵣ (CommRing.Ring-R (PolyisCRing {R} {CR} record { _+_ = _+_ ; _∙_ = _∙_ ; ^-inj = ^-inj ; +-inj = +-inj ; ∙-inj = ∙-inj ; ^-x = ^-x })) = {!!}
  Ring.zero-idₗ (CommRing.Ring-R (PolyisCRing {R} {CR} record { _+_ = _+_ ; _∙_ = _∙_ ; ^-inj = ^-inj ; +-inj = +-inj ; ∙-inj = ∙-inj ; ^-x = ^-x })) = {!!}
  CommRing.comm-∙ (PolyisCRing {R} {CR} record { _+_ = _+_ ; _∙_ = _∙_ ; ^-inj = ^-inj ; +-inj = +-inj ; ∙-inj = ∙-inj ; ^-x = ^-x }) = {!!}
    
      
  

  record Polynomial-x (F : Set) (Fi : Field F) : Set₁ where
    open Field Fi
    open CommRing CRing-F
    open Ring Ring-R
    open AbGroup +-AbGrp renaming (comm-∙ to comm-+)
    open Group Grp renaming (inv to -_; inv-idᵣ to -idᵣ; inv-idₗ to -idₗ)
    open Monoid Mon renaming (_∙_ to _+_; e to zero)
    field
      isCRing : CommRing (Poly-x F)
 


  data Nat+ : Set where
    nat : Nat → Nat+
    inf  : Nat+



{-
I(_,_∩_) : ∀ {K}
  → AffineSpace
  → Poly
  → Poly
  → Nat+
-}
