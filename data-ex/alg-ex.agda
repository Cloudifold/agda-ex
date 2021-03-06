import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong)
open import Data.Vec.Base using (Vec; []; _∷_; lookup)

open import Data.Product using (Σ; _×_; _,_)

open import Level

open import Data.Empty using (⊥; ⊥-elim)
-- open import Data.Nat using (ℕ; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Nullary using (¬_)
-- open import Relation.Nullary.Decidable using (True; toWitness)

{-
 need qoutient !
 -}

module alg-ex where

  infixl 4 _⋆_

  _⋆_ : ∀ {v : Level} {A : Set v} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
  _⋆_ = trans

  _∘_ : ∀ {a  : Level} {A B C : Set a} → (A → B) → (B → C) → (A → C)
  (f ∘ g) x = g (f x)

  infix 2 Σ-syntax
  
  Σ-syntax : ∀ {a b : Level} → (A : Set a) → (A → Set b) → Set (a ⊔ b)
  Σ-syntax = Σ
  
  syntax Σ-syntax A (λ x → B) = ∃[ x ∈ A ] B

  ∄-syntax : ∀ {a b : Level} → (A : Set a) → (A → Set b) → Set (a ⊔ b)
  ∄-syntax A P = ¬ (Σ A P)

  syntax ∄-syntax A (λ x → B) = ∄[ x ∈ A ] B


  data Nat : Set where
    Z : Nat
    S : Nat → Nat

  data Fin : Nat → Set where
    Zf : {n : Nat} → Fin (S n)
    Sf : {n : Nat} (i : Fin n) → Fin (S n)

  fin-inj : ∀ {n : Nat} → Fin n → Fin (S n)
  fin-inj = Sf


  itr : ∀ {a : Level} {A : Set a} → (A → A) → Nat → A → A
  itr f Z x = x
  itr f (S n) = f ∘ (itr f n)

  subset :  (A : Set) → (A → Set) → Set
  subset A P  = Σ A P

  syntax subset A (λ x → B) = [ x ∈ A ∣ B ]
  -- a , b : [ x ∈ A | P x ]
  -- a : A
  -- b : P x

  




  record Ring (R : Set) : Set₁ where
    field
      z    : R
      e    : R
      _+_  : R → R → R
      _∙_  : R → R → R
      -_   : R → R
    field
      +-assoc      : ∀ {x y z} → (x + y) + z ≡ x + (y + z)
      ∙-assoc      : ∀ {x y z} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
      +-comm       : ∀ {x y}   → x + y ≡ y + x
      e-idᵣ        : ∀ {x}     → x ∙ e ≡ x
      e-idₗ        : ∀ {x}     → e ∙ x ≡ x
      z-id         : ∀ {x}     → x + z ≡ x
      ∙-distrib-+ᵣ : ∀ {x y z} → (x ∙ (y + z)) ≡ (x ∙ y) + (x ∙ z)
      ∙-distrib-+ₗ : ∀ {x y z} → ((x + y) ∙ z) ≡ (x ∙ z) + (y ∙ z)
      -inv-+       : ∀ {x}     → x + (- x) ≡ z

  record CRing (R : Set) : Set where
    field
      z    : R
      e    : R
      _+_  : R → R → R
      _∙_  : R → R → R
      -_   : R → R
    field
      +-assoc      : ∀ {x y z} → (x + y) + z ≡ x + (y + z)
      ∙-assoc      : ∀ {x y z} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
      +-comm       : ∀ {x y}   → x + y ≡ y + x
      ∙-comm       : ∀ {x y}   → x ∙ y ≡ y ∙ x
      e-id         : ∀ {x}     → x ∙ e ≡ x
      z-id         : ∀ {x}     → x + z ≡ x
      ∙-distrib-+ᵣ : ∀ {x y z} → (x ∙ (y + z)) ≡ (x ∙ y) + (x ∙ z)
      ∙-distrib-+ₗ : ∀ {x y z} → ((x + y) ∙ z) ≡ (x ∙ z) + (y ∙ z)
      -inv-+       : ∀ {x}     → x + (- x) ≡ z

  _\-_ : (R : Set) → (s : R) →  Set
  R \- s = [ x ∈ R ∣ x ≢ s ]



  intro- : ∀ {R s} → R \- s → R
  intro- (x , x≢s) = x

  

  record Field (R : Set) : Set where
    field
      z    : R
      e    : R
      _+_  : R → R → R
      _∙_  : R → R → R
      -_   : R → R
      inv_ : R \- z → R \- z
    field
      +-assoc      : ∀ {x y z} → (x + y) + z ≡ x + (y + z)
      ∙-assoc      : ∀ {x y z} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
      +-comm       : ∀ {x y}   → x + y ≡ y + x
      ∙-comm       : ∀ {x y}   → x ∙ y ≡ y ∙ x
      e-id         : ∀ {x}     → x ∙ e ≡ x
      z-id         : ∀ {x}     → x + z ≡ x
      ∙-distrib-+ᵣ : ∀ {x y z} → (x ∙ (y + z)) ≡ (x ∙ y) + (x ∙ z)
      ∙-distrib-+ₗ : ∀ {x y z} → ((x + y) ∙ z) ≡ (x ∙ z) + (y ∙ z)
      -inv-+       : ∀ {x}     → x + (- x) ≡ z
      inv-inv-∙    : ∀ {x}     → intro- (inv x) ∙ intro- x ≡ e
      z≢e          : z ≢ e

  FieldisCRing : ∀ {R} → (FR : Field R) → CRing R
  FieldisCRing record { z = z ; e = e ; _+_ = _+_ ; _∙_ = _∙_ ; -_ = -_ ; inv_ = inv_ ;
                        +-assoc = +-assoc ; ∙-assoc = ∙-assoc ; +-comm = +-comm ; ∙-comm = ∙-comm ;
                        e-id = e-id ; z-id = z-id ; ∙-distrib-+ᵣ = ∙-distrib-+ᵣ ; ∙-distrib-+ₗ = ∙-distrib-+ₗ
                        ; -inv-+ = -inv-+ ; inv-inv-∙ = inv-inv-∙ ; z≢e = z≢e }
                      =
               record { z = z ; e = e ; _+_ = _+_ ; _∙_ = _∙_ ; -_ = -_ ;
                        +-assoc = +-assoc ; ∙-assoc = ∙-assoc ; +-comm = +-comm ; ∙-comm = ∙-comm ;
                        e-id = e-id ; z-id = z-id ; ∙-distrib-+ᵣ = ∙-distrib-+ᵣ ; ∙-distrib-+ₗ = ∙-distrib-+ₗ
                        ; -inv-+ = -inv-+  }



  record Poly-x (R : Set) (CR : CRing R) : Set₁ where
    field
      P     : Set
      x     : P
      inj   : R → P
      _+_   : P → P → P
      _∙_   : P → P → P
      -_    : P → P
    open CRing CR renaming (_+_ to _+R_; -_ to -R_; _∙_ to _∙R_)
    field
      +-assoc      : ∀ {x y z} → (x + y) + z ≡ x + (y + z)
      ∙-assoc      : ∀ {x y z} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
      +-comm       : ∀ {x y}   → x + y ≡ y + x
      ∙-comm       : ∀ {x y}   → x ∙ y ≡ y ∙ x
      inje-id         : ∀ {x}     → x ∙ (inj e) ≡ x
      injz-id         : ∀ {x}     → x + (inj z) ≡ x
      ∙-distrib-+ᵣ : ∀ {x y z} → (x ∙ (y + z)) ≡ (x ∙ y) + (x ∙ z)
      ∙-distrib-+ₗ : ∀ {x y z} → ((x + y) ∙ z) ≡ (x ∙ z) + (y ∙ z)
      -inv-+       : ∀ {x}     → x + (- x) ≡ inj z 
      +-inj        : ∀ {x y}   → inj x + inj y ≡ inj (x +R y)
      ∙-inj        : ∀ {x y}   → inj x ∙ inj y ≡ inj (x ∙R y)

  Poly-x-isCRing : ∀ {R CR}
                 → (Px : Poly-x R CR)
                 → CRing (Poly-x.P Px)
  Poly-x-isCRing {R} {CR}
    record { P = P ; x = x ; inj = inj ; _+_ = _+_ ; _∙_ = _∙_ ; -_ = -_ ;
             +-assoc = +-assoc ; ∙-assoc = ∙-assoc ; +-comm = +-comm ; ∙-comm = ∙-comm ;
             inje-id = inje-id ; injz-id = injz-id ; ∙-distrib-+ᵣ = ∙-distrib-+ᵣ ; ∙-distrib-+ₗ = ∙-distrib-+ₗ ;
             -inv-+ = -inv-+ ; +-inj = +-inj ; ∙-inj = ∙-inj }
           =
    record { z = inj (CRing.z CR) ; e = inj (CRing.e CR) ; _+_ = _+_ ; _∙_ = _∙_ ; -_ = -_ ;
             +-assoc = +-assoc ; ∙-assoc = ∙-assoc ; +-comm = +-comm ; ∙-comm = ∙-comm ;
             e-id = inje-id ; z-id = injz-id ; ∙-distrib-+ᵣ = ∙-distrib-+ᵣ ; ∙-distrib-+ₗ = ∙-distrib-+ₗ ;
             -inv-+ = -inv-+ }

  record Domain (R : Set) : Set where
    field
      z    : R
      e    : R
      _+_  : R → R → R
      _∙_  : R → R → R
      -_   : R → R
    field
      +-assoc      : ∀ {x y z} → (x + y) + z ≡ x + (y + z)
      ∙-assoc      : ∀ {x y z} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
      +-comm       : ∀ {x y}   → x + y ≡ y + x
      ∙-comm       : ∀ {x y}   → x ∙ y ≡ y ∙ x
      e-id         : ∀ {x}     → x ∙ e ≡ x
      z-id         : ∀ {x}     → x + z ≡ x
      ∙-distrib-+ᵣ : ∀ {x y z} → (x ∙ (y + z)) ≡ (x ∙ y) + (x ∙ z)
      ∙-distrib-+ₗ : ∀ {x y z} → ((x + y) ∙ z) ≡ (x ∙ z) + (y ∙ z)
      -inv-+       : ∀ {x}     → x + (- x) ≡ z
      ¬-z-div      : ∀ {x y : R \- z} → intro- x ∙ intro- y ≢ z


  record Subset (R : Set) : Set₁ where
    field
      Sub : Set
      inj  : Sub → R
    -- field
      -- inj-inj : ∀ {x y} → inj x ≡ inj y → x ≡ y

  _is∈_ : ∀ {R : Set} → (x : R) →  (Su : Subset R) → Set
  x is∈ Su = ∃[ x' ∈ Sub ] x ≡ inj x' 
    where
      Sub = Subset.Sub Su
      inj = Subset.inj Su

  {- Because ≡ is decidable -}

  _is∉_ : ∀ {R : Set} → (x : R) →  (Su : Subset R) → Set
  x is∉ Su = ∄[ x' ∈ Sub ] (x ≡ inj x')
    where
      Sub = Subset.Sub Su
      inj = Subset.inj Su

  _\--_ : (R : Set) →  (S : Subset R) → Set
  R \-- Su = [ x ∈ R ∣ x is∉ Su ]

  

  record Ideal (R : Set) (CR : CRing R) : Set₁ where
    open CRing CR
    field
      I : Set
      inj : I → R
    field
      inj-inj : ∀ {x y} → inj x ≡ inj y → x ≡ y
      +-closed : ∀ {x y} → ∃[ w ∈ I ] inj w ≡ inj x + inj y 
      ∙-closed : ∀ {r x} → ∃[ w ∈ I ] inj w ≡ inj x ∙ r     
      -closed  : ∀ {x}   → ∃[ w ∈ I ] inj w ≡ - inj x 

  record IdealContain (R : Set) (CR : CRing R) (Su : Subset R) : Set₁ where
    open CRing CR
    open Subset Su renaming (inj to inj-Sub-R)
    field
      I : Set
      inj : I → R
      inj-Sub-I : Sub → I
    field
      inj-comm : inj-Sub-I ∘ inj ≡ inj-Sub-R
      -- inj-Sub-I-inj :  ∀ {x y} → inj-Sub-I x ≡ inj-Sub-I y → x ≡ y {- can be proved -}
      inj-inj  : ∀ {x y} → inj x ≡ inj y → x ≡ y
      +-closed : ∀ {x y} → ∃[ w ∈ I ] inj w ≡ inj x + inj y 
      ∙-closed : ∀ {r x} → ∃[ w ∈ I ] inj w ≡ inj x ∙ r     
      -closed  : ∀ {x}   → ∃[ w ∈ I ] inj w ≡ - inj x 

  QaQ : ∀ {R : Set} {x z : R} → [ x ∈ R ∣ ∃[ z ∈ R ] z ≡ x ] → R
  QaQ (fst , fst₁ , snd) = fst


  ∏ₐ  : {R : Set} → (n : Nat) → (Fin n → R) → (r : R) → (_∙_ : R → R → R) → R
  ∏ₐ Z p r _∙_ = r
  ∏ₐ (S n) p r _∙_ = p-zero ∙ (∏ₐ n (fin-inj ∘ p) r _∙_)
     where
       p-zero = p Zf

  
  record UFD (R : Set) : Set where
    field
      z    : R
      e    : R
      _+_  : R → R → R
      _∙_  : R → R → R
      -_   : R → R
      --   R^× := [ x ∈ R ∣ ∃[ z ∈ R ] z ∙ x ≡ e  ]
      --   Irreduci := [ x ∈ R | ∀ {y z : (R \-- R^x) \- z } → y ∙ z ≢ x   ]
   
    field
      +-assoc      : ∀ {x y z} → (x + y) + z ≡ x + (y + z)
      ∙-assoc      : ∀ {x y z} → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)
      +-comm       : ∀ {x y}   → x + y ≡ y + x
      ∙-comm       : ∀ {x y}   → x ∙ y ≡ y ∙ x
      e-id         : ∀ {x}     → x ∙ e ≡ x
      z-id         : ∀ {x}     → x + z ≡ x
      ∙-distrib-+ᵣ : ∀ {x y z} → (x ∙ (y + z)) ≡ (x ∙ y) + (x ∙ z)
      ∙-distrib-+ₗ : ∀ {x y z} → ((x + y) ∙ z) ≡ (x ∙ z) + (y ∙ z)
      -inv-+       : ∀ {x}     → x + (- x) ≡ z
      ¬-z-div      : ∀ {x y : R \- z} → intro- x ∙ intro- y ≢ z
    field
      z≢e          : z ≢ e
      
    -invol : ∀ {x} →  x ≡ - (- x)
    -invol {x} =  (sym z-id) ⋆ (cong (λ qwq → x + qwq) (sym (-inv-+ {(- x)})) ) ⋆ (sym +-assoc) ⋆ (cong (λ qwq → qwq + (- (- x))) (-inv-+) ) ⋆ +-comm ⋆ z-id
    -- -invol = sym - - x  ≡  z + - - x ≡ (x + - x) + - - x ≡ x + ((- x) + (- - x))  ≡ x + z ≡ x
    -inj₁   : ∀ {x y} → - x ≡ - y → - (- x) ≡ y
    -inj₁ {x} {y} -x≡-y  =  (cong -_ -x≡-y) ⋆ (sym -invol)
    
    -inj₂   : ∀ {x y} → - (- x) ≡ y → x ≡ y
    -inj₂  qwq  = sym ((sym qwq) ⋆ (sym -invol))
    
    -inj    : ∀ {x y} → - x ≡ - y → x ≡ y
    -inj {x} {y}   = -inj₁ {x} {y} ∘ -inj₂ {x} {y}

    +-inj   : ∀ {x} → x + x ≡ x → x ≡ z
    +-inj {x} x+x≡x = sym (   sym ((cong (λ y → y + (- x)) x+x≡x) ⋆ -inv-+) ⋆ +-assoc ⋆ (cong (λ y → x + y) -inv-+) ⋆ z-id ) 
    -- z ≡ x + (x + (- x)) ≡ x + z

    z-el₁ : ∀ {x} → (x ∙ z) + (x ∙ z) ≡ x ∙ z
    z-el₁ {x} = (sym ∙-distrib-+ᵣ) ⋆ (cong (λ y → x ∙ y) (z-id {z}))
    
    z-el : ∀ {x} →  x ∙ z ≡ z
    z-el {x} = +-inj {x ∙ z} ( z-el₁ )
    -- x ∙ z ≡ x ∙ (e + (- e)) ≡ x ∙ e + x ∙ (- e) ≡ x + - x ≡ z

    
    R^×-set = [ x ∈ R ∣ ∃[ y ∈ R ] y ∙ x ≡ e  ]
    R^×-inj : [ x ∈ R ∣ ∃[ y ∈ R ] y ∙ x ≡ e  ] → R
    R^×-inj = λ (a , b , c) →  a
    R^×     = record {Sub = R^×-set ; inj = R^×-inj }
    zis∉R^× : ∄[ x' ∈ R^×-set ] (z ≡ R^×-inj x')
    zis∉R^× = λ ((y , (w , w∙y≡e )) , z≡y) → ( z≢e ((sym z-el) ⋆ (cong (λ t →  w ∙ t) z≡y) ⋆ w∙y≡e) ) 
    qz      : R \-- R^×
    qz      = z , zis∉R^×

    Irreduci = [ x ∈ R ∣ (∀ {((y , y∉R^×) , b)  ((z , z∉R^×) , d) : (R \-- R^×) \- qz } → y ∙ z ≢ x)   ]
    inj-Irreduci : Irreduci → R
    inj-Irreduci  = λ (a , b) → a

    ∏  : (n : Nat) → (Fin n → R) → R
    ∏ n p = ∏ₐ n p e _∙_

    ∏ₚ : ∀ {n : Nat} → (Fin n → Irreduci) → R
    ∏ₚ {n} p = ∏ n (p ∘ inj-Irreduci)

    field
      factor       : (((x , x∉R^×) , c) : ( R \-- R^× ) \- qz )  → ∃[ n ∈ Nat ] ( ∃[ p ∈ (Fin n → Irreduci) ] (∃[ (r , prf) ∈ R^×-set ] x ≡ r ∙ (∏ₚ p) ))



  Field-is-UFD : ∀ {R : Set} → (FR : Field R) → UFD R
  UFD.z            (Field-is-UFD FR) = Field.z FR
  UFD.e            (Field-is-UFD FR) = Field.e FR
  UFD._+_          (Field-is-UFD FR) = Field._+_ FR
  UFD._∙_          (Field-is-UFD FR) = Field._∙_ FR
  UFD.-            (Field-is-UFD FR) = Field.- FR
  UFD.+-assoc      (Field-is-UFD FR) = Field.+-assoc FR
  UFD.∙-assoc      (Field-is-UFD FR) = Field.∙-assoc FR
  UFD.+-comm       (Field-is-UFD FR) = Field.+-comm FR
  UFD.∙-comm       (Field-is-UFD FR) = Field.∙-comm FR
  UFD.e-id         (Field-is-UFD FR) = Field.e-id FR
  UFD.z-id         (Field-is-UFD FR) = Field.z-id FR
  UFD.∙-distrib-+ᵣ (Field-is-UFD FR) = Field.∙-distrib-+ᵣ FR
  UFD.∙-distrib-+ₗ (Field-is-UFD FR) = Field.∙-distrib-+ₗ FR
  UFD.-inv-+       (Field-is-UFD FR) = Field.-inv-+ FR
  UFD.¬-z-div      (Field-is-UFD FR) {x} {y} x∙y≡z = z≢e (sym ( sym inv-inv-∙ ⋆ (cong (λ q → intro- (inv y) ∙ q) ((sym (∙-comm ⋆ e-id))  ⋆ (cong (λ q → q ∙ (intro- y)) (sym inv-inv-∙)) ⋆ ∙-assoc ⋆ (cong (λ q → intro- (inv x) ∙ q) x∙y≡z) ⋆ z-el)) ⋆ z-el  ))
    where
      open Field FR
      {-
      _∙_ = Field._∙_ FR
      _+_ = Field._+_ FR
      z   = Field.z FR
      e   = Field.e FR
      -_  = Field.- FR
      inv = Field.inv FR
      -inv-+ = Field.-inv-+ FR
      inv-inv-∙ = Field.inv-inv-∙ FR
      z≢e = Field.z≢e FR
      +-assoc = Field.+-assoc FR
      ∙-assoc = Field.∙-assoc FR
      ∙-distrib-+ᵣ = Field.∙-distrib-+ᵣ FR
      z-id  = Field.z-id FR
      e-id  = Field.e-id FR
      ∙-comm = Field.∙-comm FR
      -}

      +-inj   : ∀ {x} → x + x ≡ x → x ≡ z
      +-inj {x} x+x≡x = sym (   sym ((cong (λ y → y + (- x)) x+x≡x) ⋆ -inv-+) ⋆ +-assoc ⋆ (cong (λ y → x + y) -inv-+) ⋆ z-id ) 
      -- z ≡ x + (x + (- x)) ≡ x + z

      z-el₁ : ∀ {x} → (x ∙ z) + (x ∙ z) ≡ x ∙ z
      z-el₁ {x} = (sym ∙-distrib-+ᵣ) ⋆ (cong (λ y → x ∙ y) (z-id {z}))
    
      z-el : ∀ {x} →  x ∙ z ≡ z
      z-el {x} = +-inj {x ∙ z} ( z-el₁ )
  UFD.z≢e          (Field-is-UFD FR) = Field.z≢e FR
  UFD.factor      (Field-is-UFD {R} FR) ((x , x∉) , d) = ?
    where
      open Field FR
      R^×-set = [ x ∈ R ∣ ∃[ y ∈ R ] y ∙ x ≡ e  ]
      R^×-inj : [ x ∈ R ∣ ∃[ y ∈ R ] y ∙ x ≡ e  ] → R
      R^×-inj = λ (a , b , c) →  a

      R^×→R-z : R^×-set → R \- z
      R^×→R-z = ?
    
      +-inj   : ∀ {x} → x + x ≡ x → x ≡ z
      +-inj {x} x+x≡x = sym (   sym ((cong (λ y → y + (- x)) x+x≡x) ⋆ -inv-+) ⋆ +-assoc ⋆ (cong (λ y → x + y) -inv-+) ⋆ z-id ) 
      -- z ≡ x + (x + (- x)) ≡ x + z

      z-el₁ : ∀ {x} → (x ∙ z) + (x ∙ z) ≡ x ∙ z
      z-el₁ {x} = (sym ∙-distrib-+ᵣ) ⋆ (cong (λ y → x ∙ y) (z-id {z}))
    
      z-el : ∀ {x} →  x ∙ z ≡ z
      z-el {x} = +-inj {x ∙ z} ( z-el₁ )
      
     

    
  


  
     


