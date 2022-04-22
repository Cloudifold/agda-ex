{-# OPTIONS --without-K #-}

import Relation.Binary.PropositionalEquality
  as Eq
open Eq
  using (_≡_; refl; sym; cong; trans)
open Eq.≡-Reasoning
  using (begin_; _≡⟨⟩_; step-≡; _∎)

id : {A : Set} → A → A
id x = x

infixl 20 _∙_ 
_∙_ : {A B C : Set} → (A → B) → (B → C) → (A → C)
(f ∙ g) x = g (f x)

postulate
  ex : ∀ {A B : Set} {f g : A → B} → ( ∀ {x : A} → f x ≡ g x ) → f ≡ g



{-
 Monad-Join : Monoid object in Functor(C,C)
 Monad-Binding : Extension system
 -}


record Monad-Join (T : Set → Set) : Set₁ where
  field
    map : ∀ {A B} → (A → B) → T A → T B
    -- ↑ monad functor action on morphsims
    unit : ∀ {A} → A → T A
    mult : ∀ {A} → T (T A) → T A
    -- ↑ structural natural transformations for monad
    map-id : ∀ {A} {x : T A} → map (id {A}) x ≡ id {T A} x
    map-∙ : ∀ {A B C} {f : A → B} {g : B → C} {x : T A} → map (f ∙ g) x ≡ ((map f) ∙ (map g)) x
    -- ↑ functor axioms
    unit-natural : ∀ {A B} {f : A → B} {x : A}           → (unit {A} ∙ map f) x           ≡ (f ∙ unit {B}) x
    mult-natural : ∀ {A B} {f : A → B} {x : T (T A)}     → (mult {A} ∙ map f) x           ≡ (map (map f) ∙ mult {B}) x
    left-id : ∀ {A} {x : T A}                             → (unit {T A} ∙ mult {A}) x      ≡ x
    right-id : ∀ {A} {x : T A}                            → (map (unit {A}) ∙ mult {A}) x  ≡ x
    assoc : ∀ {A} {x : T (T (T A))}                       → (mult {T A} ∙ mult {A}) x      ≡ (map (mult {A}) ∙ mult {A}) x
    {-
      unit-natural
      
         A  ----- f ----> B
         |                |
       unit             unit
         |                |
         V                V
        T A -- map f --> T B

      mult-natural
        
        T (T A) -- map (map f) --> T (T B)
          |                          |
        mult                       mult
          |                          |
          V                          V
        T A  ------ map f ------>  T B

      left-id

          T A ---- id ----> T A
           |                 | 
       unit (T A)           id
           |                 |
           V                 V
        T (T A) -- mult --> T A

      right-id

          T A ---- id ----> T A
           |                 | 
       map unit A           id
           |                 |
           V                 V
        T (T A) -- mult --> T A

      assoc

        T (T (T A)) -- mult (T A) --> T (T A)
            |                            |
        map mult A                     mult
            |                            |
            V                            V
         T (T A)  ------- mult ------>  T A
     -}


record Monad-Binding (T : Set → Set) : Set₁ where
  infixl 6 _>>=_
  field
    pure : ∀ {A} → A → T A
    _>>=_ : ∀ {A B} → T A → (A → T B) → T B
    >>=-right-id : ∀ {A} {x : T A} → x >>= pure ≡ x
    >>=-left-id : ∀ {A B} {f : A → T B} {x : A} → (pure {A} ∙ (_>>= f)) x ≡ f x
    K-comp-assoc : ∀ {A B C} {f : A → T B} {g : B → T C} {x : T A} → x >>= f ∙ (_>>= g) ≡ (x >>= f) >>= g
    -- ↑ Kleisli composition associativity                                                    x >>= f >>= g  (by left associativity)
    {-
      >>= : T A → (A → T B) → T B
      binding extension
      
      >>=-right-id

         A -- pure --> T A              A -- pure --> T A
                        ^                              ^
                        |                              |
              ⇓ >>=     |         =                    |
                        |                              |
        T A ---- _>>= (pure A)         T A ------- identity

               (    _>>= (pure A) = id     )

      >>=-left-id

         A -- pure --> T A --- _>>= f ---> T B
 
                         =

                  A --- f ---> T B

      K-comp-assoc
        
         A -- f --> T B --- _>>= g ---> T C           A ---- f ---> T B -- _>>= g --> T C
                                         ^                           ^
                                         |                           |
                     ⇓ >>=               |     =          ⇓ >>=      |
                                         |                           |
        T A -- _>>= (f ∙ (_>>= g)) ------+           T A -- _>>= f --+ 
     -}


module _ {T₁ : Set → Set} (T : Monad-Join T₁) where
  open Monad-Binding {{ ... }}
  open Monad-Join T
  instance 
    Join⇒Binding : Monad-Binding T₁
    Join⇒Binding .pure         = unit
    Join⇒Binding ._>>=_ x f    = mult (map f x)
    Join⇒Binding .>>=-right-id = right-id
    Join⇒Binding .>>=-left-id  = trans (cong mult (unit-natural)) (left-id)
    Join⇒Binding .K-comp-assoc {f = f} {g = g} {x = x} = begin
      x >>= f ∙ (_>>= g)                        ≡⟨ cong mult
                                                        (map-∙ {f = f} {g = (_>>= g)} {x = x})  ⟩
      mult ( map (map g ∙ mult) (map f x) )     ≡⟨ cong mult
                                                        (map-∙ {f = (map g)} {g = mult} {x = (map f x)}) ⟩ -- step 1
      {- mult (( map f ∙  map ((map g) ∙ mult)) x) -}
      (map mult ∙ mult) (map (map g) (map f x)) ≡⟨ sym ( assoc {x = (map (map g) (map f x))} ) ⟩ -- step 2
      {- (map (map g) ∙ map mult ∙ mult) (map f x) -}
      mult ( (map (map g) ∙ mult) (map f x) )     ≡⟨ cong mult (sym ( mult-natural {f = g} {x = (map f x)} )) ⟩ -- step 3
      {- (map (map g) ∙ mult ∙ mult) (map f x) -}
      {-

        after step 1 :
          goal : path2 ≡ path1
         
        (map f x) :  T (T B) -- map (map g) -->  T (T (T C)) -- mult (T C) --> T (T C)
                        |                            |                            |
                     mult B                     map (mult C)                   mult C
                        |                            |                            |
                        V                            V                            V
                       T C  ------ map g ------>  T (T C)  ------ mult C ----->  T C

            route name : left   :=  path1
                         middle :=  path2
                         right  :=  path3
            
            step 2     : path2  ==  path3
            step 3     : path3  ==  path1
       -}
      (x >>= f) >>= g ∎


module _ {T₁ : Set → Set} (T : Monad-Binding T₁) where
  open Monad-Join {{ ... }}
  open Monad-Binding T
  instance 
    Binding⇒Join : Monad-Join T₁
    Binding⇒Join .map f = _>>= f ∙ pure 
    Binding⇒Join .unit = pure
    Binding⇒Join .mult = _>>= id
    
    Binding⇒Join .map-id = >>=-right-id
    Binding⇒Join .map-∙ {f = f} {g = g} {x = x} = begin
      x >>= f ∙ g ∙ p            ≡⟨ sym (cong (λ y → (x >>= f ∙ y))
                                              (ex {f = pure ∙ (_>>= g ∙ p)}
                                                  >>=-left-id)) ⟩ -- >>=-left-id {f = g ∙ p} {x = x}
      x >>= f ∙ p ∙ (_>>= g ∙ p) ≡⟨ K-comp-assoc ⟩
      x >>= f ∙ p >>= g ∙ p ∎
      where
        p = pure
        
    Binding⇒Join .unit-natural = >>=-left-id
    Binding⇒Join .mult-natural {f = f} {x = x} = begin
      x >>= id >>= f ∙ p                 ≡⟨ sym K-comp-assoc ⟩ -- K-comp-assoc {f = id} {g = f ∙ p} {x = x}
      x >>= (_>>= f ∙ p)                 ≡⟨ sym (cong (λ y → x >>= (_>>= f ∙ p) ∙ y)
                                                      (ex {f = p ∙ (_>>= id)}
                                                          >>=-left-id)) ⟩
      x >>= (_>>= f ∙ p) ∙ p ∙ (_>>= id) ≡⟨ K-comp-assoc ⟩ -- K-comp-assoc {f = (_>>= f ∙ p) ∙ p} {g = id} {x = x}
      x >>= (_>>= f ∙ p) ∙ p >>= id ∎
      where
        p = pure
        
    Binding⇒Join .left-id = >>=-left-id {f = id}
    
    Binding⇒Join .right-id {x = x} = begin
      x >>= p ∙ p >>= id      ≡⟨ sym K-comp-assoc ⟩ -- K-comp-assoc {f = p ∙ p} {g = id} {x = x}
      x >>= p ∙ p ∙ (_>>= id) ≡⟨ cong (λ y → x >>= p ∙ y)
                                      (ex {f = p ∙ (_>>= id)}
                                          >>=-left-id) ⟩ -- >>=-left-id {f = id} {x = x}
      x >>= p ≡⟨ >>=-right-id ⟩
      x ∎
      where
        p = pure
        
    Binding⇒Join .assoc {x = x} = begin
      x >>= id >>= id                 ≡⟨ sym K-comp-assoc ⟩ -- K-comp-assoc {f = id} {g = id} {x = x}
      x >>= (_>>= id)                 ≡⟨ sym (cong (λ y → x >>= (_>>= id) ∙ y)
                                                   (ex {f = p ∙ (_>>= id)}
                                                       >>=-left-id)) ⟩ -- >>=-left-id {f = id} {x = x}
      x >>= (_>>= id) ∙ p ∙ (_>>= id) ≡⟨ K-comp-assoc ⟩ -- K-comp-assoc {f = (_>>= ∙ id) ∙ p} {g = id} {x = x}
      x >>= (_>>= id) ∙ p >>= id ∎
      where
        p = pure
