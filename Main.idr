module Main

data Nat = Zero | Succ n

data Nat' : Type where
  Zero' : Nat'
  Succ' : (n : Nat') -> Nat'

data List' a = Nil | (::) a (List' a)

append' : forall a. (1 xs : List a) -> (1 ys : List a) -> List a
append' = ?rhs