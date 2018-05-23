module Util where

data Optional (A : Set) : Set where
  none : Optional A
  some : A → Optional A
map : {A B : Set} → (A → B) → Optional A → Optional B
map f none = none
map f (some x) = some (f x)

data Bool : Set where
  true : Bool
  false : Bool

