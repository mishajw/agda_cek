module Cek where

open import Util

-- Variables to use in lambda calculus
data Variable : Set where
  X : Variable
  Y : Variable
  Z : Variable

-- Hacky equality check for variables
-- TODO: Remove this function
eq : Variable → Variable → Bool
eq X X = true
eq Y Y = true
eq Z Z = true
eq _ _ = false

-- Definition of lambda: function creation, application, or a variable
data Lambda : Set where
  λ'_·_ : Variable → Lambda → Lambda
  [_][_] : Lambda → Lambda → Lambda
  [_] : Variable → Lambda

mutual
  -- Variable to closure mapping for the environment
  data Environment : Set where
    ⊘ : Environment
    [_⇒_]∷_ : Variable → Closure → Environment → Environment
  -- Closed lambda with mappings
  data Closure : Set where
    clos[λ'_·_,_] : Variable → Lambda → Environment → Closure
  -- Value for the machine, either a variable, or a closure
  data Value : Set where
    vV : Variable → Value
    vC : Closure → Value

-- Look for a value inside an environment
lookup_inside_ : Variable → Environment → Optional Value
lookup x inside ⊘ = none
lookup x inside ([ x' ⇒ m ]∷ e) with eq x x'
... | true = some (vC m)
... | false = lookup x inside e

-- Frame for the continuation
data Frame : Set where
  [_∘] : Value → Frame
  [∘_~_] : Lambda → Environment → Frame

-- Stack of continuation for the machine
data Kontinuation : Set where
  ■ : Kontinuation
  _∷_ : Frame → Kontinuation → Kontinuation
infix 5 _∷_

-- Possible values for control in the machine
data Control : Set where
  cλ : Lambda → Control
  cV : Value → Control

-- State of the machine
data CekState : Set where
  <_~_~_> : Control → Environment → Kontinuation → CekState

-- Perform a single step in tha machine
cek-step : CekState → Optional CekState
cek-step < cλ [ x ] ~ e ~ k > = map make-state (lookup x inside e) where
  make-state : Value → CekState
  make-state v = < cV v ~ e ~ k >
cek-step < cλ [ w₁ ][ w₂ ] ~ e ~ k > =
  some < cλ w₁ ~ e ~ [∘ w₂ ~ e ] ∷ k >
cek-step < cλ (λ' x · w) ~ e ~ k > =
  some < closed-control ~ e ~ k > where
    closed-control = cV (vC ( clos[λ' x · w , e ] ) )
cek-step < cV m ~ e₁ ~ [∘ w ~ e₂ ] ∷ k > =
  some < cλ w ~ e₂ ~ [ m ∘] ∷ k >
cek-step < cV (vC w₁) ~ e ~ [ vC (clos[λ' v · w₂ , e₂ ]) ∘] ∷ k > =
  some < cλ w₂ ~ [ v ⇒ w₁ ]∷ e₂ ~ k >
cek-step _ = none

-- Run the machine until termination
-- TODO: Termination checking fails for this function
cek-run : Lambda → Optional Value
cek-run l = cek-run' < cλ l ~ ⊘ ~ ■ > where
  cek-run' : CekState → Optional Value
  cek-run' < cV v ~ _ ~ ■ > = some v
  cek-run' s@(< c ~ e ~ k >) with cek-step s
  ... | some new-state = cek-run' new-state
  ... | none = none

-- Some lambda examples:
lambda₀ = λ' X · [ X ]
lambda₁ = [ X ]
lambda₂ = [ [ λ' X · λ' Y · [ X ] ][ λ' X · [ X ] ] ][ λ' Z · [ Z ] ]

