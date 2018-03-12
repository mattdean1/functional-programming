module Types.Order where

open import Types.Nat
open import Types.Bool

_<=_ : Nat → Nat → Bool
zero     <= _        = true
_        <= zero     = false
(succ a) <= (succ b) = a <= b

data _<=p_ : Nat → Nat → Set where
  zero<=p : (x : Nat) → zero <=p x
  succ<=p : (x y : Nat) → x <=p y → (succ x) <=p (succ y)
