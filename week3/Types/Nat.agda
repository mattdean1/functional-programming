module Types.Nat where

open import Types.Equality

data Nat : Set where
  zero : Nat
  succ  : Nat → Nat

_+_ : Nat → Nat → Nat
zero     + n = n
(succ m) + n = succ (m + n)
infixl 5 _+_

_*_ : Nat → Nat → Nat
zero     * n = zero
(succ m) * n = (m * n) + n
