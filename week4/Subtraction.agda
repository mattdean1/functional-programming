module Subtraction where

open import Types.Nat
open import Types.Equality

_-_ : Nat → Nat → Nat
zero - zero = zero
zero - succ n = zero
succ m - zero = succ m
succ m - succ n = m - n

subtract-equal : {a b : Nat} → a ≡ b → a - b ≡ zero
subtract-equal (refl zero) = refl zero
subtract-equal (refl (succ a)) = subtract-equal (refl a)
