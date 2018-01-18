module Symbols where

{- Natural numbers -}
data Nat : Set where
  zero : Nat
  succ  : Nat → Nat

_+_ : Nat → Nat → Nat
zero     + n = n
(succ m) + n = succ (m + n)
infixl 5 _+_


{- Booleans -}
data Bool : Set where
  true  : Bool
  false : Bool

data istrue : Bool → Set where
  ok : istrue true


{- Lists -}
data List (A : Set) : Set where
  nil   : List A
  _::_  : (x : A) → List A → List A
infixr 4 _::_

append : ∀ {A} → List A → List A → List A
append nil       l   = l
append (x :: xs) l   = x :: (append xs l)

length : ∀ {A} → List A → Nat
length nil = zero
length (x :: xs) = succ (length xs)
