module Types.Nat where

open import Types.Equality

data Nat : Set where
  zero : Nat
  succ  : Nat → Nat

_+_ : Nat → Nat → Nat
zero     + n = n
(succ m) + n = succ (m + n)
infixl 5 _+_

+-unit2 : (x : Nat) → x + zero ≡ x
+-unit2 zero = refl zero
+-unit2 (succ x) = ≡-cong succ (+-unit2 x)

+-unit2p : {a b : Nat} → a ≡ b → a + zero ≡ b
+-unit2p {.x} {.x} (refl x) = +-unit2 x

-- adding n to both sides preserves equality
+-cong : {a b : Nat} → a ≡ b → (n : Nat) → a + n ≡ b + n
+-cong p n = ≡-cong (λ x → x + n) p

+-succ1 : (a b : Nat) → a + succ b ≡ succ (a + b)
+-succ1 zero b = refl (succ b)
+-succ1 (succ a) b = ≡-cong succ (+-succ1 a b)

+-succ2 : (a : Nat) → a + succ zero ≡ succ a
+-succ2 a = ≡-trans (+-succ1 a zero) (≡-cong succ (+-unit2 a))
