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

+-cong2 : {a b x y : Nat} → a ≡ b → x ≡ y → a + x ≡ b + y
+-cong2 (refl a) (refl x) = refl (a + x)

+-succ-dist : (a b : Nat) → succ (a + b) ≡ a + succ b
+-succ-dist zero b = refl (succ b)
+-succ-dist (succ a) b = ≡-cong succ (+-succ-dist a b)

+-succ-swap : (a b : Nat) → (succ a) + b ≡ a + succ b
+-succ-swap a b = +-succ-dist a b

+-succ2 : (a : Nat) → a + succ zero ≡ succ a
+-succ2 zero = refl (succ zero)
+-succ2 (succ a) = ≡-cong succ (+-succ2 a)





_*_ : Nat → Nat → Nat
zero     * n = zero
(succ m) * n = (m * n) + n

*-zero : (n : Nat) → n * zero ≡ zero
*-zero zero = refl zero
*-zero (succ n) = +-unit2p (*-zero n)
