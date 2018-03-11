{-# OPTIONS --allow-unsolved-metas #-}

module Properties.Nat.Multiplication where

open import Types.Equality
open import Types.Nat
open import Types.Reasoning

open import Properties.Nat.Addition

-- one is the identity element
*-unitl : (n : Nat) → succ zero * n ≡ n
*-unitl n = refl n

*-unitr : (n : Nat) → n * succ zero ≡ n
*-unitr zero = refl zero
*-unitr (succ n) = lemma (*-unitr n)
  where
  lemma : {a b : Nat} → a ≡ b → a + succ zero ≡ succ b
  lemma (refl a) = +-add-one a


-- zero annihilates Nat
*-zerol : (a : Nat) → a * zero ≡ zero
*-zerol zero = refl zero
*-zerol (succ a) = +-unitrp (*-zerol a)

*-zeror : (a : Nat) → zero * a ≡ zero
*-zeror a = refl zero


-- multiplication is associative
*-assoc : (a b c : Nat) → (a * b) * c ≡ a * (b * c)
*-assoc zero b c = refl zero
*-assoc (succ a) b zero = p1 b (≡-trans (*-zerol ((a * b) + b)) (p0 a b))
  where
  p0 : (a b : Nat) → zero ≡ a * (b * zero)
  p0 a b = ≡-trans (≡-sym (*-zerol a)) (≡-cong (λ x → a * x) (≡-sym (*-zerol b)))

  p1 : {a b : Nat} → (x : Nat) → a ≡ b → a ≡ b + (x * zero)
  p1 {a} {b} x p = p1' a b zero (x * zero) (≡-sym (+-unitrp (≡-sym p))) (≡-sym (*-zerol x))
    where
    p1' : (a b x y : Nat) → a ≡ b + x → x ≡ y → a ≡ b + y
    p1' a b .x y p (refl x) = p

*-assoc (succ a) b (succ c) = {!   !}
