{-# OPTIONS --allow-unsolved-metas #-}

module Exercises1 where

open import Types.Equality
open import Types.Nat
open import Types.Int


-- Show that (Nat, +, 0) is a commutative monoid.
+-unit1 : (x : Nat) → zero + x ≡ x
+-unit1 x = refl x

+-unit2' : (x : Nat) → x + zero ≡ x
+-unit2' zero = refl zero
+-unit2' (succ x) = ≡-cong succ (+-unit2 x)

+-assoc : (x y z : Nat) → (x + y) + z ≡ x + (y + z)
+-assoc zero y z = refl (y + z)
+-assoc (succ x) y z = ≡-cong succ (+-assoc x y z)

+-comm : (x y : Nat) → x + y ≡ y + x
+-comm zero     y = ≡-sym (+-unit2 y)
+-comm (succ x) y = p1 x y (≡-cong succ (+-comm x y))
  where
  p1 : (a b : Nat) → succ (a + b) ≡ succ (b + a) → succ (a + b) ≡ b + succ a
  p1 a b p = ≡-trans p (+-succ-dist b a)


{-
  Show that (Nat, +, 0, *, 1) forms a semi-ring

  ring: abelian group with a second binary op that is associative, distributive, and has an identity
    (abelian group operator is the additive operator, second op is the multiplicative)
  semi ring: ring without an additive inverse
-}

{- (+-assoc, +-closure, +-identity) (*-assoc, *-dist, *-identity)
    +-closure from the type signature of +
    +-assoc above
    +-identity above (+-unit1, +-unit2)
-}

-- identity
*-unitl : (n : Nat) → succ zero * n ≡ n
*-unitl n = refl n

*-unitr : (n : Nat) → n * succ zero ≡ n
*-unitr zero = refl zero
*-unitr (succ n) = lemma (*-unitr n)
  where
  lemma : {a b : Nat} → a ≡ b → a + succ zero ≡ succ b
  lemma (refl a) = +-succ2 a

-- distributivity
*-succ-dist1 : (a b : Nat) → (succ a) * b ≡ (a * b) + b
*-succ-dist1 a b = refl ((a * b) + b)

*-succ-dist2 : (a b : Nat) → a * succ b ≡ (a * b) + a
*-succ-dist2 zero b = refl zero
*-succ-dist2 (succ a) b = p0 (a * succ b) (a * b) a b (*-succ-dist2 a b)
  where
  p0 : (x y z n : Nat) → x ≡ y + z → x + succ n ≡ y + n + succ z
  p0 x y z n p = ≡-trans (≡-trans (≡-sym (+-succ-dist x n)) (≡-cong succ (≡-cong (λ q → q + n) p))) (p0' y z n)
    where
    p0' : (a b c : Nat) → succ (a + b + c) ≡ a + c + succ b
    p0' a b c = ≡-trans (≡-cong succ (p0'' a b c)) (p0''' a c b)
      where
      p0'' : (a b c : Nat) → a + b + c ≡ a + c + b
      p0'' zero b c = +-comm b c
      p0'' (succ a) b c = ≡-cong succ (p0'' a b c)

      p0''' : (a b c : Nat) → succ (a + b + c) ≡ a + b + succ c
      p0''' zero b c = +-succ-dist b c
      p0''' (succ a) b c = ≡-cong succ (p0''' a b c)

*-succ-dist3 : (a b : Nat) → (succ a) * (succ b) ≡ (a * b) + a + b
*-succ-dist3 a b = {!   !}

*-distl : (a b c : Nat) → a * (b + c) ≡ (a * b) + (a * c)
*-distl zero b c = refl zero
*-distl (succ a) b c = ?
-- *-distl (succ a) zero c = lem a (zero + ((a * c) + c))
--   where
--   lem : (x y : Nat) → y ≡ (x * zero) + zero + y
--   lem x y = ≡-sym (≡-cong (λ q → q + zero + y) (*-zero x))
--
-- *-distl (succ a) (succ b) c = {!   !}

*-distr : (a b c : Nat) → (b + c) * a ≡ (b * a) + (c * a)
*-distr a b c = {!   !}

*-assoc : (a b c : Nat) → (a * b) * c ≡ a * (b * c)
*-assoc zero b c = refl zero
*-assoc (succ a) b zero = p1 b (≡-trans (*-zero ((a * b) + b)) (p0 a b))
  where
  p0 : (a b : Nat) → zero ≡ a * (b * zero)
  p0 a b = ≡-trans (≡-sym (*-zero a)) (≡-cong (λ x → a * x) (≡-sym (*-zero b)))

  p1 : {a b : Nat} → (x : Nat) → a ≡ b → a ≡ b + (x * zero)
  p1 {a} {b} x p = p1' a b zero (x * zero) (≡-sym (+-unit2p (≡-sym p))) (≡-sym (*-zero x))
    where
    p1' : (a b x y : Nat) → a ≡ b + x → x ≡ y → a ≡ b + y
    p1' a b .x y p (refl x) = p

*-assoc (succ a) b (succ c) = {!   !}
