module Exercises where

open import Types.Equality
open import Types.Nat
open import Types.Int

{-
Show that (Nat, +, 0) is a commutative monoid.
Define the type of integers Int.
Define addition and subtraction for integers.
Show that (Int, +, 0, -) forms an abelian group.
Define multiplication for Nat.
Show that (Nat, +, 0, x, 1) forms a semi-ring
-}

-- Show that (Nat, +, 0) is a commutative monoid.
+-unit1 : (x : Nat) → zero + x ≡ x
+-unit1 x = refl x

+-unit2 : (x : Nat) → x + zero ≡ x
+-unit2 zero = refl zero
+-unit2 (succ x) = ≡-cong succ (+-unit2 x)

+-assoc : (x y z : Nat) → (x + y) + z ≡ x + (y + z)
+-assoc zero y z = refl (y + z)
+-assoc (succ x) y z = ≡-cong succ (+-assoc x y z)

+-comm : (x y : Nat) → x + y ≡ y + x
+-comm zero     y = ≡-sym (+-unit2 y)
+-comm (succ x) y = p1 x y (≡-cong succ (+-comm x y))
  where
  p0 : (a b : Nat) → succ (a + b) ≡ a + succ b
  p0 zero     b = refl (succ b)
  p0 (succ a) b = ≡-cong succ (p0 a b)

  p1 : (a b : Nat) → succ (a + b) ≡ succ (b + a) → succ (a + b) ≡ b + succ a
  p1 a b p = ≡-trans p (p0 b a)

-- Show that (Int, +, 0, -) forms an abelian group.
