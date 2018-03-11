module Exercises1 where

open import Types.Equality
open import Types.Reasoning
open import Types.Nat
open import Types.Int

open import Properties.Nat.Addition
open import Properties.Nat.Multiplication


{-
  Show that (Nat, +, 0) is a commutative monoid.

  The type signature of addition proves closure
  identity        +-unitl and +-unitr
  associativity   +-assoc
  commutativity   +-comm
-}


{-
  Show that (Nat, +, 0, *, 1) forms a semi-ring

  1. (Nat, +, 0) is a commutative monoid
      See above

  2. (Nat, *, 1) is a monoid
      Closure from the type signature of *
      identity        *-unitl and *-unitr
      associativity   *-assoc

  3. Multiplication distributes left and right over addition
      *-distl and *-distr below

  4. The first identity annihilates with the second operation
      *-zerol and *-zeror

-}

*-distl : (a b c : Nat) → a * (b + c) ≡ (a * b) + (a * c)
*-distl zero b c = refl zero
*-distl (succ a) b c
  = begin
    (a * (b + c)) + (b + c)       ≡⟨ ≡-cong (λ q → q + (b + c)) (*-distl a b c) ⟩
    (a * b) + (a * c) + (b + c)   ≡⟨ +-assoc (a * b) (a * c) (b + c) ⟩
    (a * b) + ((a * c) + (b + c)) ≡⟨ ≡-cong (λ q → (a * b) + q) (≡-sym (+-assoc (a * c) b c)) ⟩
    (a * b) + ((a * c) + b + c)   ≡⟨ +-assoc4 (a * b) (a * c) b c ⟩
    (a * b) + (a * c) + b + c     ≡⟨ +-comm4 (a * b) (a * c) b c ⟩
    (a * b) + b + (a * c) + c     ≡⟨ +-assoc ((a * b) + b) (a * c) c ⟩
    (a * b) + b + ((a * c) + c)
    ∎

*-distr : (a b c : Nat) → (a + b) * c ≡ (a * c) + (b * c)
*-distr = {!   !}



-- succ is distributive over multiplication
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
