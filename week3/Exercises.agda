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

+-assoc : (x y z : Nat) → (x + y) + z ≡ x + (y + z)
+-assoc zero y z = refl (y + z)
+-assoc (succ x) y z = ≡-cong succ (+-assoc x y z)

+-comm : (x y : Nat) → x + y ≡ y + x
+-comm zero     y = ≡-sym (+-unit2 y)
+-comm (succ x) y = p1 x y (≡-cong succ (+-comm x y))
  where
  p1 : (a b : Nat) → succ (a + b) ≡ succ (b + a) → succ (a + b) ≡ b + succ a
  p1 a b p = ≡-trans p (≡-sym (+-succ1 b a))

-- Show that (Int, +ᵢ, 0, negate) forms an abelian group.
-- (Type, Operation, Identity, Inverse)
{-
  Group axioms:
    Closure
      ∀ (a b ∈ G), (a∘b) ∈ G
    Associativity
      ∀ (a b c ∈ G), (a ∘ b) ∘ c ≡ a ∘ (b ∘ c)
    Identity
      ∃ i ∈ G, ∀ a ∈ G, a ∘ i ≡ i ∘ a ≡ a
    Inverse
      ∀ a ∈ G, ∃ a⁻¹ ∈ G, a ∘ a⁻¹ ≡ a⁻¹ ∘ a ≡ i where i is the identity element

  An Abelian group is also commutative:
    ∀ (a b ∈ G), a ∘ b ≡ b ∘ a
-}

-- Closure is satisfied by the type signature of +ᵢ
-- _+ᵢ_ : Int → Int → Int

-- Identity
-- the identity element is pos zero
z+-id1 : (a : Int) → a +ᵢ pos zero ≡ a
z+-id1 (pos x) = ≡-cong2 (λ q → pos q) (+-unit2 x)
z+-id1 (neg x) = refl (neg x)

z+-id2 : (a : Int) → (pos zero) +ᵢ a ≡ a
z+-id2 (pos x) = refl (pos x)
z+-id2 (neg x) = refl (neg x)

-- Inverse
-- the inverse of x is negate x
z+-inv1 : (a : Int) → a +ᵢ negate a ≡ pos zero
z+-inv1 (pos zero) = refl (pos zero)
z+-inv1 (pos (succ x)) = z+-inv1 (neg x)
z+-inv1 (neg zero) = refl (pos zero)
z+-inv1 (neg (succ x)) = z+-inv1 (neg x)

z+-inv2 : (a : Int) → negate a +ᵢ a ≡ pos zero
z+-inv2 (pos zero) = refl (pos zero)
z+-inv2 (pos (succ x)) = z+-inv2 (neg x)
z+-inv2 (neg zero) = refl (pos zero)
z+-inv2 (neg (succ x)) = z+-inv2 (neg x)

-- Commutativity
z+-comm : (a b : Int) → a +ᵢ b ≡ b +ᵢ a
z+-comm (pos x) (pos y) = ≡-cong2 (λ q → pos q) (+-comm x y)
z+-comm (pos x) (neg y) = refl (x - succ y)
z+-comm (neg x) (pos y) = refl (y - succ x)
z+-comm (neg x) (neg y) = ≡-cong2 (λ q → neg (q + succ zero)) (+-comm x y)

-- Associativity
z+-assoc : (a b c : Int) → (a +ᵢ b) +ᵢ c ≡ a +ᵢ (b +ᵢ c)
z+-assoc (pos x) (pos y) (pos z) = ≡-cong2 (λ q → pos q) (+-assoc x y z)
z+-assoc (pos x) (pos y) (neg z) = p0 x y (succ z)
  where
  p0' : (a b : Nat) → (a + b) - zero ≡ pos (a + b)
  p0' a b with a + b
  p0' a b | zero = refl (pos zero)
  p0' a b | succ x = refl (pos (succ x))

  p0'' : (a b : Nat) → pos (a + b) ≡ pos a +ᵢ (b - zero)
  p0'' a zero = refl (pos (a + zero))
  p0'' a (succ b) = refl (pos (a + succ b))

  p0''' : (a b : Nat) → (a + zero) - b ≡ pos a +ᵢ (zero - b)
  p0''' zero zero = refl (pos zero)
  p0''' zero (succ b) = refl (neg b)
  p0''' (succ a) zero = refl (pos (succ (a + zero)))
  p0''' (succ a) (succ b) = ≡-cong2 (λ q → q - b) (+-unit2 a)

  p0 : (x y z : Nat) → ((x + y) - z) ≡ (pos x +ᵢ (y - z))
  p0 x    y    zero = ≡-trans (p0' x y) (p0'' x y)
  p0 x    zero z    = p0''' x z
  p0 zero y    z    = ≡-sym (z+-id2 (y - z))
  p0 (succ x) (succ y) (succ z) = ≡-trans (≡-cong2 (λ q → q - z) (+-succ1 x y)) (p0 (succ x) y z)

z+-assoc (pos x) (neg y) (pos z) = p0 x (succ y) z
  where
  p0' : (a b : Nat) → (a - b) +ᵢ pos zero ≡ pos a +ᵢ (zero - b)
  p0' zero     zero     = refl (pos zero)
  p0' zero     (succ b) = refl (neg b)
  p0' (succ a) zero     = refl (pos (succ (a + zero)))
  p0' (succ a) (succ b) = z+-id1 (a - b)

  p0'' : (a b : Nat) → (a - zero) +ᵢ pos b ≡ pos a +ᵢ (b - zero)
  p0'' zero     zero     = refl (pos zero)
  p0'' zero     (succ b) = refl (pos (succ b))
  p0'' (succ a) zero     = refl (pos (succ (a + zero)))
  p0'' (succ a) (succ b) = refl (pos (succ (a + succ b)))

  p0''' : (a b : Nat) → ((zero - a) +ᵢ pos b) ≡ (pos zero +ᵢ (b - a))
  p0''' zero zero = refl (pos zero)
  p0''' zero (succ b) = refl (pos (succ b))
  p0''' (succ a) zero = refl (neg a)
  p0''' (succ a) (succ b) = ≡-sym (z+-id2 (b - a))

  p0 : (x y z : Nat) → (x - y) +ᵢ pos z ≡ pos x +ᵢ (z - y)
  p0 x y zero = p0' x y
  p0 x zero z = p0'' x z
  p0 zero x y = p0''' x y
  p0 (succ x) (succ y) z = ≡-trans (p0 x y z) (lem x y z)
    where
    lem'' : (a b : Nat) → a + succ b ≡ succ (a + b)
    lem'' zero b = refl (succ b)
    lem'' (succ a) b = ≡-cong succ (lem'' a b)

    lem' : (a b : Nat) → pos (a + succ b) ≡ (pos (succ a) +ᵢ (b - zero))
    lem' zero zero = refl (pos (succ zero))
    lem' zero (succ b) = refl (pos (succ (succ b)))
    lem' (succ a) zero = ≡-cong2 (λ q → pos (succ q)) (lem'' a zero)
    lem' (succ a) (succ b) = ≡-cong2 (λ q → pos (succ q)) (lem'' a (succ b))

    lem : (a b c : Nat) → (pos a +ᵢ (c - b)) ≡ (pos (succ a) +ᵢ (c - succ b))
    lem zero     zero     zero = refl (pos zero)
    lem (succ a) zero     zero = ≡-cong2 (λ q → pos (succ q)) (+-unit2 a)
    lem a        (succ b) zero = refl (a - succ b)
    lem a        zero     (succ c) = lem' a c
    lem a        (succ b) (succ c) = lem a b c

z+-assoc (pos x) (neg y) (neg z) = p0 x y z
  where
  p0' : (a : Nat) → (a - succ zero) ≡ (a - zero) +ᵢ neg zero
  p0' zero = refl (neg zero)
  p0' (succ a) = refl (a - zero)

  p0'' : (a b : Nat) → (a - succ (b + succ zero)) ≡ ((a - zero) +ᵢ neg (succ b))
  p0'' zero b = ≡-cong2 neg (+-succ2 b)
  p0'' (succ a) b = ≡-cong2 (λ q → a - q) (+-succ2 b)

  p0 : (x y z : Nat) → ((x - succ y) +ᵢ neg z) ≡ (x - succ (y + z + succ zero))
  p0 zero y z = refl (neg (y + z + succ zero))
  p0 (succ x) zero zero = ≡-sym (p0' x)
  p0 (succ x) zero (succ z) = ≡-sym (p0'' x z)
  p0 (succ x) (succ y) z = p0 x y z

z+-assoc (neg x) (pos y) (pos z) = p0 x y z
  where
  p0' : (a b : Nat) → (a - zero) +ᵢ pos b ≡ (a + b) - zero
  p0' zero zero = refl (pos zero)
  p0' zero (succ b) = refl (pos (succ b))
  p0' (succ a) b = refl (pos (succ (a + b)))

  p0 : (x y z : Nat) → ((y - succ x) +ᵢ pos z) ≡ ((y + z) - succ x)
  p0 x        y         zero    = ≡-trans (z+-id1 (y - succ x)) (≡-sym (≡-cong2 (λ q → q - (succ x)) (+-unit2 y)))
  p0 x        zero     (succ z) = refl (z - x)
  p0 zero     (succ y) z        = p0' y z
  p0 (succ x) (succ y) z        = p0 x y z

z+-assoc (neg x) (pos y) (neg z) = p0 x y z
  where
  p0'' : (a b c : Nat) → a + succ b + c ≡ succ (a + b + c)
  p0'' zero b c = refl (succ (b + c))
  p0'' (succ a) b c = ≡-cong succ (p0'' a b c)

  p0''' : (a b : Nat) → (neg a +ᵢ (b - zero)) ≡ (b - succ a)
  p0''' a zero = refl (neg a)
  p0''' a (succ b) = refl (b - a)

  p0' : (a b c : Nat) → neg a +ᵢ (b - succ c) ≡ neg (succ a) +ᵢ (b - c)
  p0' a zero zero = ≡-cong2 neg (≡-trans (+-succ2 (a + zero)) (≡-cong succ (+-unit2 a)))
  p0' a zero (succ c) = ≡-cong2 neg (p0'' a c (succ zero))
  p0' a (succ b) zero = p0''' a b
  p0' a (succ b) (succ c) = p0' a b c

  p05' : (a b : Nat) → (a - succ b) ≡ (neg zero +ᵢ (a - b))
  p05' zero zero = refl (neg zero)
  p05' zero (succ b) = ≡-cong2 neg (≡-sym (+-succ2 b))
  p05' (succ a) zero = refl (a - zero)
  p05' (succ a) (succ b) = p05' a b

  p04' : (a b : Nat) → ((a - zero) +ᵢ neg b) ≡ (neg zero +ᵢ (a - b))
  p04' zero zero = refl (neg zero)
  p04' zero (succ b) = ≡-cong2 neg (≡-sym (+-succ2 b))
  p04' (succ a) zero = refl (a - zero)
  p04' (succ a) (succ b) = p05' a b

  p0 : (x y z : Nat) → ((y - succ x) +ᵢ neg z) ≡ (neg x +ᵢ (y - succ z))
  p0 x zero z = refl (neg (x + z + succ zero))
  p0 zero (succ y) z = p04' y z
  p0 (succ x) (succ y) z = ≡-trans (p0 x y z) (p0' x y z)

z+-assoc (neg x) (neg y) (pos z) = p0 x y z
  where
  p0'' : (a b c : Nat) → a + (succ b) + c ≡ succ (a + b + c)
  p0'' zero     b c = refl (succ (b + c))
  p0'' (succ a) b c = ≡-cong succ (p0'' a b c)

  p0' : (x y z : Nat) → (z - (x + y + succ zero)) ≡ (neg x +ᵢ (z - y))
  p0' x zero     zero     = ≡-trans (minus-cong (+-succ2 (x + zero)) zero) (≡-cong2 neg (+-unit2 x))
  p0' x zero     (succ z) = minus-cong (≡-trans (+-succ2 (x + zero)) (≡-cong succ (+-unit2 x))) (succ z)
  p0' x (succ y) zero     = minus-cong (p0'' x y (succ zero)) zero
  p0' x (succ y) (succ z) = ≡-trans (minus-cong (p0'' x y (succ zero)) (succ z)) (p0' x y z)

  p0 : (x y z : Nat) → ((neg x +ᵢ neg y) +ᵢ pos z) ≡ (neg x +ᵢ (neg y +ᵢ pos z))
  p0 x y zero     = refl (neg (x + y + succ zero))
  p0 x y (succ z) = p0' x y z

z+-assoc (neg x) (neg y) (neg z) = p0 x y z
  where
  +-assoc4 : (a b c d : Nat) → a + b + c + d ≡ a + c + b + d
  +-assoc4 zero b c d = ≡-cong (λ q → q + d) (+-comm b c)
  +-assoc4 (succ a) b c d = ≡-cong succ (+-assoc4 a b c d)

  p0' : {a b : Nat} → neg a ≡ neg b → neg (succ a) ≡ neg (succ b)
  p0' {a} {b} (refl (neg .a)) = refl (neg (succ a))

  p0 : (x y z : Nat) → ((neg x +ᵢ neg y) +ᵢ neg z) ≡ (neg x +ᵢ (neg y +ᵢ neg z))
  p0 zero     y z = ≡-cong2 (λ q → neg q) (+-assoc4 y (succ zero) z (succ zero))
  p0 (succ x) y z = p0' (p0 x y z)
