module r3b where

open import Types.Equality
open import Types.Reasoning

-- Show that (Nat, +, 0) is a commutative monoid.
-- abelian group, ring, semi ring

-- commutative monoid has closure, identity, associativity, and commutativity

data Nat : Set where
  zero : Nat
  succ : Nat → Nat

_+_ : Nat → Nat → Nat
zero + b = b
(succ a) + b = succ (a + b)

_*_ : Nat → Nat → Nat
zero * b = zero
(succ a) * b = (a * b) + b

-- closure satisfied by the type sig of +

-- identity element is zero
+-unitr : (x : Nat) → x + zero ≡ x
+-unitr zero = refl zero
+-unitr (succ x) = ≡-cong (λ q → succ q) (+-unitr x)

+-unitl : (x : Nat) → zero + x ≡ x
+-unitl x = refl x


--associativity
+-comm : (a b : Nat) → a + b ≡ b + a
+-comm zero b = ≡-sym (+-unitr b)
+-comm (succ a) b = ≡-trans (≡-cong succ (+-comm a b)) (p b a)
  where
  p : (x y : Nat) → succ (x + y) ≡ x + succ y
  p zero y = refl (succ y)
  p (succ x) y = ≡-cong succ (p x y)


-- commutativity
+-assoc : (a b c : Nat) → (a + (b + c)) ≡ ((a + b) + c)
+-assoc zero b c = refl (b + c)
+-assoc (succ a) b c = ≡-cong succ (+-assoc a b c)

-- multiplication is distributive over addition
*-distl : (a b c : Nat) → a * (b + c) ≡ (a * b) + (a * c)
*-distl zero b c = refl zero
*-distl (succ a) b c
  = begin
    (a * (b + c)) + (b + c)         ≡⟨ ≡-cong (λ x → x + (b + c)) (*-distl a b c) ⟩
    ((a * b) + (a * c)) + (b + c)   ≡⟨ ≡-sym (+-assoc (a * b) (a * c) (b + c)) ⟩
    (a * b) + ((a * c) + (b + c))   ≡⟨ ≡-cong (λ x → (a * b) + x) (+-assoc (a * c) b c) ⟩
    (a * b) + (((a * c) + b) + c)   ≡⟨ ≡-cong (λ x → (a * b) + (x + c)) (+-comm (a * c) b) ⟩
    (a * b) + ((b + (a * c)) + c)   ≡⟨ ≡-cong (λ x → (a * b) + x) (≡-sym (+-assoc b (a * c) c)) ⟩
    (a * b) + (b + ((a * c) + c))   ≡⟨ +-assoc (a * b) b ((a * c) + c) ⟩
    ((a * b) + b) + ((a * c) + c)
    ∎
