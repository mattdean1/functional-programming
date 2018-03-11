module Properties.Nat.Addition where

open import Types.Equality
open import Types.Nat


-- zero is the identity element
+-unitl : (x : Nat) → zero + x ≡ x
+-unitl x = refl x

+-unitr : (x : Nat) → x + zero ≡ x
+-unitr zero = refl zero
+-unitr (succ x) = ≡-cong succ (+-unitr x)

+-unitrp : {a b : Nat} → a ≡ b → a + zero ≡ b
+-unitrp {.x} {.x} (refl x) = +-unitr x


-- addition is associative
+-assoc : (x y z : Nat) → x + y + z ≡ x + (y + z)
+-assoc zero y z = refl (y + z)
+-assoc (succ x) y z = ≡-cong succ (+-assoc x y z)

+-assoc4 : (a b c d : Nat) → a + (b + c + d) ≡ a + b + c + d
+-assoc4 zero b c d = refl (b + c + d)
+-assoc4 (succ a) b c d = ≡-cong succ (+-assoc4 a b c d)


-- succ is distributive over addition
+-succ-dist : (a b : Nat) → succ (a + b) ≡ a + succ b
+-succ-dist zero b = refl (succ b)
+-succ-dist (succ a) b = ≡-cong succ (+-succ-dist a b)

+-succ-swap : (a b : Nat) → (succ a) + b ≡ a + succ b
+-succ-swap a b = +-succ-dist a b

+-add-one : (a : Nat) → a + succ zero ≡ succ a
+-add-one zero = refl (succ zero)
+-add-one (succ a) = ≡-cong succ (+-add-one a)


-- addition is commutative
+-comm : (a b : Nat) → a + b ≡ b + a
+-comm zero b = ≡-sym (+-unitr b)
+-comm (succ a) b = ≡-trans (≡-cong succ (+-comm a b)) (+-succ-dist b a)

+-comm4 : (a b c d : Nat) → a + b + c + d ≡ a + c + b + d
+-comm4 zero b c d = ≡-cong (λ q → q + d) (+-comm b c)
+-comm4 (succ a) b c d = ≡-cong succ (+-comm4 a b c d)


-- adding the same thing to both sides preserves equality
+-cong : {a b : Nat} → a ≡ b → (n : Nat) → a + n ≡ b + n
+-cong p n = ≡-cong (λ x → x + n) p

+-cong2 : {a b x y : Nat} → a ≡ b → x ≡ y → a + x ≡ b + y
+-cong2 (refl a) (refl x) = refl (a + x)
