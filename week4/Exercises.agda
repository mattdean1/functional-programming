module Exercises where

open import Types.Nat
open import Types.Bool
open import Types.Equality

open import Types.Inspect
open import Types.Order


min : Nat → Nat → Nat
min a b = if (a <= b) then a else b

max : Nat → Nat → Nat
max a b = if (a <= b) then b else a


-- min is homogenous
min-hom : ∀ m n → succ (min m n) ≡ min (succ m) (succ n)
min-hom m n with (m <= n)
min-hom m n | true = refl (succ m)
min-hom m n | false = refl (succ n)

-- min/max are monotonic
min-mono : (a b c d : Nat) → a <=p b → c <=p d → (min a c) <=p (min b d)
min-mono a b c d p1 p2 with (a <= c) | (b <= d) | inspect (suspend (_<=_ a) c) | inspect (suspend (_<=_ b) d)
min-mono a b c d p1 p2 | true | true | comp1 | comp2 = p1
min-mono a b c d p1 p2 | true | false | equiv ac | comp2 = <=-trans a c d (<=-comp1 a c ac) p2
min-mono a b c d p1 p2 | false | true | equiv ac | comp2 = <=-trans c a b (<=-comp2 a c ac) p1
min-mono a b c d p1 p2 | false | false | comp1 | comp2 = p2

max-mono : (a b c d : Nat) → a <=p b → c <=p d → (max a c) <=p (max b d)
max-mono a b c d p1 p2 with (a <= c) | (b <= d) | inspect (suspend (_<=_ a) c) | inspect (suspend (_<=_ b) d)
max-mono a b c d p1 p2 | true | true | comp1 | comp2 = p2
max-mono a b c d p1 p2 | true | false | comp1 | equiv bd = <=-trans' p2 (<=-comp2 b d bd)
max-mono a b c d p1 p2 | false | true | comp1 | equiv bd = <=-trans' p1 (<=-comp1 b d bd)
max-mono a b c d p1 p2 | false | false | comp1 | comp2 = p1


{-
Consider the following definition of subtraction on Nat:
  _-_ : Nat → Nat → Nat
  zero - zero = zero
  zero - succ n = zero
  succ m - zero = succ m
  succ m - succ n = m - n
And consider the following definition of a distance between two Nats:
  dist : Nat → Nat → Nat
  dist m n = if m <= n then (n - m) else (m - n)
Show that dist is a metric, that is
the following conditions are satisfied:
  dist m n = 0 if and only if m = n
  dist m n = dist n m
  dist m n <= dist m p + dist p n
-}

_-_ : Nat → Nat → Nat
zero - zero = zero
zero - succ n = zero
succ m - zero = succ m
succ m - succ n = m - n

minus-same : {a b : Nat} → a ≡ b → a - b ≡ zero
minus-same (refl zero) = refl zero
minus-same (refl (succ a)) = minus-same (refl a)


dist : Nat → Nat → Nat
dist m n = if m <= n then (n - m) else (m - n)


dist-m1 : (m n : Nat) → m ≡ n → dist m n ≡ zero
dist-m1 m n p with (m <= n)
dist-m1 m n p | true = minus-same (≡-sym p)
dist-m1 m n p | false  = minus-same p

dist-m1' : (m n : Nat) → dist m n ≡ zero → m ≡ n
dist-m1' zero zero p = refl zero
dist-m1' zero (succ n) ()
dist-m1' (succ m) zero p = p
dist-m1' (succ m) (succ n) p = ≡-cong succ (dist-m1' m n p)


m2-lemma : {m n : Nat} → m <=p n → n <=p m → n - m ≡ m - n
m2-lemma p1 p2 = ≡-trans (minus-same (<=-same p2 p1)) (≡-sym (minus-same (<=-same p1 p2)))

dist-m2 : (m n : Nat) → (dist m n) ≡ (dist n m)
dist-m2 m n with (m <= n) | (n <= m) | inspect (suspend (_<=_ m) n) | inspect (suspend (_<=_ n) m)
dist-m2 m n | true | true | equiv mn | equiv nm = m2-lemma (<=-comp1 m n mn) (<=-comp1 n m nm)
dist-m2 m n | true | false | equiv mn | equiv nm = refl (n - m)
dist-m2 m n | false | true | equiv mn | equiv nm = refl (m - n)
dist-m2 m n | false | false | equiv mn | equiv nm = m2-lemma (<=-comp2 m n mn) (<=-comp2 n m nm)


--   dist m n <= dist m p + dist p n
dist-m3 : (a b c : Nat) → (dist a b) <=p ((dist a c) + (dist c b))
dist-m3 a b c = {!   !}
