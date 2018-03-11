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
min-mono a b c d p1 p2 | true | false | s_equiv ac | comp2 = <=-trans a c d (<=-comp1 a c ac) p2
min-mono a b c d p1 p2 | false | true | s_equiv ac | comp2 = <=-trans c a b (<=-comp2 a c ac) p1
min-mono a b c d p1 p2 | false | false | comp1 | comp2 = p2

max-mono : (a b c d : Nat) → a <=p b → c <=p d → (max a c) <=p (max b d)
max-mono a b c d p1 p2 with (a <= c) | (b <= d) | inspect (suspend (_<=_ a) c) | inspect (suspend (_<=_ b) d)
max-mono a b c d p1 p2 | true | true | comp1 | comp2 = p2
max-mono a b c d p1 p2 | true | false | comp1 | s_equiv bd = <=-trans' p2 (<=-comp2 b d bd)
max-mono a b c d p1 p2 | false | true | comp1 | s_equiv bd = <=-trans' p1 (<=-comp1 b d bd)
max-mono a b c d p1 p2 | false | false | comp1 | comp2 = p1


{-
Consider the following definition of subtraction on Nat:
  _-_ : Nat → Nat → Nat
  zero - zero = zero
  zero - succ n = zero
  succ m - zero = succ m
  succ m - succ n = m - n
And consider the following definition of a distance between two Nats:
  δ : Nat → Nat → Nat
  δ m n = if m <= n then (n - m) else (m - n)
Show that δ is a metric, that is
the following conditions are satisfied:
  δ m n = 0 if and only if m = n
  δ m n = δ n m
  δ m n <= δ m p + δ p n
-}
