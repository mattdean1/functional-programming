{-
1. Define a max function on Nat

2. Show that max and min are monotonic with respect to the order, that is a1≤ a2 and b1 ≤ b2 implies that min a1  b1 ≤ min a2 b2 and max a1 b1 ≤ max a2 b2

3. Consider the following definition of subtraction on Nat:
  _-_ : Nat → Nat → Nat
  zero - zero = zero
  zero - suc n = zero
  suc m - zero = suc m
  suc m - suc n = m - n
And consider the following definition of a distance between two Nats:
  δ : Nat → Nat → Nat
  δ m n = if m ≤ n then (n - m) else (m - n)
Show that δ is a metric, that is
the following conditions are satisfied:
  δ m n = 0 if and only if m = n
  δ m n = δ n m
  δ m n ≤ δ m p + δ p n
-}
