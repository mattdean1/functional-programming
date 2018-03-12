module Exercises where

open import Types.Nat
open import Types.Bool
open import Types.Equality
open import Types.Reasoning

open import Properties.Nat.Addition

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





dist-zero : (a : Nat) → dist a zero ≡ a
dist-zero zero = refl zero
dist-zero (succ a) = refl (succ a)

dist-zero' : (a : Nat) → dist zero a ≡ a
dist-zero' zero = refl zero
dist-zero' (succ a) = refl (succ a)


dist<=p+lemma : {a b : Nat} → a <=p b → a <=p succ (succ b)
dist<=p+lemma (zero<=p x) = zero<=p (succ (succ x))
dist<=p+lemma (succ<=p x y p) = succ<=p x (succ (succ y)) (dist<=p+lemma p)

dist<=p+ : (a b : Nat) → (dist a b) <=p (a + b)
dist<=p+ a b with (a <= b) | inspect (suspend (_<=_ a) b)
dist<=p+ a b | true | i = lem a b
  where
    lem : (x y : Nat) → (y - x) <=p (x + y)
    lem zero zero = zero<=p zero
    lem zero (succ y) = succ<=p y y (≡-><=p (refl y))
    lem (succ x) zero = zero<=p (succ (x + zero))
    lem (succ x) (succ y) = <=-trans' (dist<=p+lemma (lem x y)) (≡-><=p (≡-cong succ (+-succ-dist x y)))

dist<=p+ a b | false | i = lem a b
  where
    lem : (x y : Nat) → (x - y) <=p (x + y)
    lem zero zero = zero<=p zero
    lem zero (succ y) = zero<=p (succ y)
    lem (succ x) zero = ≡-><=p (≡-cong succ (≡-sym (+-unitr x)))
    lem (succ x) (succ y) = <=-trans' (dist<=p+lemma (lem x y)) (≡-><=p (≡-cong succ (+-succ-dist x y)))

dist-succ : (a b : Nat) → (dist a b) ≡ (dist (succ a) (succ b))
dist-succ zero zero = refl zero
dist-succ zero (succ b) = refl (succ b)
dist-succ (succ a) zero = refl (succ a)
dist-succ (succ a) (succ b) = refl (if a <= b then b - a else (a - b))

--   dist m n <= dist m p + dist p n
dist-m3 : (a b c : Nat) → (dist a b) <=p ((dist a c) + (dist c b))
dist-m3 zero zero zero = zero<=p zero
dist-m3 zero zero (succ c) = zero<=p (succ (c + succ c))
dist-m3 zero (succ b) zero = ≡-><=p (refl (dist zero (succ b)))
dist-m3 zero (succ b) (succ c)
  = <=begin
      dist zero (succ b)                  <=⟨ (≡-><=p (refl (succ b))) ⟩
      succ b                              <=⟨ <=-succ1 (≡-><=p (≡-sym (dist-zero' b))) ⟩ -- could also apply succ before converting ≡ to <=p
      succ (dist zero b)                  <=⟨ <=-succ1 (dist-m3 zero b c) ⟩
      succ ((dist zero c) + dist c b)     <=⟨ <=-succ1 (≡-><=p (+-cong (dist-zero' c) (dist c b))) ⟩
      succ (c + dist c b)                 <=⟨ <=-succ1 (≡-><=p (+-cong2 (refl c) (dist-succ c b))) ⟩
      succ (c + dist (succ c) (succ b))
    <=∎

dist-m3 (succ a) zero zero = ≡-><=p (lem a) where
  lem : (a : Nat) → dist (succ a) zero ≡ succ (a + dist zero zero)
  lem a
    = begin
      dist (succ a) zero        ≡⟨ refl (succ a) ⟩
      (succ a)                  ≡⟨ ≡-sym (≡-cong succ (+-unitr a)) ⟩
      (succ a) + zero           ≡⟨ refl (succ (a + zero)) ⟩
      succ (a + zero)           ≡⟨ refl (succ (a + zero)) ⟩
      succ (a + dist zero zero)
    ∎

dist-m3 (succ a) zero (succ c)
  = <=begin
      dist (succ a) zero                              <=⟨ ≡-><=p (dist-zero (succ a)) ⟩
      succ a                                          <=⟨ ≡-><=p (≡-cong succ (≡-sym (dist-zero a))) ⟩
      succ (dist a zero)                              <=⟨ <=-succ1 (dist-m3 a zero c) ⟩
      succ (dist a c + dist c zero)                   <=⟨ ≡-><=p (≡-cong succ (+-cong2 (refl (dist a c)) (dist-zero c))) ⟩
      succ (dist a c + c)                             <=⟨ ≡-><=p (+-succ-dist (dist a c) c) ⟩
      dist a c + succ c                               <=⟨ ≡-><=p (+-cong2 (dist-succ a c) (refl (succ c))) ⟩
      (dist (succ a) (succ c) + (succ c))             <=⟨ ≡-><=p (+-cong2 (refl (dist (succ a) (succ c))) (≡-sym (dist-zero (succ c)))) ⟩
      (dist (succ a) (succ c) + dist (succ c) zero)
    <=∎

dist-m3 (succ a) (succ b) zero = dist<=p+ (succ a) (succ b)
dist-m3 (succ a) (succ b) (succ c) = dist-m3 a b c
