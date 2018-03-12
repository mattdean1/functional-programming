module Exercises where

open import Types.Nat
open import Types.Bool
open import Types.Equality
open import Types.Reasoning
open import Types.Inspect
open import Types.Order

open import Properties.Addition
open import Properties.Order


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
min-mono a b c d p1 p2 with (a <= c) | (b <= d) | inspect (suspend (_<=_ a) c)
min-mono a b c d p1 p2 | true  | true  | comp1     = p1
min-mono a b c d p1 p2 | true  | false | equiv ac  = <=-trans a c d (<=-comp1 a c ac) p2
min-mono a b c d p1 p2 | false | true  | equiv ac  = <=-trans c a b (<=-comp2 a c ac) p1
min-mono a b c d p1 p2 | false | false | comp1     = p2

max-mono : (a b c d : Nat) → a <=p b → c <=p d → (max a c) <=p (max b d)
max-mono a b c d p1 p2 with (a <= c) | (b <= d) | inspect (suspend (_<=_ b) d)
max-mono a b c d p1 p2 | true  | true  | comp2    = p2
max-mono a b c d p1 p2 | true  | false | equiv bd = <=-trans' p2 (<=-comp2 b d bd)
max-mono a b c d p1 p2 | false | true  | equiv bd = <=-trans' p1 (<=-comp1 b d bd)
max-mono a b c d p1 p2 | false | false | comp2    = p1


{-
Consider the following definition of subtraction on Nat, and distance between two Nats
-}
open import Subtraction
open import dist

{-
Show that dist is a metric, that is the following conditions are satisfied:
  dist m n = 0 if and only if m = n
  dist m n = dist n m
  dist m n <= dist m p + dist p n
-}

-- dist m n = 0 if and only if m = n
dist-metric1 : (m n : Nat) → m ≡ n → dist m n ≡ zero
dist-metric1 m n p with (m <= n)
dist-metric1 m n p | true = subtract-equal (≡-sym p)
dist-metric1 m n p | false  = subtract-equal p

dist-metric1' : (m n : Nat) → dist m n ≡ zero → m ≡ n
dist-metric1' zero zero p = refl zero
dist-metric1' zero (succ n) ()
dist-metric1' (succ m) zero p = p
dist-metric1' (succ m) (succ n) p = ≡-cong succ (dist-metric1' m n p)


-- dist m n = dist n m
metric2-lemma : {m n : Nat} → m <=p n → n <=p m → n - m ≡ m - n
metric2-lemma p1 p2 = ≡-trans (subtract-equal (<=-same p2 p1)) (≡-sym (subtract-equal (<=-same p1 p2)))

dist-metric2 : (m n : Nat) → (dist m n) ≡ (dist n m)
dist-metric2 m n with (m <= n) | (n <= m) | inspect (suspend (_<=_ m) n) | inspect (suspend (_<=_ n) m)
dist-metric2 m n | true | true | equiv mn | equiv nm = metric2-lemma (<=-comp1 m n mn) (<=-comp1 n m nm)
dist-metric2 m n | true | false | equiv mn | equiv nm = refl (n - m)
dist-metric2 m n | false | true | equiv mn | equiv nm = refl (m - n)
dist-metric2 m n | false | false | equiv mn | equiv nm = metric2-lemma (<=-comp2 m n mn) (<=-comp2 n m nm)


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
