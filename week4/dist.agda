module dist where

open import Types.Nat
open import Types.Bool
open import Types.Equality
open import Types.Order
open import Types.Inspect

open import Properties.Addition
open import Properties.Order
open import Subtraction


dist : Nat → Nat → Nat
dist m n = if m <= n then (n - m) else (m - n)

dist-zero : (a : Nat) → dist a zero ≡ a
dist-zero zero = refl zero
dist-zero (succ a) = refl (succ a)

dist-zero' : (a : Nat) → dist zero a ≡ a
dist-zero' zero = refl zero
dist-zero' (succ a) = refl (succ a)

dist-succ : (a b : Nat) → (dist a b) ≡ (dist (succ a) (succ b))
dist-succ zero zero = refl zero
dist-succ zero (succ b) = refl (succ b)
dist-succ (succ a) zero = refl (succ a)
dist-succ (succ a) (succ b) = refl (if a <= b then b - a else (a - b))


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
