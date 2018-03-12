module Types.Order where

open import Types.Nat
open import Types.Bool
open import Types.Equality

_<=_ : Nat → Nat → Bool
zero     <= _        = true
_        <= zero     = false
(succ a) <= (succ b) = a <= b

data _<=p_ : Nat → Nat → Set where
  zero<=p : (x : Nat) → zero <=p x
  succ<=p : (x y : Nat) → x <=p y → (succ x) <=p (succ y)

<=-comp1 : (a b : Nat) → a <= b ≡ true → a <=p b
<=-comp1 zero     zero     p  = zero<=p zero
<=-comp1 zero     (succ b) p  = zero<=p (succ b)
<=-comp1 (succ a) zero     ()
<=-comp1 (succ a) (succ b) p  = succ<=p a b (<=-comp1 a b p)

<=-comp2 : (a b : Nat) → a <= b ≡ false → b <=p a
<=-comp2 zero     zero     p  = zero<=p zero
<=-comp2 zero     (succ b) ()
<=-comp2 (succ a) zero     p  = zero<=p (succ a)
<=-comp2 (succ a) (succ b) p  = succ<=p b a (<=-comp2 a b p)

<=-trans : (a b c : Nat) → a <=p b → b <=p c → a <=p c
<=-trans .zero .zero c (zero<=p .zero) (zero<=p .c) = zero<=p c
<=-trans .zero .(succ x) .(succ y) (zero<=p .(succ x)) (succ<=p x y p2) = zero<=p (succ y)
<=-trans .(succ x) .(succ y) .(succ y₁) (succ<=p x y p1) (succ<=p .y y₁ p2) = succ<=p x y₁ (<=-trans x y y₁ p1 p2)

<=-trans' : {a b c : Nat} → a <=p b → b <=p c → a <=p c
<=-trans' (zero<=p .zero) (zero<=p x) = zero<=p x
<=-trans' (zero<=p .(succ x)) (succ<=p x y p2) = zero<=p (succ y)
<=-trans' (succ<=p x y p1) (succ<=p .y y₁ p2) = succ<=p x y₁ (<=-trans' p1 p2)

<=-same : {a b : Nat} → a <=p b → b <=p a → a ≡ b
<=-same (zero<=p .zero) (zero<=p .zero) = refl zero
<=-same (succ<=p x y p1) (succ<=p .y .x p2) = ≡-cong succ (<=-same p1 p2)


<=-succ1 : {a b : Nat} → a <=p b → (succ a) <=p (succ b)
<=-succ1 (zero<=p x) = succ<=p zero x (zero<=p x)
<=-succ1 (succ<=p x y p) = succ<=p (succ x) (succ y) (<=-succ1 p)

<=-succ2 : {a b : Nat} → a <=p b → a <=p (succ b)
<=-succ2 (zero<=p x) = zero<=p (succ x)
<=-succ2 (succ<=p x y p) = succ<=p x (succ y) (<=-succ2 p)

≡-><=p : {a b : Nat} → a ≡ b → a <=p b
≡-><=p (refl zero) = zero<=p zero
≡-><=p (refl (succ a)) = succ<=p a a (≡-><=p (refl a))
