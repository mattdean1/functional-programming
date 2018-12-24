module r4 where

open import Types.Nat
open import Types.Bool
open import Types.Equality
open import Types.Inspect

_<=_ : Nat → Nat → Bool
zero <= x = true
x <= zero = false
(succ a) <= (succ b) = a <= b

data _<=p_ : Nat → Nat → Set where
  zero<=p : (x : Nat) → zero <=p x
  succ<=p : (x y : Nat) → x <=p y → (succ x) <=p (succ y)

_-_ : Nat → Nat → Nat
zero - a = zero
a - zero = a
(succ a) - (succ b) = a - b

sub-eq : {a b : Nat} → a ≡ b → a - b ≡ zero
sub-eq (refl zero) = refl zero
sub-eq (refl (succ x)) = sub-eq (refl x)

dist : Nat → Nat → Nat
dist a b = if a <= b then (b - a) else (a - b)

-- dist<=p+ : (a b : Nat) → (dist a b) <=p (a + b)
-- dist<=p+ a b with (a <= b) | inspect (suspend (_<=_ a) b)
-- dist<=p+ a b | true | equiv i = {!   !}
-- dist<=p+ a b | false | i = {!   !}



data Vec (A : Set) : Nat → Set where
  vnil : Vec A zero
  _::_ : {n : Nat} → A → Vec A n → Vec A (succ n)

hd : {A : Set}{n : Nat} → Vec A (succ n) → A
hd (x :: xs) = x

₁ : Nat
₁ = succ zero

tl : {A : Set}{n : Nat} → Vec A ((succ zero) + n) → Vec A n
tl (x :: xs) = xs

_++v_ : {A : Set}{m n : Nat} → Vec A n → Vec A m → Vec A (n + m)
vnil ++v v2 = v2
(x :: xs) ++v v2 = x :: (xs ++v v2)

revv : {A : Set}{n : Nat} → Vec A n → Vec A n
revv vnil = vnil
revv (x :: xs) = {! (revv xs) ++v (x :: vnil)  !}

mapv : {A B : Set}{n : Nat} → Vec A n → (A → B) → Vec B n
mapv vnil f = vnil
mapv (x :: v) f = (f x) :: (mapv v f)

foldv : {A B : Set}{n : Nat} → Vec A n → (A → B → B) → B → B
foldv vnil op acc = acc
foldv (x :: v) op acc = foldv v op (op x acc)
