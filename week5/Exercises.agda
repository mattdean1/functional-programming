{-
Evenness
  - implement a function that tests (returns boolean) if a Nat is even, returning true if it is and false if it is not.
  - define a data-type of proof terms for evenness.
  - prove that the two definitions above are equivalent (soundness and completeness).
  - prove that a Nat n is even if and only if there exists a unique Nat m such that n = m + m

Product
  Assuming that two functions f, g are equal f≡g, by definition, if and only if ∀ x, f(x)≡g(x)
  Formulate in Agda and prove the following property:
  For any functions f : X → A, f' : X → A', there exists a unique function  g ∶ X → A × A'
    such that f ≡ π₁∘g and f' ≡ π₂ ∘ g
    where -∘- is function compositions and π₁, π₂ are the projection functions from A × A'.
-}

module Exercises where

open import Types.Nat
open import Types.Bool
open import Types.Equality
open import Properties.Addition

open import Exists

isEven : Nat → Bool
isEven zero = true
isEven (succ zero) = false
isEven (succ (succ n)) = isEven n

data evenp_ : Nat → Set where
  evenzero : evenp zero
  evensucc : (n : Nat) → evenp n → evenp (succ (succ n))

even-complete : (n : Nat) → isEven n ≡ true → evenp n
even-complete zero            p  = evenzero
even-complete (succ zero)     ()
even-complete (succ (succ n)) p  = evensucc n (even-complete n p)

even-sound : (n : Nat) → evenp n → isEven n ≡ true
even-sound zero            p               = refl true
even-sound (succ zero)     ()
even-sound (succ (succ n)) (evensucc .n p) = even-sound n p

even-same : {a b : Nat} → evenp a → a ≡ b → evenp b
even-same p1 (refl x) = p1


-- prove that a Nat n is even if and only if there exists a unique Nat m such that n = m + m
example : ∃[ m ∶ Nat ] ((succ (succ zero)) ≡ m + m)
example = succ zero , refl (succ (succ zero))

p1 : (n : Nat) → ∃[ m ∶ Nat ] (n ≡ m + m) → evenp n
p1 .(w + w) (w , refl .(w + w)) = lem w where
  lem : (n : Nat) → evenp (n + n)
  lem zero = evenzero
  lem (succ n) = even-same (evensucc (n + n) (lem (n))) (≡-cong succ (+-succ-dist n n))

p2 : (n : Nat) → evenp n → ∃[ m ∶ Nat ] (n ≡ m + m)
p2 .zero evenzero = zero , refl zero
p2 .(succ (succ n)) (evensucc n p) = succ m , lem n m (proof IH) where
  IH : ∃[ m ∶ Nat ] (n ≡ m + m)
  IH = p2 n p
  m : Nat
  m = witness IH
  lem : (x y : Nat) → x ≡ y + y → succ (succ x) ≡ (succ y) + (succ y)
  lem .(y + y) y (refl .(y + y)) = ≡-cong succ (+-succ-dist y y)
