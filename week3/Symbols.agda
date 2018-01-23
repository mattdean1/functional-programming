module Symbols where

data _≡_ {A : Set} : A → A → Set where
  refl : (x : A) → x ≡ x
infix 0 _≡_

≡-cong : {A : Set} {a b : A} → (f : A → A) → a ≡ b → (f a) ≡ (f b)
≡-cong f (refl a) = refl (f a)

≡-trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
≡-trans (refl a) (refl b) = refl b

≡-sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
≡-sym (refl a) = refl a


data List (A : Set) : Set where
  nil   : List A
  _::_  : (x : A) → List A → List A
infixr 4 _::_

_++_ : ∀ {A} → List A → List A → List A  -- append
nil ++ l = l
(x :: xs) ++ l = x :: (xs ++ l)

[_] : ∀ {A} → (x : A) → List A
[ x ] = x :: nil

reverse : ∀ {A} → List A → List A
reverse nil = nil
reverse (x :: xs) = (reverse xs) ++ [ x ]
