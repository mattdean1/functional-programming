module Equality where

open import Symbols

{-
  6. Re-do exercises 3 and 4 using ≡.
    a) Check/prove that appending nil preserves the length
    b) Check/prove that appending lists with the same length preserves length
-}

-- 7. Prove reflexivity, symmetry, transitivity, and congruence of ≡
≡-refl : {A : Set} → (a : A) → a ≡ a
≡-refl a = refl a

≡-sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
≡-sym (refl a) = refl a

≡-trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
≡-trans (refl a) (refl b) = refl b

≡-cong : {A : Set} {a b : A} → (f : A → A) → a ≡ b → (f a) ≡ (f b)
≡-cong f (refl a) = refl (f a)


-- 8. Prove the Leibniz axioms for ≡
≡-leibniz : {A : Set} {x y : A} → ((f : A → A) → (f x) ≡ (f y)) → x ≡ y
≡-leibniz g = g (λ z → z)
