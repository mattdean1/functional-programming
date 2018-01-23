module Proofs where

open import Symbols

--appending nil is a noop
append-nil : ∀ {A} → (l : List A) → l ++ nil ≡ l
append-nil nil = refl nil
append-nil (x :: xs) = ≡-cong ((λ z → x :: z)) (append-nil xs)


{-
  Proof that reverse is an involution (is its own inverse)
    using the transitivity property of equality
    a ≡ b → b ≡ c → a ≡ c

    reverse (reverse l)
  ≡ reverse (reverse (x :: xs))
  ≡ reverse ((reverse xs) ++ [ x ])  - from the definition of reverse
  ≡ x :: reverse (reverse xs)        - a≡b
  ≡ x :: xs                          - b≡c - inductive step
  ≡ l
-}
reverse-inv : ∀ {A} → (l₁ : List A) → reverse (reverse l₁) ≡ l₁
reverse-inv nil = refl nil
reverse-inv (x :: xs) = ≡-trans (a≡b x (reverse xs)) (b≡c x xs)
  where
        a≡b : ∀ {A} → (x : A) → (l₂ : List A) → reverse (l₂ ++ [ x ]) ≡ x :: reverse l₂
        a≡b x nil = refl [ x ]
        a≡b x (y :: ys) = ≡-cong (λ z → z ++ [ y ]) (a≡b x ys)

        b≡c : ∀ {A} → (x : A) → (l₃ : List A) → x :: reverse (reverse l₃) ≡ x :: l₃
        b≡c x l₃ = ≡-cong (λ z → x :: z) (reverse-inv l₃)
