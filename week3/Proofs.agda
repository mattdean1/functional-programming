module Proofs where

open import Symbols

--appending nil is a noop
append-nil : ∀ {A} → (l : List A) → l ++ nil ≡ l
append-nil nil = refl nil
append-nil (x :: xs) = ≡-cong ((λ z → x :: z)) (append-nil xs)


-- reverse is an involution (is its own inverse)
reverse-inv : ∀ {A} → (l : List A) → reverse (reverse l) ≡ l
reverse-inv nil = refl nil
reverse-inv (x :: xs) = ≡-trans (a≡b x (reverse xs)) (b≡c x xs)
  where
        a≡b : ∀ {A} → (x : A) → (l : List A) → reverse (l ++ [ x ]) ≡ x :: reverse l
        a≡b x nil = refl [ x ]
        a≡b x (y :: ys) = ≡-cong (λ z → z ++ [ y ]) (a≡b x ys)

        b≡c : ∀ {A} → (x : A) → (l : List A) → x :: reverse (reverse l) ≡ x :: l
        b≡c x xs = ≡-cong (λ z → x :: z) (reverse-inv xs)
