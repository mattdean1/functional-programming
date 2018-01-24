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
reverse-inv nil       = refl nil
reverse-inv (x :: xs) = ≡-trans (a≡b x (reverse xs)) (b≡c x xs)
  where
        a≡b : ∀ {A} → (x : A) → (l₂ : List A) → reverse (l₂ ++ [ x ]) ≡ x :: reverse l₂
        a≡b x nil       = refl [ x ]
        a≡b x (y :: ys) = ≡-cong (λ z → z ++ [ y ]) (a≡b x ys)

        b≡c : ∀ {A} → (x : A) → (l₃ : List A) → x :: reverse (reverse l₃) ≡ x :: l₃
        b≡c x l₃ = ≡-cong (λ z → x :: z) (reverse-inv l₃)


{-
  Proof that fast-reverse is equivalent to reverse

    reverse l
  ≡ reverse (x :: xs)
  ≡ (reverse xs) ++ [ x ]           - definition of reverse
  ≡ rev-append xs        [ x ]      - p0
  ≡ rev-append xs        (x :: nil) - definition of [ ]
  ≡ rev-append (x :: xs) nil        - definition of rev-append
  ≡ fast-reverse (x :: xs)          - definition of fast-reverse
  ≡ fast-reverse l


  p0:
    (reverse l1) ++ l2
  ≡ (reverse (x :: xs)) ++ l2
  ≡ ((reverse xs) ++ [ x ]) ++ l2   - defition of reverse

    (reverse xs) ++ [ x ] ≡ rev-append xs [ x ]
      - inductive step
    ((reverse xs) ++ [ x ]) ++ l2 ≡ (rev-append xs [ x ]) ++ l2
      - congruence of equality

  ≡ (rev-append xs [ x ]) ++ l2      - inductive step + congruence of ≡
  ≡ rev-append xs ([ x ] ++ l2)      - rev-append-++-assoc
  ≡ rev-append xs (x :: nil ++ l2)   - definition of [ ]
  ≡ rev-append xs (x :: l2)          - definition of ++
  ≡ rev-append (x :: xs) l2          - definition of rev-append
  ≡ rev-append l1 l2
-}
fast-reverse≡reverse : ∀ {A} → (l₁ : List A) → reverse l₁ ≡ fast-reverse l₁
fast-reverse≡reverse nil       = refl nil
fast-reverse≡reverse (x :: xs) = p0 xs [ x ]
  where
    -- rev-append and ++ have some kind of associativity
    rev-append-++-assoc : ∀ {A}
                          → (l₁ l₂ l₃ : List A)
                          → (rev-append l₁ l₂) ++ l₃ ≡ rev-append l₁ (l₂ ++ l₃)
    rev-append-++-assoc nil       l₂ l₃ = refl (l₂ ++ l₃)
    rev-append-++-assoc (x :: xs) l₂ l₃ = rev-append-++-assoc xs (x :: l₂) l₃

    p0 : ∀ {A} → (l₂ l₃ : List A) → (reverse l₂) ++ l₃ ≡ rev-append l₂ l₃
    p0 nil       l₃ = refl l₃
    p0 (y :: ys) l₃ = ≡-trans (≡-cong (λ z → z ++ l₃) (p0 ys [ y ])) (rev-append-++-assoc ys [ y ] l₃)
