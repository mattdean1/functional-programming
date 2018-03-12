module Properties.Nat.Multiplication where

open import Types.Equality
open import Types.Nat
open import Types.Reasoning

open import Properties.Nat.Addition

-- one is the identity element
*-unitl : (n : Nat) → succ zero * n ≡ n
*-unitl n = refl n

*-unitr : (n : Nat) → n * succ zero ≡ n
*-unitr zero = refl zero
*-unitr (succ n) = lemma (*-unitr n)
  where
  lemma : {a b : Nat} → a ≡ b → a + succ zero ≡ succ b
  lemma (refl a) = +-add-one a


-- zero annihilates Nat
*-zerol : (a : Nat) → a * zero ≡ zero
*-zerol zero = refl zero
*-zerol (succ a) = +-unitrp (*-zerol a)

*-zeror : (a : Nat) → zero * a ≡ zero
*-zeror a = refl zero


-- multiplication is distributive over addition
*-distl : (a b c : Nat) → a * (b + c) ≡ (a * b) + (a * c)
*-distl zero b c = refl zero
*-distl (succ a) b c
  = begin
    (a * (b + c)) + (b + c)       ≡⟨ ≡-cong (λ q → q + (b + c)) (*-distl a b c) ⟩
    (a * b) + (a * c) + (b + c)   ≡⟨ +-assoc (a * b) (a * c) (b + c) ⟩
    (a * b) + ((a * c) + (b + c)) ≡⟨ ≡-cong (λ q → (a * b) + q) (≡-sym (+-assoc (a * c) b c)) ⟩
    (a * b) + ((a * c) + b + c)   ≡⟨ +-assoc4 (a * b) (a * c) b c ⟩
    (a * b) + (a * c) + b + c     ≡⟨ +-comm4 (a * b) (a * c) b c ⟩
    (a * b) + b + (a * c) + c     ≡⟨ +-assoc ((a * b) + b) (a * c) c ⟩
    (a * b) + b + ((a * c) + c)
    ∎

*-distr : (a b c : Nat) → (a + b) * c ≡ (a * c) + (b * c)
*-distr zero b c = refl (b * c)
*-distr (succ a) b c
  = begin
    ((a + b) * c) + c         ≡⟨ ≡-cong (λ q → q + c) (*-distr a b c) ⟩
    (a * c) + (b * c) + c     ≡⟨ +-assoc (a * c) (b * c) c ⟩
    (a * c) + ((b * c) + c)   ≡⟨ +-cong2 (refl (a * c)) (+-comm (b * c) c) ⟩
    (a * c) + (c + (b * c))   ≡⟨ ≡-sym (+-assoc (a * c) c (b * c)) ⟩
    (a * c) + c + (b * c)
    ∎

-- multiplication is associative
*-assoc : (a b c : Nat) → (a * b) * c ≡ a * (b * c)
*-assoc zero     b c = refl zero
*-assoc (succ a) b c
  = begin
      (((a * b) + b) * c)      ≡⟨ *-distr (a * b) b c ⟩
      ((a * b) * c) + (b * c)  ≡⟨ ≡-cong (λ z → z + (b * c)) (*-assoc a b c) ⟩
      (a * (b * c)) + (b * c)
      ∎
