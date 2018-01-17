module Postulates where

open import Symbols

-- postulate LEM : (A : Set) → A ∨ ¬ A
-- postulate DNE : {A : Set} → ¬ (¬ A) → A

-- LEM → DNE
LD : {A : Set} → A ∨ ¬ A → (¬ (¬ A) → A)
LD disj f = ∨-elim disj identity (λ notA → exnihilo (f notA))

-- DNE → LEM
DL : {A : Set} → (¬ (¬ A) → A) → A ∨ ¬ A
DL f = {!   !}
