module Postulates where

open import Symbols

-- postulate LEM : (A : Set) → A ∨ ¬ A
-- postulate DNE : {A : Set} → ¬ (¬ A) → A

-- LEM → DNE
h : {A : Set} → ¬ (¬ A) → ¬ A → A
h doubleNeg notA = exnihilo (doubleNeg notA)

LD : {A : Set} → A ∨ ¬ A → (¬ (¬ A) → A)
LD disj f = ∨-elim disj identity (h f)

-- DNE → LEM
DL : {A : Set} → (¬ (¬ A) → A) → A ∨ ¬ A
DL f = {!   !}
