{-
  Proving De Morgan's laws.
  See the law definitions at: http://mathworld.wolfram.com/deMorgansLaws.html
-}

module DeMorgans where

open import Symbols

{-
  1. ¬(P ∨ Q) <=> (¬P) ∧ (¬Q)

    a) ¬(P ∨ Q) → ¬P ∧ ¬Q
    b) ¬P ∧ ¬Q → ¬(P ∨ Q)
-}
1A : {P Q : Set} → ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)
1A f = ∧-in (λ p → f (∨-inl p)) (λ q → f (∨-inr q))


1B : {P Q : Set} → ¬ P ∧ ¬ Q → ¬ (P ∨ Q)
1B (∧-in notP notQ) pORq = ∨-elim pORq notP notQ


{-
  2. ¬(P ∧ Q) <=> (¬P) ∨ (¬Q)

    a) ¬(P ∧ Q) → ¬P ∨ ¬Q
    b) ¬P ∨ ¬Q → ¬(P ∧ Q)
-}
2A : (P Q : Set) → ¬ (P ∧ Q) → ¬ P ∨ ¬ Q
2A P Q f = ∨-elim (LEM P) (λ p → ∨-inr (singleAndNegationL f p)) ∨-inl where
  singleAndNegationL : {P Q : Set} → ¬ (P ∧ Q) → P → ¬ Q
  singleAndNegationL f p q = f (∧-in p q)


2B : {P Q : Set} → ¬ P ∨ ¬ Q → ¬ (P ∧ Q)
2B (∨-inl notP) (∧-in p q) = notP p
2B (∨-inr notQ) (∧-in p q) = notQ q
