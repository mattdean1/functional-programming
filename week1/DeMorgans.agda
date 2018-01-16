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
singleOrNegationL : {P Q : Set} → ¬ (P ∨ Q) → ¬ P
singleOrNegationL f p = f (∨-inl p)

singleOrNegationR : {P Q : Set} → ¬ (P ∨ Q) → ¬ Q
singleOrNegationR f q = f (∨-inr q)

1A : {P Q : Set} → ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)
1A f = ∧-in (singleOrNegationL f) (singleOrNegationR f)


1B : {P Q : Set} → ¬ P ∧ ¬ Q → ¬ (P ∨ Q)
1B (∧-in notP notQ) pORq = ∨-elim pORq notP notQ


{-
  2. ¬(P ∧ Q) <=> (¬P) ∨ (¬Q)

    a) ¬(P ∧ Q) → ¬P ∨ ¬Q
    b) ¬P ∨ ¬Q → ¬(P ∧ Q)
-}
singleAndNegationL : {P Q : Set} → ¬ (P ∧ Q) → P → ¬ Q
singleAndNegationL f p q = f (∧-in p q)

disjIn : {P Q : Set} → (P → ¬ Q) → P → ¬ P ∨ ¬ Q
disjIn f p = ∨-inr (f p)

2A : (P Q : Set) → ¬ (P ∧ Q) → ¬ P ∨ ¬ Q
2A P Q f = ∨-elim (LEM P) (disjIn (singleAndNegationL f)) ∨-inl


2B : {P Q : Set} → ¬ P ∨ ¬ Q → ¬ (P ∧ Q)
2B (∨-inl notP) (∧-in p q) = notP p
2B (∨-inr notQ) (∧-in p q) = notQ q
