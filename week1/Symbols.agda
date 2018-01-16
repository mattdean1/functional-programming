module Symbols where

{- AND -}
data _∧_ (A B : Set) : Set where
  ∧-in : A → B → A ∧ B
infixl  6 _∧_

∧-eliml : {A B : Set} → A ∧ B → A
∧-eliml (∧-in a b) = a

∧-elimr : {A B : Set} → A ∧ B → B
∧-elimr (∧-in a b) = b


{- OR -}
data _∨_ (A B : Set) : Set where
  ∨-inl : A → A ∨ B
  ∨-inr : B → A ∨ B
infixl 5 _∨_

∨-elim : {A B C : Set} → A ∨ B → (A → C) → (B → C) → C
∨-elim (∨-inl a) f _ = f a
∨-elim (∨-inr b) _ g = g b


{- NOT -}
data ⊥ : Set where

¬ : Set → Set
¬ A = A → ⊥

exnihilo : {A : Set} → ⊥ → A
exnihilo ()


{- Classical Logic -}
postulate LEM : (A : Set) → A ∨ ¬ A
postulate DNE : {A : Set} → ¬ (¬ A) → A
