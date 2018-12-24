module r1 where

{-
  Q1 from class test
  Examine whether the "law of excluded middle" (A ⋁ ¬A) and
  "double-negation elimination" (¬¬A → A) are equivalent in Agda.
-}

data ⊥ : Set where

¬ : Set → Set
¬ A = A → ⊥

data _∨_ (A B : Set) : Set where
  ∨-inl : A → A ∨ B
  ∨-inr : B → A ∨ B

∨-elim : {A B C : Set} → (A ∨ B) → (A → C) → (B → C) → C
∨-elim (∨-inl a) f _ = f a
∨-elim (∨-inr b) _ g = g b

exnihilo : {A : Set} → ⊥ → A
exnihilo ()

p1 : {A : Set} → (A ∨ ¬ A) → (¬ (¬ A) → A)
-- types are right associative so we have (A ∨ ¬ A) → ¬¬A → A
p1 disj f = ∨-elim disj (λ a → a) (λ notA → exnihilo(f notA))

--p2 : {A : Set} → (¬ (¬ A) → A) → (A ∨ ¬ A)
--p2 dne = dne (λ f → f (disj-inr (λ b → f (disj-inl b))))

{-
  Q2 from class test
  [5pts] Define the type of lists in Agda.
  [5pts] Define a type of binary trees in Agda.
  [5pts] Define a traversal function from trees to lists.
  Formulate [5pts] and prove the property that an element belongs to a tree
  if [5pts] and only if [5pts] it belongs to its traversal.
-}

data List (A : Set) : Set where
  nil  : List A
  _::_ : (x : A) → List A → List A
