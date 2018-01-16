{-
  Proving the axioms of Hilbert's axiom system.
  See https://en.wikipedia.org/wiki/List_of_Hilbert_systems
-}

module Hilbert where

open import Symbols

{- Modus Ponens -}
-- ((P → Q) ∧ P) → Q
MP : {P Q : Set} → (P → Q) → P → Q
MP f p = f p

{- Hilbert's axiom system -}
-- A → (B → A)
H1 : { A B : Set } → A → (B → A)
H1 a b = a

-- (A → (B → C)) → (B → (A → C))
H2 : { A B C : Set } → (A → (B → C)) → (B → (A → C))
H2 f b a = f a b

-- (B → C) → ((A → B) → (A → C))
H3 : { A B C : Set } → (B → C) → ((A → B) → (A → C))
H3 f g a = f (g a)

-- A → (¬A → B)
H4 : { A B : Set} → A → (¬ A → B)
H4 a f = exnihilo (f a)

-- (A → B) → ((¬ A → B) → B)
H5 : (A B : Set) → (A → B) → ((¬ A → B) → B)
H5 A B f g = ∨-elim (LEM A) f g
