{-
  Proving the axioms of Lukasiewicz's Hilbert Systems.
  See https://en.wikipedia.org/wiki/List_of_Hilbert_systems
-}

module Lukasiewicz where

open import Symbols

{- Lukasiewicz's first axiom system -}
-- (A → B) → ((B → C) → (A → C))
1A : { A B C : Set } → (A → B) → ((B → C) → (A → C))
1A f g a = g (f a)

-- (¬ A → A) → A
1B : (A : Set) → (¬ A → A) → A
1B A f = ∨-elim (LEM A) identity f

-- A → (¬ A → B)
1C : { A B : Set } → A → (¬ A → B)
1C a f = exnihilo (f a)


{- Lukasiewicz's second axiom system -}
-- ((A → B) → C) → (¬ A → C)
notAtoB : (A B : Set) → ¬ A → A → B
notAtoB A B f a = exnihilo (f a)

2A : (A B C : Set) → ((A → B) → C) → (¬ A → C)
2A A B C f g = f (notAtoB A B g)

-- (¬ A → A) → A
2B = 1B

-- (¬ A → C) → ((B → C) → ((A → B) → C))
intermediate : {A B C : Set} → (A → B) → (B → C) → (A → C)
intermediate f g a = g (f a)

2C : (A B C : Set) → (¬ A → C) → ((B → C) → ((A → B) → C))
2C A B C f g h = ∨-elim (LEM A) (intermediate h g) f


{- Lukasiewicz's third axiom system -}
-- A → (B → A)
3A : { A B : Set } → A → B → A
3A a b = a

-- (A → (B → C)) → ((A → B) → (A → C))
3B : {A B C : Set} → (A → (B → C)) → ((A → B) → (A → C))
3B f g a = f a (g a)

-- (¬ A → ¬ B) → (B → A)
helper : {A B : Set} → (¬ A → ¬ B) → B → ¬ A → A
helper f b g = exnihilo ((f g) b)

3C : (A B : Set) → (¬ A → ¬ B) → (B → A)
3C A B f b = ∨-elim (LEM A) identity (helper f b)
