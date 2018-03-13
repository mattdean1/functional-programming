module Types.Bool where

data Bool : Set where
  true : Bool
  false : Bool

if_then_else_ : {A : Set} → Bool → (x : A) → (y : A) → A
if true then x else _ = x
if false then _ else y = y
