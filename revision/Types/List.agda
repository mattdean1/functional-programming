module Types.List where

data List (A : Set) : Set where
  nil   : List A
  _::_  : (x : A) → List A → List A
infixr 4 _::_

_++_ : ∀ {A} → List A → List A → List A  -- append
nil ++ l = l
(x :: xs) ++ l = x :: (xs ++ l)

[_] : ∀ {A} → (x : A) → List A
[ x ] = x :: nil

reverse : ∀ {A} → List A → List A
reverse nil = nil
reverse (x :: xs) = (reverse xs) ++ [ x ]

rev-append : ∀ {A} → (l₁ l₂ : List A) → List A
rev-append nil l = l
rev-append (x :: xs) l = rev-append xs (x :: l)

fast-reverse : ∀ {A} → List A → List A
fast-reverse l = rev-append l nil
