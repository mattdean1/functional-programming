module Lists where

data Bool : Set where
  true  : Bool
  false : Bool

data istrue : Bool → Set where
  ok : istrue true

data List (A : Set) : Set where
  nil   : List A
  _::_  : (x : A) → List A → List A
infixr 4 _::_

--  0. Write an append function on lists
append : {A : Set} → List A → List A → List A
append nil       l   = l
append (x :: xs) l   = x :: (append xs l)

-- 1. Write a function that checks two lists have the same length
length-check : {A : Set} → List A → List A → Bool
length-check nil       nil       = true
length-check nil       (x :: xs) = false
length-check (x :: xs) nil       = false
length-check (x :: xs) (y :: ys) = length-check xs ys

-- 2. Write a data-type of proofs that two lists have the same length
data length-proof {A : Set} : List A → List A → Set where
  nils : length-proof nil nil
  cons :   (x : A) → (xs : List A)
         → (y : A) → (ys : List A)
         → length-proof xs ys
         → length-proof (x :: xs) (y :: ys)

--  3. Check/prove that appending nil preserves the length
appnil-check : {A : Set} → (l : List A) → istrue (length-check l (append l nil))
appnil-check nil = ok
appnil-check (x :: xs) = appnil-check xs

appnil-proof : {A : Set} → (l : List A) → length-proof l (append l nil)
appnil-proof nil = nils
appnil-proof (x :: xs) = cons x xs x (append xs nil) (appnil-proof xs)


--  4. Check/prove that appending lists with the same length preserves length
appsame-check : {A : Set} → (l1 l2 l3 : List A)
               → istrue (length-check l1 l2)
               → istrue (length-check (append l1 l3) (append l2 l3))
appsame-check nil       nil       nil       p   = ok
appsame-check nil       nil       (z :: zs) p   = appsame-check nil nil zs p
appsame-check nil       (y :: ys) _       ()
appsame-check (x :: xs) nil       _       ()
appsame-check (x :: xs) (y :: ys) nil       p   = appsame-check xs ys nil p
appsame-check (x :: xs) (y :: ys) l3        p   = appsame-check xs ys l3 p
