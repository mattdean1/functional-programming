module r2 where
{-
0. Write an append function on lists
1. Write a function that checks two lists have the same length
2. Write a data-type of proofs that two lists have the same length
3. Check/prove that appending nil preserves the length
4. Check/prove that appending lists with the same length preserves length
5. Prove soundness and completeness of of checking/proving same-length
-}

data List (A : Set) : Set where
  nil : List A
  _::_ : (x : A) → List A → List A

data Bool : Set where
  True : Bool
  False : Bool

data istrue : Bool → Set where
  ok : istrue True

append : {A : Set} → List A → List A → List A
append nil l2 = l2
append (x :: l1) l2 = x :: (append l1 l2)

data lengthProof {A : Set} : List A → List A → Set where
  nils : lengthProof nil nil
  cons : (x : A) → (xs : List A) →
         (y : A) → (ys : List A) →
         lengthProof xs ys →
         lengthProof (x :: xs) (y :: ys)

checkLength : {A : Set} → List A → List A → Bool
checkLength nil nil = True
checkLength nil (x :: l2) = False
checkLength (x :: l1) nil = False
checkLength (x :: l1) (x₁ :: l2) = checkLength l1 l2

appnil-check : {A : Set} → (l : List A) → istrue (checkLength l (append nil l))
appnil-check nil = ok
appnil-check (x :: l) = appnil-check l

appnil-proof : {A : Set} → (l : List A) → lengthProof l (append nil l)
appnil-proof nil = nils
appnil-proof (x :: l) = cons x l x l (appnil-proof l)


appsame-proof : {A : Set} → (l1 l2 l3 : List A) → lengthProof l2 l3 → lengthProof (append l2 l1) (append l3 l1)
appsame-proof l _ _ nils               = appnil-proof l
appsame-proof l _ _ (cons x xs y ys p) = cons x (append xs l) y (append ys l) (appsame-proof l xs ys p)

appsame-check : {A : Set} → (l1 l2 l3 : List A) → istrue (checkLength l2 l3) → istrue (checkLength (append l1 l2) (append l1 l3))
appsame-check nil       l2 l3 b = b
appsame-check (x :: l1) l2 l3 b = appsame-check l1 l2 l3 b


p-c : {A : Set} → {l1 l2 : List A} → lengthProof l1 l2 → istrue (checkLength l1 l2)
p-c nils = ok
p-c (cons x xs y ys p) = p-c p

c-p : {A : Set} → {l1 l2 : List A} → istrue (checkLength l1 l2) → lengthProof l1 l2
c-p {A} {nil}     {nil}      b  = nils
c-p {A} {nil}     {y :: ys}  ()
c-p {A} {x :: xs} {nil}      ()
c-p {A} {x :: xs} {y :: ys} b   = cons x xs y ys (c-p b)
