

module AFP where

data _∨_ (A B : Set) : Set where
  inl : A → A ∨ B
  inr : B → A ∨ B

infixl 5 _∨_

DE : {A B C : Set} → (A → C) → (B → C) → A ∨ B → C
DE f _ (inl x) = f x
DE _ g (inr x) = g x

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

_+_ : Nat → Nat → Nat
zero + n = n
suc m + n = suc (m + n)
infixl 5 _+_

₀ = zero
₁ = suc zero
₂ = ₁ + ₁
₄ = ₂ + ₂


-------------------------------------------------------------------
--                   WEEK 2 LECTURE 1                            --
-------------------------------------------------------------------

{-
  PROOF VS. VERIFICATION  :  A subtle but important distinction
-}

-- The set of Booleans
data Bool : Set where
  true  : Bool
  false : Bool

_||_ : Bool → Bool → Bool
true || _ = true
_ ||  true = true
_ || _ = false

infixl 4 _||_

_&&_ : Bool → Bool → Bool
false && _ = false
_ && false = false
_ && _ = true

infixl 5 _&&_

-- VERIFY whether two Nats are equal
check-eq : Nat → Nat → Bool
check-eq zero    zero    = true
check-eq (suc m) (suc n) = check-eq m n
check-eq _       _       = false

-- A type that corresponds to a value !
data istrue : Bool → Set where
  ok : istrue true
-- OBS: value used in type definition

-- Alternative: construct a PROOF that two Nats are equal
data prove-eq : Nat → Nat → Set where
  zero-eq : prove-eq zero zero
  succ-eq : (m n : Nat) → prove-eq m n → prove-eq (suc m) (suc n)

-- Exercise: Check that zero is a right-identity for +
zero-rid+ck : ∀ n → istrue (check-eq (n + zero) n)
zero-rid+ck zero    = ok
zero-rid+ck (suc n) = zero-rid+ck n
{-
 Obs:
 ‣ notation ∀ m → instead of (m : Nat) →
 ‣ variables declared and used in function declaration
 ‣ terminating recursion / 'induction'
-}

-- Example: checking this fact for ₂ = suc (suc zero)
ex-ci : istrue (check-eq (₂ + ₀) ₂)
ex-ci = zero-rid+ck ₂ -- = ok if ^C^N

-- Exercise: prove that zero is a right-identity for +
zero-rid+pv : ∀ n → prove-eq (n + zero) n
zero-rid+pv zero    = zero-eq
zero-rid+pv (suc n) = succ-eq (n + zero) n (zero-rid+pv n)

-- Example: proving this fact for ₂
ex-pi : prove-eq (₂ + ₀) ₂
ex-pi = zero-rid+pv ₂
-- = succ-eq (suc zero) (suc zero) (succ-eq zero zero zero-eq)

{-
 OBS: A proof is more informative.
 It explains 'why' whereas a check only says 'what'.
 Lets see how 'checked' vs 'proved' equalities work out.
 Exercise: Equality is an equivalence (reflexive, symmetric, transitive).
-}

refl-eq-pv : ∀ n → prove-eq n n
refl-eq-pv zero    = zero-eq
refl-eq-pv (suc n) = succ-eq _ _ (refl-eq-pv n)

refl-eq-ck : ∀ n → istrue (check-eq n n)
refl-eq-ck zero    = ok
refl-eq-ck (suc n) = refl-eq-ck n

sym-eq-pv : ∀ m n → prove-eq m n → prove-eq n m
sym-eq-pv  _       _        zero-eq         = zero-eq
sym-eq-pv (suc .m) (suc .n) (succ-eq m n x) = succ-eq n m (sym-eq-pv m n x)
{-
 OBS:
 ‣ pattern-match on proof term
 ‣ multiple occurrences of a variable in a pattern using .
 ‣ termination and coverage checking in Agda are complex
-}

sym-eq-ck : ∀ m n → istrue (check-eq m n) → istrue (check-eq n m)
sym-eq-ck zero    zero    _ = ok
sym-eq-ck zero    (suc n) ()
sym-eq-ck (suc m) zero    ()
sym-eq-ck (suc m) (suc n) x = sym-eq-ck m n x

trans-eq-pv : ∀ m n p → prove-eq m n → prove-eq n p → prove-eq m p
trans-eq-pv zero      zero     zero    zero-eq         zero-eq
  = zero-eq
trans-eq-pv (suc .m) (suc .n) (suc .p) (succ-eq m n x) (succ-eq .n p y)
  = succ-eq _ _ (trans-eq-pv m n p x y)

trans-eq-ck : ∀ m n p → istrue (check-eq m n)
                      → istrue (check-eq n p)
                      → istrue (check-eq m p)
trans-eq-ck zero    zero    _       _  y = y
trans-eq-ck zero    (suc n) p       () _
trans-eq-ck (suc m) zero    p       () _
trans-eq-ck (suc m) (suc n) zero    _  ()
trans-eq-ck (suc m) (suc n) (suc p) x  y = trans-eq-ck m n p x y
{-
 Obs:
 With 'proofs' we can pattern-match the proof and only consider
 cases for which the proof holds.
 Agda can have multiple occurrences of variables in a pattern using '.x'.
 With 'checks' we cannot pattern-match the (trivial) check.
 So we must pattern-match the arguments.
 This leads to more cases. Agda pattern-match exhaustiveness checking helps.
-}

-------------------------------------------------------------------
--                   WEEK 2 LECTURE 2                            --
-------------------------------------------------------------------

{-
  OBS: How do we know we have the 'right' notion of equality? This is a
  rather philosophical question. We can show that the two definitions
  coincide, as a sanity check (see below) but we can also try to show that
  the definitions meet other properties of equality, such as the Leibniz
  axioms. Informally, they are

  ∀ m n ∀ P. m = n ↔ P (m) = P (n)

  However, we only have equality at Nat. So lets try that!
-}

cong-eq-pv : ∀ m n → (f : Nat → Nat) → prove-eq m n → prove-eq (f m) (f n)
cong-eq-pv .zero .zero f zero-eq = refl-eq-pv (f zero)
-- We need to produce data of type 'prove-eq (f zero) (f zero)'
cong-eq-pv .(suc m) .(suc n) f (succ-eq m n p) = cong-eq-pv m n g p
  where
  g : Nat → Nat
  g x = f (suc x)
{- Comment on the proof:
   m, n : Nat
   f : Nat → Nat
   p : prove-eq m n
   succ-eq m n p : prov-eq (suc m) (suc n) ... Note this is not inductively on m or n
   We need to prove (construct) prove-eq (f (suc m)) (f (suc n)).
   This is going to be a proof by induction with inductive call
   conge-eq-pv m n g? p
   Note that even though we made an induction on the proof-term, the inductive call
   is on m and n. This is ok, both pattern coverage and termination check succeed,
   but for different reasons.
   The trick here is to find the function g?
   Looking at the type that we need to prove/construct, we need a function that
   would lead to f (suc m) and f(suc n)... that function is
   g? = λ z → f (suc z).
   QED
-}

cong-eq-ck : ∀ m n → (f : Nat → Nat)
                   → istrue (check-eq m n)
                   → istrue (check-eq (f m) (f n))
cong-eq-ck zero zero f p = refl-eq-ck (f zero)
cong-eq-ck zero (suc n) f ()
cong-eq-ck (suc m) zero f ()
cong-eq-ck (suc m) (suc n) f p = cong-eq-ck m n (λ z → f (suc z)) p

Leibniz-eq-pv : ∀ m n → ((f : Nat → Nat) → prove-eq (f m) (f n)) → prove-eq m n
Leibniz-eq-pv m n p = p (λ z → z)
-- We only need to find an instance of p. Identity does it.

Leibniz-eq-ck : ∀ m n
  → ((f : Nat → Nat) → istrue (check-eq (f m) (f n)))
  → istrue (check-eq m n)
Leibniz-eq-ck m n p = p (λ z → z)

{-
  OBS:
  This is a weak form of axioms since we only have equality at Nat.
-}

{-
======================================================================
==           SOUNDNESS AND COMPLETENESS THEOREMS                    ==
======================================================================
-}

-- "Theorem"
-- In general, if we have a proof, then equality should check ('soundness')
sound-eq : ∀ m n → prove-eq m n → istrue (check-eq m n)
sound-eq _   _ zero-eq         = ok
{- Explanation:
   We are using induction on the third argument, which is a 'proof term.'
   In the case zero-eq : prove-eq zero zero it follows that the first
   two arguments can be inferred as m = n = zero.
   We need the function to produce a term of type istrue (check-eq zero zero),
   which is the same as a term of type (istrue true).
   The type (istrue true) is inhabited by 'ok'.
-}
sound-eq ._ ._ (succ-eq m n p) = sound-eq m n p
{-
  Explanation:
  The second inductive case is succ-eq m n p : prove_eq (suc m) (suc n)
  (Looking at the type of the thrid argument it follows that the first argument
  must be 'suc m' and the second 'suc n'. Since they can be safely inferred,
  we can use '._' for the argument which means, roughly speaking, 'the safely
  inferred argument'. If there is no safely inferrable argument then the '._'
  will be hightlighted in yellow.)
  So it means that we need to produce a term of type istrue (check-eq (suc m) (suc n),
  which simplifies, by executing the function check-eq, to istrue check-eq m n
  This is the same type as 'sound-eq m n p', so we use that.
  Agda makes sure that this is a terminating call.
-}

-- "Theorem"
-- In general, if equality checks out, then we should be able to prove it
-- ('completeness')
compl-eq : ∀ m n → istrue (check-eq m n) → prove-eq m n
compl-eq zero    zero    ok = zero-eq
compl-eq (suc m) (suc n) q = succ-eq m n (compl-eq m n q)
compl-eq zero    (suc n) ()
compl-eq (suc m) zero    ()
{-
 OBS:
 pattern-match on Nats
 q : istrue (check-eq m n)
 impossible patterns
 '_' on the RHS stands for 'inferred argument'
     If it cannot be inferred then Agda will highlight it in yellow
-}

-- We can construct a proof of equality by 'running the theorem'
ex-peq : prove-eq (suc (suc zero)) (suc (suc zero))
ex-peq = compl-eq (suc (suc zero)) (suc (suc zero)) ok
-- = succs (suc zero) (suc zero) (succs zero zero zeros)

----------------------------------
-- A GENERAL NOTION OF EQUALITY --
----------------------------------

data List (A : Set) : Set where
  nil  : List A
  _∷_  : (x : A) → List A → List A

infixr 4 _∷_

-- Example of function on lists, 'length'
length : {A : Set} → List A → Nat
length nil      = zero
length (a ∷ as) = suc (length as)

-- Example of list, lenght of a list
ex-l : List Nat
ex-l = ₀ ∷ ₁ ∷ ₄ ∷ nil

ex-len = length ex-l

{-
LAB EXERCISES
 0. Write an append function on lists
 1. Write a function that checks two lists have the same length
 2. Write a data-type of proofs that two lists have the same length
 3. Check/prove that appending nil preserves the length
 4. Check/prove that appending lists with the same length preserves length
 5. Prove soundness and completeness of of checking/proving same-length
-}

{-
 OBS: In general we cannot use the same strategy to check
      whether two lists are equal!

 list-eq-ck : {A : Set} → List A → List A → Bool
 list-eq-ck nil      nil      = true
 list-eq-ck (x ∷ xs) (y ∷ ys) = What if A is a non-decidable type,
                                e.g. a function?
 list-eq-ck _        _        = false

 … but we can construct a proof that two lists are equal.
 Even better, we can construct a proof that any two things are equal
 … if they are identical!
-}

-- The EQUALITY TYPE
data _≡_ {A : Set} : A → A → Set where
  refl : (x : A) → x ≡ x

infix 0 _≡_

-- How does ≡ compare to prove-eq for Nats?

prove-eq⇒≡ : ∀ m n → prove-eq m n → m ≡ n
prove-eq⇒≡ zero zero zero-eq        = refl zero
prove-eq⇒≡ ._   ._  (succ-eq m n x) = suc≡ m n (prove-eq⇒≡ m n x)
  where
  suc≡ : ∀ m n → m ≡ n → suc m ≡ suc n
  suc≡ .m .m (refl m) = refl (suc m)
-- OBS: Induction on ≡ has only one case (one constructor)
--      A Lemma will be required: suc preserves ≡

≡⇒prove-eq : ∀ m n → m ≡ n → prove-eq m n
≡⇒prove-eq .m .m (refl m) = refl-eq-pv m
{-
 OBS:
 So ≡ is equivalent to prove-eq, but more convenient due to more generality,
 more succinct.
 This is what we will use from now on for all equalities!
-}

{-
EXERCISES FOR THE LAB
 6. Re-do exercises 3 and 4 above using ≡ instead.
 7. Prove reflexivity, symmetry and transitivity of ≡
 8. Prove the Leibniz axioms for ≡
-}

-------------------------------------------------------------------
--                   WEEK 3 LECTURE 1                            --
-------------------------------------------------------------------

{- Agda Automation:
    ^C^C   means pattern-match an argument
    ?      means postpone a term
    ^C^,   means show goal and local variables
    ^C^R   means refine a goal (can take a hint)
    ^C^A   means solve automatically (can take a hint)
    ^C^spc means accept a term
    ^C^f   means move to next goal
    ^C^b   means move to previous goal

   More advanced commands:
    ^C^h   means compute and copy signature of a function ('lemma')
    esc.   go to definition
    esc*   go back
    esc,   go back
    ^u^x=  describe unicode character
-}

sym-≡ : {A : Set} → {x y : A} → x ≡ y → y ≡ x
sym-≡ (refl x) = refl x

trans-≡ : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans-≡ (refl x) (refl .x) = refl x

cong-≡ : {A B : Set} → {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong-≡ f (refl x) = refl (f x)

{- Note: we are using implicit args more aggressively to keep proof terms simple -}

{-
  With the above, we have enough to prove some simple properties of programs.
-}

-- Append two lists
_++_ : {A : Set} → (xs ys : List A) → List A
nil      ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixl 3 _++_

-- Standard property of append : (++, nil, List A) forms a monoid
-- i.e. unit, associative

unitl-nil-++ : {A : Set} → (xs : List A) → nil ++ xs ≡ xs
unitl-nil-++ xs = refl xs

unitr-nil-++ : {A : Set} → (xs : List A) → xs ++ nil ≡ xs -- Note: try ∀ xs → instead
unitr-nil-++ nil = refl nil
unitr-nil-++ (x ∷ xs) = cong-≡ (λ z →  x ∷ z) (unitr-nil-++ xs)

assoc-++ : {A : Set} → (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
assoc-++ nil ys zs = refl (ys ++ zs)
assoc-++ (x ∷ xs) ys zs = cong-≡ (_∷_ x) (assoc-++ xs ys zs)

-- Standard : map and fold
fold : {A B : Set} → (A → B → B) → B → List A → B
fold f b nil      = b
fold f b (x ∷ xs) = f x (fold f b xs)

map : {A B : Set} → (A → B) → List A → List B
map f nil      = nil
map f (x ∷ xs) = (f x) ∷ (map f xs)

-- Obs: 'map f' is a "structure-preserving" function for any f
mf-str-unit : {A B : Set} → (f : A → B) → (map f) nil ≡ nil
mf-str-unit = λ f → refl nil

mf-str-append : {A B : Set} → (f : A → B) → (xs ys : List A)
            → (map f) (xs ++ ys) ≡ (map f xs) ++ (map f ys)
mf-str-append f nil ys = refl (map f ys)
mf-str-append f (x ∷ xs) ys = cong-≡ (_∷_ (f x)) (mf-str-append f xs ys)

-- Optimisation : map-fusion law
_∘_ : {A B C : Set} → (f : A → B)(g : B → C) → (A → C)
f ∘ g = λ x → g (f x)

infixl 5 _∘_

map-fusion : {A B C : Set} → (xs : List A)(f : A → B)(g : B → C)
           → map g (map f xs) ≡ map (f ∘ g) xs
map-fusion xs f g = {!!}


-- More Agda syntax : mixfix operators

[_] : {A : Set} → A → List A
[ x ] = x ∷ nil

if_then_else : {A : Set} → Bool → A → A → A
if true  then x else _ = x
if false then _ else x = x

{- More examples : reverse -}

reverse : {A : Set} → List A → List A
reverse nil      = nil
reverse (x ∷ xs) = (reverse xs) ++ [ x ]

{- A property of reverse : involution -}

rev-app : {A : Set} → (xs ys : List A) → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
rev-app nil ys = sym-≡ (unitr-nil-++ (reverse ys))
rev-app (x ∷ xs) ys = trans-≡ p0 p1 where
  p0 : (reverse (xs ++ ys)) ++ [ x ] ≡ reverse ys ++ reverse xs ++ [ x ]
  p0 = cong-≡ (λ z → z ++ [ x ]) (rev-app xs ys)
  p1 : reverse ys ++ reverse xs ++ [ x ] ≡ reverse ys ++ (reverse xs ++ [ x ])
  p1 = assoc-++ (reverse ys) (reverse xs) (x ∷ nil)

rev-invol : {A : Set} → (xs : List A) → reverse (reverse xs) ≡ xs
rev-invol nil = refl nil
rev-invol (x ∷ xs) = trans-≡ p0 p1 where
  p0 : reverse (reverse xs ++ [ x ]) ≡ x ∷ reverse (reverse xs)
  p0 = rev-app (reverse xs) (x ∷ nil)
  p1 :  x ∷ reverse (reverse xs) ≡ x ∷ xs
  p1 = cong-≡ (λ z → x ∷ z) (rev-invol xs)

{- Fast append : rev-app -}

revapp : {A : Set} → (xs zs : List A) → List A
revapp nil      zs = zs
revapp (x ∷ xs) zs = revapp xs (x ∷ zs)

frev : {A : Set} → List A → List A
frev xs = revapp xs nil

exapp = frev (₁ ∷ ₂ ∷ nil)

revapp-lemma : {A : Set} → (xs ys zs : List A)
             → (revapp xs ys) ++ zs ≡ revapp xs (ys ++ zs)
revapp-lemma xs ys zs = {!!}

reverse=frev : {A : Set} → (xs : List A) → reverse xs ≡ frev xs
reverse=frev nil = refl nil
reverse=frev (x ∷ xs) = {!!}


{-
  WEEK 4 : MORE EXAMPLES
-}

{-
  Binary search tree - of Nats, for simplicity
-}

{- We need comparison -}

_≤_ : Nat → Nat → Bool
zero ≤ _ = true
(suc m) ≤ (suc n) = m ≤ n
(suc _) ≤ zero = false

infix 5 _≤_

data _≤p_ : Nat → Nat → Set where
  zero≤p : ∀ n → zero ≤p n
  suc≤p  : ∀ m n → m ≤p n → suc m ≤p suc n

infix 5 _≤p_

sound≤ : (m n : Nat) → m ≤p n → m ≤ n ≡ true
sound≤ .zero n (zero≤p .n) = refl true
sound≤ .(suc m) .(suc n) (suc≤p m n p) = sound≤ m n p

comp≤ : (m n : Nat) → m ≤ n ≡ true → m ≤p n
comp≤ zero zero p = zero≤p zero
comp≤ zero (suc n) p = zero≤p (suc n)
comp≤ (suc m) zero ()
comp≤ (suc m) (suc n) p = suc≤p m n (comp≤ m n p)

{- ≤p is an order -}
refl≤ : ∀ n → (n ≤p n)
refl≤ zero = zero≤p zero
refl≤ (suc m) = suc≤p m m (refl≤ m)

trans≤ : ∀ m n p → m ≤p n → n ≤p p → m ≤p p
trans≤ .zero .zero p (zero≤p .zero) (zero≤p .p) = zero≤p p
trans≤ .zero .(suc m) .(suc n) (zero≤p .(suc m)) (suc≤p m n r) = zero≤p (suc n)
trans≤ .(suc m) .(suc n) .(suc n₁) (suc≤p m n q) (suc≤p .n n₁ r) = suc≤p m n₁ (trans≤ m n n₁ q r)

antisym≤ : ∀ m n → m ≤p n → n ≤p m → m ≡ n
antisym≤ .zero .zero (zero≤p .zero) (zero≤p .zero) = refl zero
antisym≤ .(suc m) .(suc n) (suc≤p m n p) (suc≤p .n .m q) = cong-≡ suc (antisym≤ m n p q) -- with hint cong-≡

{- for Nat it is a total order -}
total≤Nat : ∀ m n → (m ≤p n) ∨ (n ≤p m)
total≤Nat zero zero = inl (zero≤p zero)
total≤Nat zero (suc n) = inl (zero≤p (suc n))
total≤Nat (suc m) zero = inr (zero≤p (suc m))
total≤Nat (suc m) (suc n) = DE (λ z → inr (suc≤p n m z))
                               (λ z → inl (suc≤p m n z))
                               (total≤Nat n m)

-- look ahead : root
data Maybe (A : Set) : Set where
  none : Maybe A
  some : A → Maybe A

-- look ahead : lifted comparison
data _≤p'_ : Maybe Nat → Maybe Nat → Set where
  some≤p'  : (m n : Nat) → m ≤p n → (some m) ≤p' (some n)
  nonel≤p' : (m : Nat) → none ≤p' (some m)
  noner≤p' : (m : Nat) → (some m) ≤p' none

mutual -- new Agda syntax, for 'induction-recursion'
  data bst : Set where
    empty : bst
    node : (n : Nat) → (l : bst) → (r : bst) → (root l ≤p' (some n)) → ((some n) ≤p' root r) → bst

  root : bst → Maybe Nat
  root empty = none
  root (node n l r _ _) = some n

{-
Is this a good definition?
  * it is a broken definition because the invariant is not strong enough
  * it may seem to define a BST but it doesn't! EG:
           2
          /\
         1  nil
        /\
     nil  3
  * Question: When would we have noticed the invariant is broken?
  * additionally, it is neither elegant or proof-efficient!
  * while proving properties we may revise or provide alternative definitions.
  * we could keep several definitions provided they are isomorphic.
-}

{--
Example tree:
 2
 /\
0  4
--}

n1 : bst
n1 = node ₀ empty empty (nonel≤p' zero) (noner≤p' zero) -- auto the proof obligations
n2 : bst
n2 = node ₄ empty empty (nonel≤p' ₄) (noner≤p' ₄)       -- proof are required cannot be _
n3 : bst
n3 = node ₂ n1 n2 (some≤p' ₀ ₂ (zero≤p ₂)) (some≤p' ₂ ₄ (suc≤p (suc zero) (suc (suc (suc zero)))
                                                           (suc≤p zero (suc (suc zero)) (zero≤p (suc (suc zero))))))

-- Insert node
insert : Nat → bst → bst
insert n empty = node n empty empty (nonel≤p' n) (noner≤p' n)
insert n (node m l r pl pr) =
  if n ≤ m then (node m (insert n l) r {!!} {!!})     -- note that proof obligations change
           else (node m l (insert n r) {!!} {!!})     -- did we use the right invariants? perhaps more general?

mutual -- Alternative definition with more general invariant
  data Bst : Set where
    Empty : Bst
    Node : (n : Nat) → (l : Bst) → (r : Bst) → n ≥a l → n ≤a r → Bst

  data _≥a_ : Nat → Bst → Set where
    Empty≥a : ∀ n → n ≥a Empty
    Node≥a  : ∀ m n l r p q → n ≥a l → n ≥a r → m ≤p n → n ≥a (Node m l r p q)

  data _≤a_ : Nat → Bst → Set where
    Empty≤a : ∀ n → n ≤a Empty
    Node≤a  : ∀ m n l r p q → n ≤a l → n ≤a r → n ≤p m → n ≤a (Node m l r p q)

-- same example redux
N1 : Bst
N1 = Node ₀ Empty Empty (Empty≥a zero) (Empty≤a zero)
N2 : Bst
N2 = Node ₄ Empty Empty (Empty≥a (suc (suc (suc (suc zero))))) (Empty≤a (suc (suc (suc (suc zero)))))
N3 = Node ₂ N1 N2 (Node≥a zero (suc (suc zero)) Empty Empty (Empty≥a zero)
                     (Empty≤a zero) (Empty≥a (suc (suc zero)))
                     (Empty≥a (suc (suc zero))) (zero≤p (suc (suc zero))))
                  (Node≤a (suc (suc (suc (suc zero)))) (suc (suc zero)) Empty Empty
                     (Empty≥a (suc (suc (suc (suc zero)))))
                     (Empty≤a (suc (suc (suc (suc zero))))) (Empty≤a (suc (suc zero)))
                     (Empty≤a (suc (suc zero)))
                     (suc≤p (suc zero) (suc (suc (suc zero)))
                     (suc≤p zero (suc (suc zero)) (zero≤p (suc (suc zero)))))) -- auto (needed!)

-- Insert node

ins : Nat → Bst → Bst
ins n Empty = Empty
ins n (Node m l r pl pr) =
  if n ≤ m then (Node m (ins n l) r p1 p2)
           else (Node m l (ins n r) p3 p4) where -- problem : the value of n ≤ m is lost!
  p1 : m ≥a ins n l
  p1 = {!!}
  p2 : m ≤a r
  p2 = {!!}
  p3 : m ≥a l
  p3 = {!!}
  p4 : m ≤a ins n r
  p4 = {!!}
