{-# OPTIONS --no-termination #-}

open import Agda.Builtin.Nat public

record Stream (A : Set) : Set where
  coinductive
  field
    hd : A
    tl : Stream A
open Stream

cons : ∀ {A} → A → Stream A → Stream A
hd (cons a xs) = a
tl (cons a xs) = xs

repeat : ∀ {A} → A → Stream A
hd (repeat a) = a
tl (repeat a) = repeat a

-- conversion between sequences and streams

fromSeq : ∀ {A} → (Nat → A) → Stream A
hd (fromSeq f) = f 0
tl (fromSeq f) = fromSeq (λ n → f (suc n))

toSeq : ∀ {A} → Stream A → (Nat → A)
toSeq xs zero = hd xs
toSeq xs (suc n) = toSeq (tl xs) n

-- conversion to lists

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A
infixr 10 _∷_

take : Nat → ∀ {A} → Stream A → List A
take zero xs = []
take (suc n) xs = (hd xs) ∷ (take n (tl xs))

-- more basic stream processing

mapS : ∀ {A B} → (A → B) → (Stream A → Stream B)
hd (mapS f xs) = f (hd xs)
tl (mapS f xs) = mapS f (tl xs)

{- compare this with... -}
mapL : ∀ {A B} → (A → B) → (List A → List B)
mapL f [] = []
mapL f (x ∷ xs) = f x ∷ mapL f xs

zipWithS : ∀ {A B C} → (A → B → C) → Stream A → Stream B → Stream C
hd (zipWithS f xs ys) = f (hd xs) (hd ys)
tl (zipWithS f xs ys) = zipWithS f (tl xs) (tl ys)

{- compare this with... -}
zipWithL : ∀ {A B C} → (A → B → C) → List A → List B → List C
zipWithL f [] ys = []
zipWithL f (x ∷ xs) [] = []
zipWithL f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWithL f xs ys

-- some streams of natural numbers

upFrom : Nat → Stream Nat
hd (upFrom n) = n
tl (upFrom n) = upFrom (suc n)

nats = upFrom 0
evens = zipWithS _*_ (repeat 2) nats
odds = zipWithS _+_ (repeat 1) evens

cycleDown : Nat → Nat → Stream Nat
hd (cycleDown n k) = k
tl (cycleDown n 0) = cycleDown n n
tl (cycleDown n (suc k)) = cycleDown n k

-- bad : Stream Nat
-- hd bad = 0
-- hd (tl bad) = 1
-- tl (tl bad) = tl (tl bad)

fib : Stream Nat
hd fib = 0
hd (tl fib) = 1
tl (tl fib) = zipWithS _+_ fib (tl fib)

trib : Stream Nat
hd trib = 0
hd (tl trib) = 1
hd (tl (tl trib)) = 2
tl (tl (tl trib)) = zipWithS _+_ (zipWithS _+_ trib (tl trib)) (tl (tl trib))

-- collect all iterated applications of a function to a value

iterate : ∀ {A} (f : A → A) (a : A) → Stream A
hd (iterate f a) = a
tl (iterate f a) = mapS f (iterate f a)

mystery-stream1 = iterate (_*_ 2) 1
mystery-stream2 = iterate (_+_ 1) 0

-- more stream processing

buffer : ∀ {A} → List A → Stream A → Stream A
buffer [] ys = ys
buffer (x ∷ xs) ys = cons x (buffer xs ys)

merge : ∀ {A} → Stream A → Stream A → Stream A
hd (merge xs ys) = hd xs
hd (tl (merge xs ys)) = hd ys
tl (tl (merge xs ys)) = merge (tl xs) (tl ys)

compress : ∀ {A} → (A → A → A) → Stream A → Stream A
hd (compress f xs) = f (hd xs) (hd (tl xs))
tl (compress f xs) = compress f (tl (tl xs))

nats' = merge evens odds

evens' = compress (λ x y → x) nats
odds' = compress (λ x y → y) nats

-- stream filtering

data Bool : Set where
  true : Bool
  false : Bool

if_then_else_ : Bool → {A : Set} → A → A → A
if true then e₁ else e₂ = e₁
if false then e₁ else e₂ = e₂

mutual
  isEven : Nat → Bool
  isEven 0 = true
  isEven (suc n) = isOdd n

  isOdd : Nat → Bool
  isOdd 0 = false
  isOdd (suc n) = isEven n

filterL : ∀ {A} → (A → Bool) → List A → List A
filterL f [] = []
filterL f (x ∷ xs) = if f x then x ∷ filterL f xs
                     else filterL f xs

filterS : ∀ {A} → (A → Bool) → Stream A → Stream A
hd (filterS f xs) = if f (hd xs) then hd xs
                    else hd (filterS f (tl xs))
tl (filterS f xs) = if f (hd xs) then filterS f (tl xs)
                    else tl (filterS f (tl xs))

-- reasoning about equality

data _≡_ {X : Set} : X → X → Set where
 refl : (x : X) → x ≡ x

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym (refl x) = refl x

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans (refl x) p = p

cong : ∀ {A B} (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f (refl x) = refl (f x)

record _≈_ {A : Set} (xs ys : Stream A) : Set where
  coinductive
  field
    hd-eq : hd xs ≡ hd ys
    tl-eq : tl xs ≈ tl ys
open _≈_

refl≈ : ∀ {A} (xs : Stream A) → xs ≈ xs
hd-eq (refl≈ xs) = refl (hd xs)
tl-eq (refl≈ xs) = refl≈ (tl xs)

trans≈ : ∀ {A} {xs ys zs : Stream A} → xs ≈ ys → ys ≈ zs → xs ≈ zs
hd-eq (trans≈ p q) = trans (hd-eq p) (hd-eq q)
tl-eq (trans≈ p q) = trans≈ (tl-eq p) (tl-eq q)

prop1 : ∀ {A} (xs : Stream A) → xs ≈ cons (hd xs) (tl xs)
hd-eq (prop1 xs) = refl (hd xs)
tl-eq (prop1 xs) = refl≈ (tl xs)

prop2 : cycleDown 2 2 ≈ buffer (2 ∷ 1 ∷ 0 ∷ []) (cycleDown 2 2)
hd-eq prop2 = refl 2
hd-eq (tl-eq prop2) = refl 1
hd-eq (tl-eq (tl-eq prop2)) = refl 0
tl-eq (tl-eq (tl-eq prop2)) = refl≈ (cycleDown 2 2)

prop3 : zipWithS _+_ (cycleDown 1 1) (cycleDown 1 0) ≈ repeat 1
hd-eq prop3 = refl 1
hd-eq (tl-eq prop3) = refl 1
tl-eq (tl-eq prop3) = prop3

prop4 : fib ≈ buffer (0 ∷ 1 ∷ []) (zipWithS _+_ fib (tl fib))
hd-eq prop4 = refl 0
hd-eq (tl-eq prop4) = refl 1
tl-eq (tl-eq prop4) = refl≈ (zipWithS _+_ fib (tl fib))

prop5 : ∀ {A} (xs : Stream A) → xs ≈ fromSeq (toSeq xs)
hd-eq (prop5 xs) = refl (hd xs)
tl-eq (prop5 xs) = prop5 (tl xs)

prop6 : ∀ {A B C} (f : A → B → C) (x : A) (ys : Stream B) → mapS (f x) ys ≈ zipWithS f (repeat x) ys
hd-eq (prop6 f x ys) = refl (f x (hd ys))
tl-eq (prop6 f x ys) = prop6 f x (tl ys)

prop7 : ∀ {A} (xs : Stream A) → xs ≈ merge (compress (λ x y → x) xs) (compress (λ x y → y) xs)
hd-eq (prop7 xs) = refl (hd xs)
hd-eq (tl-eq (prop7 xs)) = refl (hd (tl xs))
tl-eq (tl-eq (prop7 xs)) = prop7 (tl (tl xs))

prop8 : ∀ n → upFrom n ≈ iterate (_+_ 1) n
hd-eq (prop8 n) = refl n
tl-eq (prop8 n) = trans≈ (lemma n) (cong≈ (_+_ 1) (prop8 n))
  where
    lemma : ∀ n → upFrom (suc n) ≈ mapS (_+_ 1) (upFrom n)
    hd-eq (lemma n) = refl (suc n)
    tl-eq (lemma n) = lemma (suc n)
    cong≈ : ∀ {A B} (f : A → B) {xs ys : Stream A} → xs ≈ ys → mapS f xs ≈ mapS f ys
    hd-eq (cong≈ f p) = cong f (hd-eq p)
    tl-eq (cong≈ f p) = cong≈ f (tl-eq p)

-- Since the no-termination flag is set, it's not a bad idea to "test" our proofs
-- to ensure that they are really proofs! Proofs of stream equalities should be
-- productive in the same sense that well-defined streams are, that is, they should
-- produce an output equality when observed by any finite sequence of hd-eq's or tl-eq's.
-- Here are a few tests (which all pass):

test-prop2 : hd-eq (tl-eq (tl-eq (tl-eq (tl-eq (tl-eq (tl-eq prop2)))))) ≡ refl 2
test-prop2 = refl (refl 2)

test-prop6 : hd-eq (tl-eq (tl-eq (prop6 _*_ 2 nats))) ≡ refl 4
test-prop6 = refl (refl 4)

test-prop8 : hd-eq (tl-eq (tl-eq (tl-eq (prop8 3)))) ≡ refl 6
test-prop8 = refl (refl 6)
