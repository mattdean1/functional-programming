open import Agda.Builtin.Nat public
open import Agda.Builtin.Size public

record Stream (A : Set) (i : Size) : Set where
  coinductive
  field
    hd : A
    tl : {j : Size< i} → Stream A j
open Stream

cons : ∀ {A i} → A → Stream A i → Stream A (↑ i)
hd (cons a xs) = a
tl (cons a xs) = xs

repeat : {A : Set} → A → ∀ {i} → Stream A i
hd (repeat a) = a
tl (repeat a) = repeat a

twos : Stream Nat ω
twos = repeat 2

-- conversion between sequences and streams

fromSeq : ∀ {A} → (Nat → A) → ∀ {i} → Stream A i
hd (fromSeq f) = f 0
tl (fromSeq f) = fromSeq (λ n → f (suc n))

toSeq : ∀ {A} → (∀ {i} → Stream A i) → (Nat → A)
toSeq xs zero = hd xs
toSeq xs (suc n) = toSeq (tl xs) n

-- conversion to lists

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A
infixr 10 _∷_

take : Nat → {A : Set} → (∀ {i} → Stream A i) → List A
take zero xs = []
take (suc n) xs = (hd xs) ∷ (take n (tl xs))

-- more basic stream processing

mapS : ∀ {A B i} → (A → B) → (Stream A i → Stream B i)
hd (mapS f xs) = f (hd xs)
tl (mapS f xs) = mapS f (tl xs)

zipWithS : {A B C : Set} {i : Size} → (A → B → C) → Stream A i → Stream B i → Stream C i
hd (zipWithS f xs ys) = f (hd xs) (hd ys)
tl (zipWithS f xs ys) = zipWithS f (tl xs) (tl ys)

-- some streams of natural numbers

upFrom : Nat → ∀ {i} → Stream Nat i
hd (upFrom n) = n
tl (upFrom n) = upFrom (suc n)

nats : Stream Nat ω
nats = upFrom 0
evens = zipWithS _*_ (upFrom 0) (repeat 2)
odds = zipWithS _+_ evens (repeat 1)

cycleDown : Nat → Nat → ∀ {i} → Stream Nat i
hd (cycleDown n k) = k
tl (cycleDown n 0) = cycleDown n n
tl (cycleDown n (suc k)) = cycleDown n k

fib : ∀ {i} → Stream Nat i
hd fib = 0
hd (tl fib) = 1
tl (tl fib) = zipWithS _+_ fib (tl fib)

trib : ∀ {i} → Stream Nat i
hd trib = 0
hd (tl trib) = 1
hd (tl (tl trib)) = 2
tl (tl (tl trib)) = zipWithS _+_ (zipWithS _+_ trib (tl trib)) (tl (tl trib))

-- collect all iterated applications of a function to a value

iterate : ∀ {A i} (f : A → A) (a : A) → Stream A i
hd (iterate f a) = a
tl (iterate f a) = mapS f (iterate f a)

mystery-stream1 = iterate (_*_ 2) 1
mystery-stream2 = iterate (_+_ 1) 0

-- more stream processing

buffer : ∀ {A i} → List A → Stream A i → Stream A i
buffer [] ys = ys
buffer (x ∷ xs) ys = cons x (buffer xs ys)

merge : ∀ {A i} → Stream A i → Stream A i → Stream A i
hd (merge xs ys) = hd xs
hd (tl (merge xs ys)) = hd ys
tl (tl (merge xs ys)) = merge (tl xs) (tl ys)

{-
compress : ∀ {A i} → (A → A → A) → Stream A ? → Stream A ?
-- What should go in the holes?
-- Since compress consumes two elements of input for every element of output,
-- we would like to write something like
--   compress : ∀ {A i} → (A → A → A) → Stream A (2 * i) → Stream A i
-- or 
--   compress : ∀ {A i} → (A → A → A) → Stream A i → Stream A (i / 2)
-- though unfortunately this can't be expressed using Size types (AFAIK).
hd (compress f xs) = f (hd xs) (hd (tl xs))
tl (compress f xs) = compress f (tl (tl xs))
-}

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

{-
filterS : ∀ {A i} → (A → Bool) → Stream A {!!} → Stream A {!!}
-- As with "compress" above, it is not clear how to fill in the size
-- parameters to please the termination checker. Here, though, the
-- situation is actually much worse: we may need to consume
-- arbitrarily many elements of input to produce an element of output,
-- and we may never even find one! Intuitively, for "filterS f xs" to
-- be a valid stream we need to know that the predicate f holds for
-- infinitely many xs, but that is not expressed in the type.
hd (filterS f xs) = if f (hd xs) then hd xs
                    else hd (filterS f (tl xs))
tl (filterS f xs) = if f (hd xs) then filterS f (tl xs)
                    else tl (filterS f (tl xs))
-}
