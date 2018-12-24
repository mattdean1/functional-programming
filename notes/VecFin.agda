module VecFin where

open import AFP
open import Ex


{-
  The Hierarchy of Safety
  =======================

  * no safety / random code may execute (asm, C)
  * minimal safety / program may crash (Java)
  * partial safety / program may diverge (Haskell, OCaml) (†)
  * total safety / program will produce a value (Agda)

  --
  (†) It's a lie.
-}

{- 
  Certain errors such as 
    * array out of bounds (index)
    * empty list (hd / tl)
   are very annoying because
     * they make functional languages unsafe
     * dealing with them properly is complicated
     * dealing with them properly is inefficient

  The "hello world" of DDD is the "vector" type
-}

data Vec (A : Set) : Nat → Set where
  vnil : Vec A zero
  _::_ : {n : Nat} → A → Vec A n → Vec A (suc n)

infixr 6 _::_

exvec : Vec Nat ₄
exvec = ₀ :: ₁ :: ₂ :: ₃ :: vnil

-- Typical application : avoiding out-of-bounds errors
_⊙_ : {n : Nat} → Vec Nat n → Vec Nat n → Nat
vnil ⊙ vnil = zero
(x :: xs) ⊙ (y :: ys) = x * y + (xs ⊙ ys)

ex⊙ : Nat
ex⊙ = exvec ⊙ exvec
-- ex⊙ = suc( suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))

{-
NOTE: We could implement indexed access:

_▹_ : {A : Set}{n : Nat} → Vect A n → (m : Nat) → m ≤p n → A
Exercise!

Question: but there is a (better? / nicer? / fancier?) (equivalent) way.
-}

-- The type of "numbers less than the Nat n"
data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

exfin : Fin ₄
exfin = fsuc fzero

{- Typical application : a safe look-up -}

_▹_ : {A : Set} {n : Nat} → Vec A n → Fin n → A
vnil ▹ ()
(x :: xs) ▹ fzero  = x
(x :: xs) ▹ fsuc m = xs ▹ m

{-
Obs on Fin n:
 NB : these are not Nats
      there are NO "subsets" / "subtypes" in DTT
      this can be a pain in the neck
      zero vs fzero : incomparable b/c different types!
-}

{- We need to redefine addition, etc:

Interactive:
-}

-- We can increase the boundary if necessary (for addition)
incFin : (m m' : Nat) → m ≤p m' → (n : Fin m) → Fin m'  
incFin .zero m' (zero≤p .m') ()
incFin .(suc m) .(suc n) (suc≤p m n p) fzero = fzero
incFin .(suc m) .(suc m') (suc≤p m m' p) (fsuc n) = fsuc IH where
  IH : Fin m'
  IH = incFin m m' p n

_+'_ : {m n : Nat} → (p : Fin m) → (q : Fin n) → Fin (m + n)
_+'_ {m} {n} (fzero {r}) q = incFin n (suc (r + n)) {!!} q
fsuc p₁ +' q = {!!}
-- The rest is an exercise FUN!

{-
 A new data-type is a bit like starting from scratch. Ugh.
 Can we reuse Nat infrastructure?
-}

ofNat : (n : Nat) → Fin (suc n)
ofNat zero    = fzero
ofNat (suc n) = fsuc (ofNat n)

ofFin : (m n : Nat) → Fin m → m ≡ suc n → Nat
ofFin _ _ fzero _ = zero
ofFin .(suc n) n q (refl .(suc n)) = n 

-- How do we know we got the right mappings? 
-- Exercise: Consider whether ofNat / ofFin form some kind of iso?
-- Question : How do we know incFin is 'right' ? 



{- We will end up wanting to say stuff such as
   ∀m:Nat.∀n:Fin m. m ≤ n
   ... but we can't because the types don't match!
   How do we say it? 
-}

monot≤p : ∀ m → m ≤p suc m
monot≤p = {!!} 

≤Fin : (m : Nat) → (n : Fin m) → (ofFin (suc m) m (incFin m (suc m) (monot≤p m) n) (refl (suc m))) ≤p m
≤Fin zero ()
≤Fin (suc m) fzero = {!!} where
  Goal : ofFin ₂ ₁
        (incFin ₁ ₂ (monot≤p ₁) fzero)
        (refl ₂)
        ≤p suc m
  Goal = {!!} 
≤Fin (suc m) (fsuc n) = {!!}


-- Idea : 'phase distinction'
--         separate index types from term types
--         connect them using singleton types

data Singleton (A : Set) : (x : A) → Set where
  it : (x : A) → Singleton A x

get : {A : Set}{x : A} → Singleton A x → A 
get (it x) = x

ex-sing-nat : Singleton Nat ₁
ex-sing-nat = it ₁

ex-sing-list : Singleton (List Nat) (₁ ∷ ₂ ∷ nil)
ex-sing-list = it (₁ ∷ ₂ ∷ nil)


len : {A : Set} {n : Nat} → Vec A n → Singleton Nat n
len {n = zero} vnil = it zero
len {n = suc n} (_ :: v) = it (suc n) where
  n' : Singleton Nat n
  n' = len v

nth : {A : Set} {n i : Nat} → i < n → Vec A n → Singleton Nat i → A
nth (zero< n) (x :: _) (it .zero) = x
nth (suc< m n p) (x :: v) (it .(suc m)) = nth p v (it m) 

-- More complex functions [back to Agda]

rev' : {A : Set}{m n : Nat} → Vec A m → Vec A n → Vec A (m + n)
rev' vnil v2 = v2
rev' {A = A} {m = m}{n = n}(_::_ {p} x v1) v2 = transport p n result where
  result : Vec A (p + suc n)
  result = rev' v1 (x :: v2)
  lem : ∀ p n → p + suc n ≡ suc (p + n)
  lem zero n₁ = refl (suc n₁)
  lem (suc p₁) n₁ = cong≡ suc (lem p₁ n₁)
  transport : ∀ p n → Vec A (p + suc n) → Vec A (suc (p + n))
  transport p n v = cong≡' (Vec A) (lem p n) v 

rev : {A : Set}{n : Nat} → Vec A n → Vec A n
rev {A} {n} v = transport n result where
  result : Vec A (n + zero) 
  result = rev' v vnil
  transport : ∀ n → Vec A (n + zero) → Vec A n
  transport n v = cong≡' (λ z → Vec A z) (unitr+ n) v

filter : {A : Set}{m : Nat} → (A → Bool) → Vec A m → ∃[ n ∶ Nat ] ((n ≤p m) × Vec A n)
filter f vnil = zero , ((zero≤p zero) , vnil)
filter {A}{suc n}f (x :: v) with f x
filter {A}{suc n} f (x :: v) | true = suc z , (suc≤p z n (fst RRp) , res) where
  RR : Σ Nat (λ z → z ≤p n × Vec A z)
  RR = filter f v
  z : Nat
  z = witness RR
  RRp : z ≤p n × Vec A z
  RRp = proof RR
  res : Vec A (suc z)
  res = x :: (snd RRp)

filter {A}{suc n} f (x :: v) | false = (witness RR) , (Goal , res) where
  RR : Σ Nat (λ z → z ≤p n × Vec A z)
  RR = filter f v
  z : Nat
  z = witness RR
  RRp : z ≤p n × Vec A z
  RRp = proof RR
  res : Vec A z
  res = snd RRp
  Goal : witness RR ≤p suc n
  Goal = trans≤ (witness RR) n (suc n) (fst RRp) (monot≤ n) 


ex-filter : ∃[ n ∶ Nat ] ((n ≤p ₄) × Vec Bool n)
ex-filter = filter (λ x → x) (true :: false :: true :: false :: vnil)

-- ₁ ,
-- suc≤p (suc zero) (suc (suc (suc zero))) (suc≤p zero (suc (suc zero)) (zero≤p (suc (suc zero)))) ,
-- true :: true :: vnil

-- Exercise : Try to formalise insert-sort
--            It is a big project, no need to finish
--            Concentrate on the interesting / important proofs
--            Assume auxiliary results (e.g. properties of Nats are proved elsewhere)
