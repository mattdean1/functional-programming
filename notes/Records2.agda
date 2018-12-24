{-# OPTIONS --copatterns #-}

-- Define the property of "being an equivalence"
-- Obs: It is a property 'of a type' hence in Set₁
record Equiv (A : Set) : Set₁ where
  field
    _≈_   : A → A → Set
    refl  : ∀ a → a ≈ a
    trans : ∀ {a b c} → a ≈ b → b ≈ c → a ≈ c
    sym   : ∀ {a b} → a ≈ b → b ≈ a
  infix  5 _≈_

-- Example: 'propositional' equality is an instance of an equivalence
module PropEq where
  data _≡_ {A : Set} : A → A → Set where
    refl : (a : A) → a ≡ a

  trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
  trans (refl a) (refl .a) = refl a

  sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
  sym (refl a) = refl a
  
  -- produce the proof that A can be equipped with an equivalence (≡)
  -- remember: co-patterns
  isEquiv : {A : Set} → Equiv A
  Equiv._≈_   isEquiv = _≡_
  Equiv.refl  isEquiv = refl
  Equiv.trans isEquiv = trans
  Equiv.sym   isEquiv = sym

  -- A useful additional property:
  cong : {A B : Set} → (f : A → B) → {a₀ a₁ : A} → a₀ ≡ a₁ → f a₀ ≡ f a₁
  cong f (refl a) = refl (f a)

-- A silly ('degenerate') example of equivalence
--   (everything is equated)
module TrivEq where
  data triveq {A : Set} : A → A → Set where
    * : ∀ {a1 a2} → triveq a1 a2

  isEquiv : {A : Set} → Equiv A
  Equiv._≈_   isEquiv = triveq
  Equiv.refl  isEquiv = λ _ → *
  Equiv.trans isEquiv = λ _ _ → *
  Equiv.sym   isEquiv = λ _ → *

-- Obs:
-- Propeq is the "smallest" equivalence on A
-- TrivEq is the "largest" equivalence on A

-- A typical abstract algebraic structure 
-- Obs: More flexible if we don't define relative to ≡
record Monoid (A : Set) : Set₁ where
  field
    theEquiv : Equiv A
    -- Obs: an equivalence structure needs to be externally provided
  open Equiv theEquiv
  -- Provide access to _≈_, otherwise the syntax is clumsy
  -- The syntax for opening a record is rather annoying:
  --     to open a record r : R we write  'open R r'
  field
    _+_   : A → A → A
    zero  : A
    idl   : ∀ a → (zero + a) ≈ a
    -- Obs: Without opening the equivalence we would write
    --     idl : ∀ a → Equiv._≈_ theEquiv (zero + a) a 
    idr   : ∀ a → (a + zero) ≈ a
    assoc : ∀ a b c → ((a + b) + c) ≈ (a + (b + c))
    -- NB: Because we work with ≈ rather than ≡ we also require congruences:
    --     (generally equivalences need not be congruences)
    congl : ∀ (a : A) {b1 b2 : A} → b1 ≈ b2 → (a + b1) ≈ (a + b2)
    congr : ∀ b {a1 a2} → a1 ≈ a2 → (a1 + b) ≈ (a2 + b)

-- A Group is a Monoid with extra properties
record Group (A : Set) : Set₁ where
  field
    theMonoid : Monoid A
    -- Obs : a monoid structure needs to be provided
  open Monoid theMonoid
  open Equiv theEquiv
  field
    inv  : A → A
    invl : ∀ a → (a + (inv a)) ≈ zero
    invr : ∀ a → ((inv a) + a) ≈ zero

-- Monoid instance : (List, ++, [])
module ListMonoid where
  data List (A : Set) : Set where
    [] : List A
    _∷_ : A → List A → List A
  infixr 10 _∷_

  _++_ : {A : Set} → List A → List A → List A
  [] ++ bs = bs
  (a ∷ as) ++ bs = a ∷ (as ++ bs)

  open PropEq

  isMonoid : {A : Set} → Monoid (List A)
  Monoid.theEquiv (isMonoid {A}) = isEquiv {List A}
  Monoid._+_     isMonoid = _++_
  Monoid.zero    isMonoid = []
  Monoid.congl   isMonoid = λ as p → cong (λ bs → as ++ bs) p
  Monoid.congr   isMonoid = λ bs p → cong (λ as → as ++ bs) p
  Monoid.idl     isMonoid = refl
  Monoid.idr     isMonoid = ++-idr where
                            ++-idr : {A : Set} → (as : List A) → (as ++ []) ≡ as
                            ++-idr [] = refl []
                            ++-idr (x ∷ as) = cong (_∷_ x) (++-idr as)
  Monoid.assoc   isMonoid = ++-assoc where
                            ++-assoc : {A : Set} → (as bs cs : List A) → ((as ++ bs) ++ cs) ≡ (as ++ (bs ++ cs))
                            ++-assoc [] bs cs = refl (bs ++ cs)
                            ++-assoc (a ∷ as) bs cs = cong (_∷_ a) (++-assoc as bs cs)

-- A very powerful function
  eval : {A X : Set} → Monoid X → (A → X) → List A → X
  eval monX f []       = Monoid.zero monX
  eval monX f (a ∷ as) = Monoid._+_ monX (f a) (eval monX f as)
  -- Obs:
  -- This is "map / reduce" (a formulation of 'fold')!
  --      * function f maps over the elements of List A into X
  --      * the zero of monX is the value of the empty list
  --      * the _+_ of monX folds the resulting list
  -- This is a 'universal' function

module NatMonoids where
  data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

  _+_ : ℕ → ℕ → ℕ
  zero + n = n
  (suc m) + n = suc (m + n)

  open PropEq

  -- The typical Monoid (N, +, zero)
  plusMonoid : Monoid ℕ
  Monoid.theEquiv plusMonoid = PropEq.isEquiv {ℕ}
  Monoid._+_     plusMonoid = _+_
  Monoid.zero    plusMonoid = zero
  Monoid.congl   plusMonoid = λ m p → cong (λ n → m + n) p
  Monoid.congr   plusMonoid = λ n p → cong (λ m → m + n) p
  Monoid.idl     plusMonoid = refl
  Monoid.idr     plusMonoid = +-idr where
                              +-idr : (m : ℕ) → (m + zero) ≡ m
                              +-idr zero = refl zero
                              +-idr (suc m) = cong suc (+-idr m)
  Monoid.assoc   plusMonoid = +-assoc where
                                +-assoc : (m n p : ℕ) → ((m + n) + p) ≡ (m + (n + p))
                                +-assoc zero n p = refl (n + p)
                                +-assoc (suc m) n p = cong suc (+-assoc m n p)

  -- A different monoid (N, max, zero)
  max : ℕ → ℕ → ℕ
  max zero n = n
  max (suc m) zero = suc m
  max (suc m) (suc n) = suc (max m n)

  maxMonoid : Monoid ℕ
  Monoid.theEquiv maxMonoid = isEquiv {ℕ}
  Monoid._+_     maxMonoid = max
  Monoid.zero    maxMonoid = zero
  Monoid.congl   maxMonoid = λ m p → cong (λ n → max m n) p
  Monoid.congr   maxMonoid = λ n p → cong (λ m → max m n) p
  Monoid.idl     maxMonoid = refl
  Monoid.idr     maxMonoid = max-idr where
                             max-idr : (m : ℕ) → max m zero ≡ m
                             max-idr zero = refl zero
                             max-idr (suc m) = refl (suc m)
  Monoid.assoc   maxMonoid = max-assoc where
                             max-assoc : (m n p : ℕ) → (max (max m n) p) ≡ (max m (max n p))
                             max-assoc zero n p = refl (max n p)
                             max-assoc (suc m) zero p = refl (max (suc m) p)
                             max-assoc (suc m) (suc n) zero = refl (suc (max m n))
                             max-assoc (suc m) (suc n) (suc p) = cong suc (max-assoc m n p)


module Test where
  open ListMonoid
  open NatMonoids

  -- A new view on 'length'
  --   1. map each element to 'one'
  --   2. reduce by +
  length : {A : Set} → List A → ℕ
  length xs = eval NatMonoids.plusMonoid (λ _ → suc zero) xs

  -- the identity function
  ι : {A : Set} → A → A
  ι = λ x → x
  
  -- A new view on 'concat'
  --   1. map each element to itself
  --   2. reduce by +
  concat : {A : Set} → List (List A) → List A
  concat xs = eval ListMonoid.isMonoid ι xs

  sum : List ℕ → ℕ
  sum xs = eval NatMonoids.plusMonoid ι xs

  maximum : List ℕ → ℕ
  maximum xs = eval NatMonoids.maxMonoid ι xs

  -- Map is evaluation into another list:
  map : {A B : Set} → (A → B) → List A → List B
  map {A} {B} f xs = eval (ListMonoid.isMonoid {B}) (λ x → (f x) ∷ []) xs

  xs = (suc zero) ∷ zero ∷ zero ∷ (suc zero) ∷ []
  ys = (suc (suc zero)) ∷ (suc zero) ∷ (suc (suc (suc zero))) ∷ []
  zs = xs ∷ ys ∷ xs ∷ ys ∷ []

  test1 = length xs
  test2 = sum xs
  test3 = length ys
  test4 = sum ys
  test5 = maximum ys
  test6 = concat zs


-- 'Abstract' algebra (Nice!)
module UniqueZeroMon {A} (M : Monoid A) where
  open Monoid M
  open Equiv theEquiv
  
  p : ∀ (zero' : A) → (∀ (a : A) → (zero' + a) ≈ a) → zero' ≈ zero
  p zero' x = trans (sym p1) p2 where
    p1 : (zero' + zero) ≈ zero'
    p1 = idr zero'
    p2 : (zero' + zero) ≈ zero
    p2 = x zero 

-- Instantiating the abstract proof
module Test'' where
  open PropEq
  open ListMonoid

  unique-[] : {A : Set} → ∀ ([]' : List A) → (∀ xs → ([]' ++ xs) ≡ xs) → []' ≡ []
  unique-[] {A} []' x = p []' x where
                open UniqueZeroMon (isMonoid {A}) 

  open NatMonoids
  unique-zero+ : ∀ zero' → (∀ n → (zero' + n) ≡ n) → zero' ≡ zero
  unique-zero+ zero' x = p zero' x where
               open UniqueZeroMon plusMonoid
    
  unique-zero-max : ∀ zero' → (∀ n → (max zero' n) ≡ n) → zero' ≡ zero
  unique-zero-max zero' x = p zero' x where
               open UniqueZeroMon maxMonoid 
    
module UniqueInverseGroup {A} (G : Group A) where
  open Group G
  open Monoid theMonoid
  open Equiv theEquiv

  p : ∀ a' → ∀ a → a' + a ≈ zero → a' ≈ inv a
  p a' a x = trans p4 (trans p3 (trans p2 (trans p0 p1))) where
          p0 : (a' + a) + inv a ≈ zero + inv a
          p0 = congr (inv a) x
          p1 : zero + inv a ≈ inv a
          p1 = idl (inv a)
          p2 : a' + (a + inv a) ≈ (a' + a) + inv a
          p2 = sym (assoc a' a (inv a))
          p3 : a' + zero ≈ a' + (a + inv a)
          p3 = congl a' (sym (invl a))
          p4 : a' ≈ a' + zero
          p4 = sym (idr a') 

-- More complex properties involve a bureaucracy for name-management
-- (not so nice)
record MonoidHom (A B : Set) : Set₁ where
  constructor monoidHom
  field
    theMonoidA : Monoid A
    theMonoidB : Monoid B
  open Monoid theMonoidA
    renaming (theEquiv to theEquivA
             ; _+_ to _+A_
             ; zero to zeroA)
  open Monoid theMonoidB
    renaming (theEquiv to theEquivB
             ; _+_ to _+B_
             ; zero to zeroB)
  -- OBS: Avoid name-clashing by renaming operators in import
  open Equiv theEquivB 
  field
    f : A → B
    hom+ : ∀ (a a' : A) → (f (a +A a')) ≈ ((f a) +B (f a'))
    homz : (f zeroA) ≈ zeroB

module Test' (A : Set) where
  open ListMonoid using (_∷_ ; [] ; List)
  open Monoid (ListMonoid.isMonoid {A}) 
    renaming ( _+_ to _++_
             ; zero to nil)
             
  open Monoid NatMonoids.plusMonoid
    renaming ( congl to congl-nat
             ; congr to congr-nat
             ; assoc to assoc-nat
             ; theEquiv to equiv-nat)
  open Equiv equiv-nat

  length-is-mh : MonoidHom (ListMonoid.List A) NatMonoids.ℕ
  length-is-mh = monoidHom
    (ListMonoid.isMonoid {A})
    NatMonoids.plusMonoid
    Test.length
    Goal
    (PropEq.refl NatMonoids.zero) where
      open Test renaming (length to len) 
      Goal : (as bs : List A) →
             len (as ++ bs) ≈ (len as) + (len bs)
      Goal [] bs = PropEq.refl (len bs)
      Goal (a ∷ as) bs = goal where
        one = NatMonoids.suc zero
        IH : len (as ++ bs) ≈ (len as) + (len bs)
        IH = Goal as bs
        p0 : len ((a ∷ as) ++ bs) ≈ one + len (as ++ bs)
        p0 = PropEq.refl (NatMonoids.suc (len (as ++ bs))) 
        p1 : one + len (as ++ bs) ≈ one + ((len as) + (len bs))
        p1 = congl-nat (one) IH
        p2 : one + ((len as) + (len bs)) ≈ (one + (len as)) + (len bs)
        p2 = assoc-nat one (len as) (len bs)
        p3 : one + (len as) ≈ len (a ∷ as)
        p3 = PropEq.refl (NatMonoids.suc (len as))
        p4 : (one + (len as)) + (len bs) ≈ len (a ∷ as) + (len bs)
        p4 = congr-nat (len bs) p3 
        goal : len ((a ∷ as) ++ bs) ≈ len (a ∷ as) + len bs
        goal = trans p0 (trans p1 (trans p2 p4)) 
        -- OBS:
        -- Not implemented: The Agda synthesizer (Agsy) does not support copatterns yet

record Congruence {A B : Set} (E : Equiv A) (F : Equiv B) : Set₁ where
  open Equiv E renaming (_≈_ to _∼_)
  open Equiv F
  field
    f : A → B
    cong : ∀ a₀ a₁ → a₀ ∼ a₁ → f a₀ ≈ f a₁

module CongruenceProps where

  -- PropEq is a congruence for any function
  isCong : {A B : Set} → (A → B) → Congruence (PropEq.isEquiv {A}) (PropEq.isEquiv {B})
  Congruence.f (isCong f) = f
  Congruence.cong (isCong f) a₀ .a₀ (PropEq.refl .a₀) = PropEq.refl (f a₀)

  -- Congruences compose
  comp : {A B C : Set}{E : Equiv A}{F : Equiv B}{G : Equiv C}
       → Congruence E F → Congruence F G → Congruence E G
  Congruence.f (comp cong₀ cong₁) = λ x → g (f x) where
    f = Congruence.f cong₀
    g = Congruence.f cong₁ 
  Congruence.cong (comp {A}{B}{C}{E}{F}{G} cong₀ cong₁) a₀ a₁ x = p2 where
    open Equiv E renaming (_≈_ to _∼A_ )
    open Equiv F renaming (_≈_ to _∼B_ )
    open Equiv G renaming (_≈_ to _∼C_ )
    open Congruence cong₀
    open Congruence cong₁ renaming (f to g ; cong to cong')
    p1 : f a₀ ∼B f a₁
    p1 = cong a₀ a₁ x
    p2 : g (f a₀) ∼C g (f a₁)
    p2 = cong' (f a₀) (f a₁) p1
    
