module Types.Inspect where

open import Types.Equality

data Unit : Set where
  unit : Unit

Suspend : Set → Set
Suspend A = Unit → A

-- suspend a (dependent) function application by wrapping it in a lambda
suspend : {A : Set} {B : A → Set} (f : (x : A) → B x) (x : A) → Suspend (B x)
suspend f x = λ { unit → f x }
  {- weird syntax here for the lambda since
     it's clearer than `suspend f x unit = f x`
     and agda's unification algorithm doesn't deal well with λ _ → f x
  -}

-- pass an element of the unit type to a suspended computation to 'unwrap' it
force : {A : Set} → Suspend A → A
force f = f unit

-- equivalence type for suspended computations and their result
data _≈_ {A : Set} (x : Suspend A) (y : A) : Set where
  s_equiv : (force x) ≡ y → x ≈ y

-- take a look at the result of the suspended computation
inspect : {A : Set} (x : Suspend A) → x ≈ (force x)
inspect f = s_equiv (refl (f unit))


-- Usage
-- Note that you must pattern match with both (f x) and (inspect (suspend f x)) for agda to resolve things properly
foo : {A B : Set} (f : A → B) (x : A) → B
foo f x with f x | inspect (suspend f x)
foo f x | result | s_equiv p = result where
    p0 : f x ≡ result
    p0 = p
