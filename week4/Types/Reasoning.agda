module Types.Reasoning where

open import Types.Equality

open import Types.Nat
open import Types.Order


begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
begin x≡y = x≡y

_≡⟨_⟩_ : {A : Set} (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = ≡-trans x≡y y≡z

_∎ : {A : Set} → (x : A) → x ≡ x
x ∎ = refl x

infix  3 _∎
infixr 2 _≡⟨_⟩_
infix  1 begin_



<=begin_ : {x y : Nat} → x <=p y → x <=p y
<=begin x<=y = x<=y

_<=⟨_⟩_ : (x {y z} : Nat) → x <=p y → y <=p z → x <=p z
x <=⟨ x<=y ⟩ y<=z = <=-trans' x<=y y<=z
--
_<=∎ : (x : Nat) → x <=p x
x <=∎ = ≡-><=p (refl x)

infix  3 _<=∎
infixr 2 _<=⟨_⟩_
infix  1 <=begin_
