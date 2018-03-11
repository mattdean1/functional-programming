module Types.Reasoning where

open import Types.Equality


begin_ : {A : Set} {x y : A} → x ≡ y → x ≡ y
begin x≡y = x≡y

_≡⟨_⟩_ : {A : Set} (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = ≡-trans x≡y y≡z

_∎ : {A : Set} → (x : A) → x ≡ x
x ∎ = refl x


infix  3 _∎
infixr 2 _≡⟨_⟩_
infix  1 begin_
