module Types.Equality where

data _≡_ {A : Set} : A → A → Set where
  refl : (x : A) → x ≡ x
infix 0 _≡_

≡-cong : {A : Set} {a b : A} → (f : A → A) → a ≡ b → (f a) ≡ (f b)
≡-cong f (refl a) = refl (f a)

≡-trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
≡-trans (refl a) (refl b) = refl b

≡-sym : {A : Set} {a b : A} → a ≡ b → b ≡ a
≡-sym (refl a) = refl a
