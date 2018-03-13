module Exists where

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → (b : B a) → Σ A B

syntax Σ A (λ y → B) = ∃[ y ∶ A ] B

witness : {A : Set}{B : A → Set} → ∃[ x ∶ A ] (B x) → A
witness (x , y) = x

proof : {A : Set}{B : A → Set} → (p : ∃[ x ∶ A ] (B x)) → (B (witness p))
proof (x , y) = y
