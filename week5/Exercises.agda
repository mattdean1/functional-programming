{-
Evenness
  - implement a function that tests (returns boolean) if a Nat is even, returning true if it is and false if it is not.
  - define a data-type of proof terms for evenness.
  - prove that the two definitions above are equivalent (soundness and completeness).
  - prove that a Nat n if even if and only if there exists a unique Nat m such that n = m + m
Product
  Assuming that two functions f, g are equal f≡g, by definition, if and only if ∀ x, f(x)≡g(x)
  Formulate in Agda and prove the following property:
  For any functions f : X → A, f' : X → A', there exists a unique function  g ∶ X → A × A'
    such that f ≡ π₁∘g and f' ≡ π₂ ∘ g
    where -∘- is function compositions and π₁, π₂ are the projection functions from A × A'.
-}
