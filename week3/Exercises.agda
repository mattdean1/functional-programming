module Exercises where

{-
  1. Show that (Nat, +, 0) is a commutative monoid.

      import Types.Nat
      import Properties.Nat.Addition

      The type signature of addition proves closure
      identity        +-unitl and +-unitr
      associativity   +-assoc
      commutativity   +-comm


  2. Show that (Int, +ᵢ, 0, negate) forms an abelian group.

      import Types.Int
      import Properties.Int

      Group axioms:
        Closure
          ∀ (a b ∈ G), (a∘b) ∈ G
          Satisfied by the type signature of +ᵢ - _+ᵢ_ : Int → Int → Int

        Associativity
          ∀ (a b c ∈ G), (a ∘ b) ∘ c ≡ a ∘ (b ∘ c)
          z+-assoc

        Identity
          ∃ i ∈ G, ∀ a ∈ G, a ∘ i ≡ i ∘ a ≡ a
          z+-id1 and z+-id2

        Inverse
          ∀ a ∈ G, ∃ a⁻¹ ∈ G, a ∘ a⁻¹ ≡ a⁻¹ ∘ a ≡ i where i is the identity element
          z+-inv1 and z+-inv2

      An Abelian group is also commutative:
        ∀ (a b ∈ G), a ∘ b ≡ b ∘ a
        z+-comm


  3. Show that (Nat, +, 0, *, 1) forms a semi-ring

      import Properties.Nat.Multiplication

      (Nat, +, 0) is a commutative monoid
          See above

      (Nat, *, 1) is a monoid
          Closure from the type signature of *
          identity        *-unitl and *-unitr
          associativity   *-assoc

      Multiplication distributes left and right over addition
          *-distl and *-distr

      The first identity annihilates with the second operation
          *-zerol and *-zeror
-}
