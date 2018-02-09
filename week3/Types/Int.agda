module Types.Int where

open import Types.Nat

data Int : Set where
  pos : Nat → Int
  neg : Nat → Int -- neg n = -(n+1)

{-
  We must have a 1 to 1 mapping between Nat and Int
    so 0 ∈ Nat => 0, -1 ∈ Int
       1 ∈ Nat => 1, -2 ∈ Int

  If we instead defined neg n = -n we would have two constructors for 0 ∈ Int
-}

negate : Int → Int
negate (pos zero) = pos zero
negate (pos (succ n)) = neg n
negate (neg n) = pos (succ n)

_-_ : Nat → Nat → Int
zero - zero = pos zero
zero - succ y = neg y
succ x - zero = pos (succ x)
succ x - succ y = x - y

-- Define addition and subtraction for integers.
_+ᵢ_ : Int → Int → Int
pos x +ᵢ pos y = pos (x + y)
neg x +ᵢ neg y = neg (x + y + (succ zero))
pos x +ᵢ neg y = x - succ y
neg x +ᵢ pos y = y - succ x

_-ᵢ_ : Int → Int → Int
x -ᵢ y = x +ᵢ negate y
