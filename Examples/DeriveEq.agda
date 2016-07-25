module Generic.Examples.DeriveEq where

open import Generic.Core
open import Generic.Property.Eq
open import Generic.Data.Vec

open import Data.Vec as Vec hiding (Vec)

VecInj : ∀ {n α} {A : Set α} -> Vec.Vec A n ↦ Vec A n
VecInj = record { R } where
  module R where
    to : ∀ {n} -> Vec.Vec _ n -> Vec _ n
    to = Vec.foldr (Vec _) _∷ᵥ_ []ᵥ

    from : ∀ {n} -> Vec _ n -> Vec.Vec _ n
    from = elimVec (λ {n} _ -> Vec.Vec _ n) Vec._∷_ Vec.[]

    from-to : ∀ {n} -> from ∘ to ≗ id {A = Vec.Vec _ n}
    from-to  []      = refl
    from-to (x ∷ xs) = cong (x ∷_) (from-to xs)

instance
  VecEq : ∀ {n α} {A : Set α} {{aEq : Eq A}} -> Eq (Vec.Vec A n)
  VecEq = viaInj VecInj

xs : Vec.Vec ℕ 3
xs = 2 ∷ 4 ∷ 1 ∷ []

test : xs ≟ xs ≡ yes refl
test = refl
