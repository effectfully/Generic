module Generic.Examples.DeriveEq where

open import Generic.Core
open import Generic.Property.Eq
open import Generic.Data.Vec

open import Data.Vec as StdVec renaming (Vec to StdVec)

VecInj : ∀ {n α} {A : Set α} -> StdVec A n ↦ Vec A n
VecInj {A = A} = record { R } where
  module R where
    to : ∀ {n} -> StdVec A n -> Vec A n
    to = StdVec.foldr (Vec _) _∷ᵥ_ []ᵥ

    from : ∀ {n} -> Vec A n -> StdVec A n
    from = elimVec (λ {n} _ -> StdVec A n) _∷_ []

    from-to : ∀ {n} -> from ∘ to ≗ id {A = StdVec A n}
    from-to  []      = refl
    from-to (x ∷ xs) = cong (x ∷_) (from-to xs)

module _ where
  private open module Dummy {n α A} = _↦_ (VecInj {n} {α} {A})

  elimStdVec : ∀ {n α π} {A : Set α}
             -> (P : ∀ {n} -> StdVec A n -> Set π)
             -> (∀ {n} {xs : StdVec A n} x -> P xs -> P (x ∷ xs))
             -> P []
             -> (xs : StdVec A n)
             -> P xs
  elimStdVec P f z xs = subst P (from-to xs) $ elimVec (P ∘ from) f z (to xs)

instance
  VecEq : ∀ {n α} {A : Set α} {{aEq : Eq A}} -> Eq (StdVec A n)
  VecEq = viaInj VecInj

xs : StdVec ℕ 3
xs = 2 ∷ 4 ∷ 1 ∷ []

test : xs ≟ xs ≡ yes refl
test = refl
