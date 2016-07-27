module Generic.Examples.DeriveEq where

open import Generic.Main
open import Generic.Property.Eq
open import Generic.Function.Elim

open import Data.Vec as Vec

Vec′ : ∀ {α} -> Set α -> ℕ -> Set α
Vec′ = readData Vec

VecInj : ∀ {n α} {A : Set α} -> Vec A n ↦ Vec′ A n
VecInj {A = A} = record { R } where
  module R where
    to : ∀ {n} -> Vec A n -> Vec′ A n
    to = Vec.foldr (Vec′ _) (readCons Vec._∷_) (readCons Vec.[])

    from : ∀ {n} -> Vec′ A n -> Vec A n
    from xs = uncoerce xs

    from-to : ∀ {n} -> from ∘ to ≗ id {A = Vec A n}
    from-to  []      = refl
    from-to (x ∷ xs) = cong (_ ∷_) (from-to xs)

instance
  VecEq : ∀ {n α} {A : Set α} {{aEq : Eq A}} -> Eq (Vec A n)
  VecEq = viaInj VecInj

xs : Vec ℕ 3
xs = 2 ∷ 4 ∷ 1 ∷ []

test : xs ≟ xs ≡ yes refl
test = refl

module _ where
  private open module Dummy {n α A} = _↦_ (VecInj {n} {α} {A})

  elimVec : ∀ {n α π} {A : Set α}
          -> (P : ∀ {n} -> Vec A n -> Set π)
          -> (∀ {n} {xs : Vec A n} x -> P xs -> P (x ∷ xs))
          -> P []
          -> (xs : Vec A n)
          -> P xs
  elimVec P f z xs = subst P (from-to xs)
                   $ elim (P ∘ from) (lift z , λ x r -> lift (f x r)) (to xs)
