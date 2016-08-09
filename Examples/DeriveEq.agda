module Generic.Examples.DeriveEq where

open import Generic.Main
open import Generic.Function.Elim

open import Data.Vec using (Vec) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)

module DeriveEqStar where
  open import Relation.Binary
  open import Data.Star

  instance StarEq : ∀ {i t} {I : Set i} {T : Rel I t} {i j}
                      {{iEq : Eq I}} {{tEq : ∀ {i j} -> Eq (T i j)}} -> Eq (Star T i j)
  unquoteDef StarEq = deriveEqTo StarEq (quote Star)

module DeriveEqVec where
  instance VecEq : ∀ {n α} {A : Set α} {{aEq : Eq A}} -> Eq (Vec A n)
  unquoteDef VecEq = deriveEqTo VecEq (quote Vec)

  xs : Vec ℕ 3
  xs = 2 ∷ᵥ 4 ∷ᵥ 1 ∷ᵥ []ᵥ

  test₁ : xs ≟ xs ≡ yes refl
  test₁ = refl

  test₂ : xs ≟ (2 ∷ᵥ 4 ∷ᵥ 2 ∷ᵥ []ᵥ) ≡ no _
  test₂ = refl

module DeriveEqD where
  data D {α β} (A : Set α) (B : A -> Set β) : ∀ {n x} -> Vec (B x) n -> ℕ -> Set (α ⊔ β) where
    c₁ : ∀ {x n} (ys : Vec (B x) n) m -> A -> D A B ys m
    c₂ : ∀ {x n m y} {ys zs : Vec (B x) n}
       -> D A B (y ∷ᵥ ys) 0 -> Vec A m -> D A B ys (suc n) -> D A B zs n

  -- `VecEq` is in scope.
  instance DEq : ∀ {α β} {A : Set α} {B : A -> Set β} {n m x} {ys : Vec (B x) n}
                   {{aEq : Eq A}} {{bEq : ∀ {x} -> Eq (B x)}} -> Eq (D A B ys m)
  unquoteDef DEq = deriveEqTo DEq (quote D)
