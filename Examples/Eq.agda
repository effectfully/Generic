-- You need the development version of Agda (15.06.2016) or Agda 2.5.1.1 in order to type check this.

module Generic.Examples.Eq where

open import Generic.Core
open import Generic.Property.Eq
open import Generic.Data.Fin
open import Generic.Data.List
open import Generic.Data.Vec

xs : Vec (List (Fin 4)) 3
xs = (fsuc fzero ∷ₗ fzero ∷ₗ []ₗ)
   ∷ᵥ (fsuc (fsuc fzero) ∷ₗ []ₗ)
   ∷ᵥ (fzero ∷ₗ fsuc (fsuc (fsuc fzero)) ∷ₗ []ₗ)
   ∷ᵥ []ᵥ

test : xs ≟ xs ≡ yes refl
test = refl
