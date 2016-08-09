-- You need the development version of Agda (15.06.2016) or Agda 2.5.1.1 in order to type check this.

module Generic.Examples.Eq where

open import Generic.Main hiding (List; []; _∷_)
open import Generic.Examples.Data.Fin
open import Generic.Examples.Data.List
open import Generic.Examples.Data.Vec

xs : Vec (List (Fin 4)) 3
xs = (fsuc fzero ∷ fzero ∷ [])
   ∷ᵥ (fsuc (fsuc fzero) ∷ [])
   ∷ᵥ (fzero ∷ fsuc (fsuc (fsuc fzero)) ∷ [])
   ∷ᵥ []ᵥ

test : xs ≟ xs ≡ yes refl
test = refl
