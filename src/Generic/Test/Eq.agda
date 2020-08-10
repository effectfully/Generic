module Generic.Test.Eq where

open import Generic.Main hiding (List; []; _∷_)
open import Generic.Test.Data.Fin
open import Generic.Test.Data.List
open import Generic.Test.Data.Vec

xs : Vec (List (Fin 4)) 3
xs = (fsuc fzero ∷ fzero ∷ [])
   ∷ᵥ (fsuc (fsuc fzero) ∷ [])
   ∷ᵥ (fzero ∷ fsuc (fsuc (fsuc fzero)) ∷ [])
   ∷ᵥ []ᵥ

test : xs ≟ xs ≡ yes refl
test = refl
