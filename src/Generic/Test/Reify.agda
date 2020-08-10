module Generic.Test.Reify where

open import Generic.Core
open import Generic.Property.Reify
open import Generic.Test.Data.Fin
open import Generic.Test.Data.Vec

open import Data.Fin renaming (Fin to StdFin)
open import Data.Vec renaming (Vec to StdVec)

xs : Vec (Fin 4) 3
xs = fsuc (fsuc (fsuc fzero)) ∷ᵥ fzero ∷ᵥ fsuc fzero ∷ᵥ []ᵥ

xs′ : StdVec (StdFin 4) 3
xs′ = suc (suc (suc zero)) ∷ zero ∷ (suc zero) ∷ []

test : reflect xs ≡ xs′
test = refl
