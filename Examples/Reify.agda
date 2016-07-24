module Generic.Examples.Reify where

open import Generic.Core
open import Generic.Property.Reify
open import Generic.Data.Fin
open import Generic.Data.Vec

open import Data.Fin as Fin hiding (Fin)
open import Data.Vec as Vec hiding (Vec)

vec : Vec (Fin 4) 3
vec = fsuc (fsuc (fsuc fzero)) ∷ᵥ fzero ∷ᵥ fsuc fzero ∷ᵥ []ᵥ

test : reflect vec ≡ suc (suc (suc zero)) ∷ zero ∷ (Fin.Fin 4 ∋ suc zero) ∷ []
test = refl
