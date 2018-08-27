module Generic.Examples.Data.Vec where

open import Generic.Main

import Data.Vec as Vec

infixr 5 _∷ᵥ_

Vec : ∀ {α} -> Set α -> ℕ -> Set α
Vec = readData Vec.Vec

-- []ᵥ : ∀ {α} {A : Set α} -> Vec A 0
pattern []ᵥ = #₀ lrefl

-- _∷ᵥ_ : ∀ {n α} {A : Set α} -> A -> Vec A n -> Vec A (suc n)
pattern _∷ᵥ_ {n} x xs = !#₁ (relv n , relv x , xs , lrefl)

elimVec : ∀ {n α π} {A : Set α}
        -> (P : ∀ {n} -> Vec A n -> Set π)
        -> (∀ {n} {xs : Vec A n} x -> P xs -> P (x ∷ᵥ xs))
        -> P []ᵥ
        -> (xs : Vec A n)
        -> P xs
elimVec P f z  []ᵥ      = z
elimVec P f z (x ∷ᵥ xs) = f x (elimVec P f z xs)
