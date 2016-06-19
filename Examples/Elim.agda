module Generic.Examples.Elim where

open import Generic.Core
open import Generic.Function.Elim
open import Generic.Data.Vec

-- Is it possible to get rid of these `lift`s?
elimVec′ : ∀ {n α π} {A : Set α}
         -> (P : ∀ {n} -> Vec A n -> Set π)
         -> (∀ {n} {xs : Vec A n} x -> P xs -> P (x ∷ᵥ xs))
         -> P []ᵥ
         -> (xs : Vec A n)
         -> P xs
elimVec′ P f z = elim P (lift z , λ x {_} r -> lift (f x r))
