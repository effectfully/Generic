module Generic.Data.Vec where

open import Generic.Core

infixr 5 _∷ᵥ_

Vec : ∀ {α} -> Set α -> ℕ -> Set α
Vec A = μ
      $ var 0
      ⊕ (ipi ℕ λ n -> A ⇒ var n ⊛ var (suc n))

-- []ᵥ : ∀ {α} {A : Set α} -> Vec A 0
pattern []ᵥ = #₀ lrefl

-- _∷ᵥ_ : ∀ {n α} {A : Set α} -> A -> Vec A n -> Vec A (suc n)
pattern _∷ᵥ_ {n} x xs = !#₁ (n , x , xs , lrefl)

elimVec : ∀ {n α π} {A : Set α}
        -> (P : ∀ {n} -> Vec A n -> Set π)
        -> (∀ {n} {xs : Vec A n} x -> P xs -> P (x ∷ᵥ xs))
        -> P []ᵥ
        -> (xs : Vec A n)
        -> P xs
elimVec P f z  []ᵥ      = z
elimVec P f z (x ∷ᵥ xs) = f x (elimVec P f z xs)
