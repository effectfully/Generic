module Generic.Data.Vec where

open import Generic.Core

infixr 5 _∷ᵥ_

vec : ∀ {α} -> Set α -> Data ℕ α
vec A = var 0
      ∷ (ipi ℕ λ n -> pi A λ _ -> var n ⊛ var (suc n))
      ∷ []

Vec : ∀ {α} -> Set α -> ℕ -> Set α
Vec = μ ∘ vec

-- []ᵥ : ∀ {α} {A : Set α} -> Vec A 0
pattern []ᵥ = node (inj₁ lrefl)

-- _∷ᵥ_ : ∀ {n α} {A : Set α} -> A -> Vec A n -> Vec A (suc n)
pattern _∷ᵥ_ {n} x xs = node (inj₂ (n , x , xs , lrefl))

elimVec : ∀ {α pi} {A : Set α} {n}
        -> (P : ∀ {n} -> Vec A n -> Set pi)
        -> (∀ {n} {xs : Vec A n} x -> P xs -> P (x ∷ᵥ xs))
        -> P []ᵥ
        -> (xs : Vec A n)
        -> P xs
elimVec P f z  []ᵥ      = z
elimVec P f z (x ∷ᵥ xs) = f x (elimVec P f z xs)
