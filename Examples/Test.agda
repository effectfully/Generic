module Generic.Examples.Test where

open import Generic.Core
open import Generic.Property.Eq

infixr 5 _∷ᵥ_

vec : ∀ {α} -> Set α -> Data ℕ α
vec A = var 0
      ∷ (πᵢ ℕ λ n -> π A λ _ -> var n ⊛ var (suc n))
      ∷ []

Vec : ∀ {α} -> Set α -> ℕ -> Set α
Vec = μ ∘ vec

-- []ᵥ : ∀ {α} {A : Set α} -> Vec A 0
pattern []ᵥ = node (inj₁ lrefl)

-- _∷ᵥ_ : ∀ {n α} {A : Set α} -> A -> Vec A n -> Vec A (suc n)
pattern _∷ᵥ_ {n} x xs = node (inj₂ (n , x , xs , lrefl))

elimVec : ∀ {α π} {A : Set α} {n}
        -> (P : ∀ {n} -> Vec A n -> Set π)
        -> (∀ {n} {xs : Vec A n} x -> P xs -> P (x ∷ᵥ xs))
        -> P []ᵥ
        -> (xs : Vec A n)
        -> P xs
elimVec P f z  []ᵥ      = z
elimVec P f z (x ∷ᵥ xs) = f x (elimVec P f z xs)


xs : Vec ℕ 3
xs = 2 ∷ᵥ 3 ∷ᵥ 0 ∷ᵥ []ᵥ

test : _≟_ {{DescEq {{tt , (natEq , λ _ -> natEq , _) , tt}}}} xs xs ≡ yes refl
test = refl

-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/InstanceArguments.hs:276
fail : xs ≟ xs ≡ yes refl
fail = ?
