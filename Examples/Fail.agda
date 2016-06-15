module Generic.Examples.Fail where

open import Generic.Core
open import Generic.Property.Eq
open import Generic.Data.Vec

xs : Vec ℕ 3
xs = 2 ∷ᵥ 3 ∷ᵥ 0 ∷ᵥ []ᵥ

test : _≟_ {{DescEq {{tt , (ℕEq , λ {_} -> ℕEq , _) , tt}}}} xs xs ≡ yes refl
test = refl

-- An internal error has occurred. Please report this as a bug.
-- Location of the error: src/full/Agda/TypeChecking/InstanceArguments.hs:276
fail : xs ≟ xs ≡ yes refl
fail = ?
