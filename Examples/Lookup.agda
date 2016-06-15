module Generic.Examples.Lookup where

open import Generic.Core
open import Generic.Function.Lookup
open import Generic.Data.Vec

xs : Vec ℕ 4
xs = 3 ∷ᵥ 1 ∷ᵥ 4 ∷ᵥ 2 ∷ᵥ []ᵥ

pattern pthere₁ p = pthere (inj₁ p)

test-lookup2 : xs ! pthere₁ (pthere₁ (phere (thereπ hereπ))) ≡ 4
test-lookup2 = refl

test-drop2 : xs ! pthere₁ (phere (thereπ (thereπ here⊛))) ≡ 4 ∷ᵥ 2 ∷ᵥ []ᵥ
test-drop2 = refl
