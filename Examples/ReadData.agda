module Generic.Examples.ReadData where

open import Generic.Main

data D (A : Set) (B : ℕ -> Set) : ∀ n -> B n -> Set where
  c₁ : ∀ {n} y -> D A B n y
  c₂ : ∀ {y} -> (∀ {n} y -> D A B n y) -> List ℕ -> D A B 0 y 

D′ : ∀ (A : Set) (B : ℕ -> Set) n -> B n -> Set
D′ = readData D

pattern c₁′ {n} y    = #₀  (n , y , lrefl)
pattern c₂′ {y} r xs = !#₁ (y , r , xs , lrefl)

inj : ∀ {A B n y} -> D A B n y -> D′ A B n y
inj (c₁ y)    = c₁′ y
inj (c₂ r xs) = c₂′ (λ x -> inj (r x)) xs

outj : ∀ {A B n y} -> D′ A B n y -> D A B n y
outj (c₁′ y)    = c₁ y
outj (c₂′ r xs) = c₂ (λ x -> outj (r x)) xs
