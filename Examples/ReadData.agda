module Generic.Examples.ReadData where

open import Generic.Main

data D {α β} (A : Set α) (B : ℕ -> Set β) : ∀ {n} -> B n -> List ℕ -> Set (α ⊔ β) where
  c₁ : ∀ {n} (y : B n) xs -> D A B y xs
  c₂ : ∀ {y : B 0} {{xs}} -> (∀ {n} (y : B n) -> D A B y xs) -> List A -> D A B y xs 

D′ : ∀ {α β} (A : Set α) (B : ℕ -> Set β) {n} -> B n -> List ℕ -> Set (α ⊔ β)
D′ = readData D

pattern c₁′ {n} y xs      = #₀  (n , y , xs , lrefl)
pattern c₂′ {y} xs r ys = !#₁ (y , xs , r , ys , lrefl)

inj : ∀ {α β} {A : Set α} {B : ℕ -> Set β} {n xs} {y : B n} -> D A B y xs -> D′ A B y xs
inj (c₁ y xs) = c₁′ y xs
inj (c₂ r ys) = c₂′ _ (λ x -> inj (r x)) ys

outj : ∀ {α β} {A : Set α} {B : ℕ -> Set β} {n xs} {y : B n} -> D′ A B y xs -> D A B y xs
outj (c₁′ y xs)    = c₁ y xs
outj (c₂′ xs r ys) = c₂ {{xs}} (λ x -> outj (r x)) ys
