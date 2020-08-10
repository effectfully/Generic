module Generic.Test.ReadData where

open import Generic.Main

data D {α β} (A : Set α) (B : ℕ -> Set β) : ∀ {n} -> B n -> List ℕ -> Set (α ⊔ β) where
  c₁ : ∀ {n} (y : B n) xs -> A -> D A B y xs
  c₂ : ∀ {y : B 0} -> (∀ {n} (y : B n) {{xs}} -> D A B y xs) -> .(List A) -> D A B y []

-- No longer works: Failed to solve the following constraints: Has bigger sort: Setω
-- D′ : TypeOf D
D′ : ∀ {α β} -> (A : Set α) -> (B : ℕ -> Set β) -> ∀ {n} -> B n -> List ℕ -> Set (α ⊔ β)
D′ = readData D

unquoteDecl foldD = deriveFoldTo foldD (quote D)

inj : ∀ {α β} {A : Set α} {B : ℕ -> Set β} {n xs} {y : B n} -> D A B y xs -> D′ A B y xs
inj = gcoerce foldD

outj : ∀ {α β} {A : Set α} {B : ℕ -> Set β} {n xs} {y : B n} -> D′ A B y xs -> D A B y xs
outj d = guncoerce d

pattern c₁′ {n} y xs x = #₀  (relv n , relv y , relv xs , relv x , lrefl)
pattern c₂′ {y} r ys   = !#₁ (relv y , r , irrv ys , lrefl)

inj′ : ∀ {α β} {A : Set α} {B : ℕ -> Set β} {n xs} {y : B n} -> D A B y xs -> D′ A B y xs
inj′ (c₁ y xs x) = c₁′ y xs x
inj′ (c₂ r ys)   = c₂′ (λ y -> inj′ (r y)) ys

outj′ : ∀ {α β} {A : Set α} {B : ℕ -> Set β} {n xs} {y : B n} -> D′ A B y xs -> D A B y xs
outj′ (c₁′ y xs x) = c₁ y xs x
outj′ (c₂′ r ys)   = c₂ (λ y -> outj′ (r y)) ys
