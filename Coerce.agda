module Generic.Coerce where

open import Generic.Prelude

Coerce′ : ∀ {α β} -> α ≡ β -> Set α -> Set β
Coerce′ refl = id

Coerce : ∀ {α β} -> α ≡ β -> Set α -> Set β
Coerce q A = Apply (λ q -> Coerce′ q A) q

coerce′ : ∀ {α β} {A : Set α} {{q : α ≡ β}} -> A -> Coerce′ q A
coerce′ {{refl}} = id

coerce : ∀ {α β} {A : Set α} {q : α ≡ β} -> A -> Coerce q A
coerce {q = q} = tag ∘ coerce′ {{q}}

uncoerce′ : ∀ {α β} {A : Set α} {{q : α ≡ β}} -> Coerce′ q A -> A
uncoerce′ {{refl}} = id

inspectUncoerce′ : ∀ {α β} {A : Set α} {{q : α ≡ β}}
                 -> (p : Coerce′ q A) -> ∃ λ (x : A) -> p ≡ coerce′ x
inspectUncoerce′ {{refl}} x = x , refl

unproj₁′ : ∀ {α β γ} {A : Set α} {B : A -> Set β} {{q : α ⊔ β ≡ γ}}
         -> Coerce′ q (Σ A B) -> A
unproj₁′ = proj₁ ∘ uncoerce′

unproj₂′ : ∀ {α β γ} {A : Set α} {B : A -> Set β} {{q : α ⊔ β ≡ γ}}
         -> (p : Coerce′ q (Σ A B)) -> B (unproj₁′ p)
unproj₂′ = proj₂ ∘ uncoerce′

uncoerce : ∀ {α β} {A : Set α} {q : α ≡ β} -> Coerce q A -> A
uncoerce {q = q} x = uncoerce′ {{q}} (detag x)

unproj₁ : ∀ {α β γ} {A : Set α} {B : A -> Set β} {q : α ⊔ β ≡ γ}
        -> Coerce q (Σ A B) -> A
unproj₁ = proj₁ ∘ uncoerce

unproj₂ : ∀ {α β γ} {A : Set α} {B : A -> Set β} {q : α ⊔ β ≡ γ}
        -> (p : Coerce q (Σ A B)) -> B (unproj₁ p)
unproj₂ = proj₂ ∘ uncoerce

split′ : ∀ {α β γ δ} {A : Set α} {B : A -> Set β} {C : Set γ} {{q : α ⊔ β ≡ δ}}
       -> Coerce′ q (Σ A B) -> (∀ x -> B x -> C) -> C
split′ p g = uncurry g (uncoerce′ p)

split : ∀ {α β γ δ} {A : Set α} {B : A -> Set β} {C : Set γ} {q : α ⊔ β ≡ δ}
      -> Coerce q (Σ A B) -> (∀ x -> B x -> C) -> C
split {q = q} p = split′ {{q}} (detag p)

Transform : ∀ {α β γ δ ε} {A : Set α} {B : A -> Set β} {q₁ : α ⊔ β ≡ γ} {{q₂ : δ ≡ ε}}
          -> Coerce q₁ (Σ A B) -> (∀ x -> B x -> Set δ) -> Set ε
Transform {{q₂}} p C = split p λ x y -> Coerce′ q₂ (C x y)

splitWith₂ : ∀ {α β γ δ} {A : Set α} {B : A -> Set β}
           -> (q : α ⊔ β ≡ δ)
           -> (C : ∀ {δ} {r : α ⊔ β ≡ δ} -> Coerce′ r (Σ A B) -> Coerce′ r (Σ A B) -> Set γ)
           -> (p₁ p₂ : Coerce′ q (Σ A B))
           -> (∀ x₁ x₂ y₁ y₂ -> C {r = refl} (x₁ , y₁) (x₂ , y₂))
           -> C {r = q} p₁ p₂
splitWith₂ refl C (x₁ , y₁) (x₂ , y₂) g = g x₁ x₂ y₁ y₂
