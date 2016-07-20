module Generic.Lib.Propositional where

open import Level

infix 3 _≡_ _≗_

data _≡_ {α} {A : Set α} (x : A) : A -> Set where
  instance refl : x ≡ x

pattern lrefl = lift refl

_≗_ : ∀ {α β} {A : Set α} {B : A -> Set β} -> (∀ x -> B x) -> (∀ x -> B x) -> Set α
f ≗ g = ∀ x -> f x ≡ g x

subst : ∀ {α β} {A : Set α} {x y} -> (B : A -> Set β) -> x ≡ y -> B x -> B y
subst B refl z = z

cong : ∀ {α β} {A : Set α} {B : Set β} {x y} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
cong f refl = refl

cong₂ : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ} {x₁ x₂ y₁ y₂}
      -> (g : A -> B -> C) -> x₁ ≡ x₂ -> y₁ ≡ y₂ -> g x₁ y₁ ≡ g x₂ y₂
cong₂ g refl refl = refl
