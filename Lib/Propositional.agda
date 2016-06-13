module Generic.Lib.Propositional where

open import Level

infix 3 _≡_

data _≡_ {α} {A : Set α} (x : A) : A -> Set where
  instance refl : x ≡ x

pattern lrefl = lift refl

cong : ∀ {α β} {A : Set α} {B : Set β} {x y} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
cong f refl = refl

cong₂ : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ} {x₁ x₂ y₁ y₂}
      -> (g : A -> B -> C) -> x₁ ≡ x₂ -> y₁ ≡ y₂ -> g x₁ y₁ ≡ g x₂ y₂
cong₂ g refl refl = refl
