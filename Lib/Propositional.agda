module Generic.Lib.Propositional where

open import Level
open import Relation.Binary

infix 3 _≡_ _≗_

data _≡_ {α} {A : Set α} (x : A) : A -> Set where
  instance refl : x ≡ x

pattern lrefl = lift refl

_≗_ : ∀ {α β} {A : Set α} {B : A -> Set β} -> (∀ x -> B x) -> (∀ x -> B x) -> Set α
f ≗ g = ∀ x -> f x ≡ g x

sym : ∀ {α} {A : Set α} {x y : A} -> x ≡ y -> y ≡ x
sym refl = refl

trans : ∀ {α} {A : Set α} {x y z : A} -> x ≡ y -> y ≡ z -> x ≡ z
trans refl refl = refl

left : ∀ {α} {A : Set α} {x y z : A} -> y ≡ x -> z ≡ x -> y ≡ z
left refl refl = refl

right : ∀ {α} {A : Set α} {x y z : A} -> x ≡ y -> x ≡ z -> y ≡ z
right refl refl = refl

subst : ∀ {α β} {A : Set α} {x y} -> (B : A -> Set β) -> x ≡ y -> B x -> B y
subst B refl z = z

cong : ∀ {α β} {A : Set α} {B : Set β} {x y} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
cong f refl = refl

cong₂ : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ} {x₁ x₂ y₁ y₂}
      -> (g : A -> B -> C) -> x₁ ≡ x₂ -> y₁ ≡ y₂ -> g x₁ y₁ ≡ g x₂ y₂
cong₂ g refl refl = refl

≡-Setoid : ∀ {α} -> Set α -> Setoid α zero
≡-Setoid A = record
  { Carrier       = A
  ; _≈_           = _≡_
  ; isEquivalence = record
      { refl  = refl
      ; sym   = sym
      ; trans = trans
      }
  }
