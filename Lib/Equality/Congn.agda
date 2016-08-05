module Generic.Lib.Equality.Congn where

open import Generic.Lib.Intro
open import Generic.Lib.Equality.Propositional
open import Generic.Lib.Data.Nat
open import Generic.Lib.Data.Pow
open import Generic.Lib.Data.Sets

zip≡ : ∀ {n αs} {As : Sets {n} αs} -> HList As -> HList As -> Sets (replicatePow n lzero)
zip≡ {0}      tt       tt      = tt
zip≡ {suc _} (x , xs) (y , ys) = (x ≡ y) , zip≡ xs ys

congn : ∀ {β} {B : Set β} n {αs} {As : Sets {n} αs} {xs ys : HList As}
      -> (f : Fold As B) -> Fold (zip≡ xs ys) (applyFold f xs ≡ applyFold f ys)
congn  0      y      = refl
congn (suc n) f refl = congn n (f _)

private
  module Test where
    cong′ : ∀ {α β} {A : Set α} {B : Set β} {x y} -> (f : A -> B) -> x ≡ y -> f x ≡ f y
    cong′ = congn 1

    cong₂′ : ∀ {α β γ} {A : Set α} {B : Set β} {C : Set γ} {x₁ x₂ y₁ y₂}
           -> (g : A -> B -> C) -> x₁ ≡ x₂ -> y₁ ≡ y₂ -> g x₁ y₁ ≡ g x₂ y₂
    cong₂′ = congn 2
