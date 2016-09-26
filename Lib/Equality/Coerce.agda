module Generic.Lib.Equality.Coerce where

open import Generic.Lib.Intro
open import Generic.Lib.Equality.Propositional
open import Generic.Lib.Decidable
open import Generic.Lib.Data.Product

Coerce′ : ∀ {α β} -> α ≡ β -> Set α -> Set β
Coerce′ refl = id

coerce′ : ∀ {α β} {A : Set α} -> (q : α ≡ β) -> A -> Coerce′ q A
coerce′ refl = id

uncoerce′ : ∀ {α β} {A : Set α} -> (q : α ≡ β) -> Coerce′ q A -> A
uncoerce′ refl = id

inspectUncoerce′ : ∀ {α β} {A : Set α}
                 -> (q : α ≡ β) -> (p : Coerce′ q A) -> ∃ λ x -> p ≡ coerce′ q x
inspectUncoerce′ refl x = x , refl

split : ∀ {α β γ δ} {A : Set α} {B : A -> Set β} {C : Set γ}
      -> (q : α ⊔ β ≡ δ) -> Coerce′ q (Σ A B) -> (∀ x -> B x -> C) -> C
split q p g = uncurry g (uncoerce′ q p)

decCoerce′ : ∀ {α β} {A : Set α} -> (q : α ≡ β) -> IsSet A -> IsSet (Coerce′ q A)
decCoerce′ refl = id

data Coerce {β} : ∀ {α} -> α ≡ β -> Set α -> Set β where
  coerce : ∀ {A} -> A -> Coerce refl A

qcoerce : ∀ {α β} {A : Set α} {q : α ≡ β} -> A -> Coerce q A
qcoerce {q = refl} = coerce
