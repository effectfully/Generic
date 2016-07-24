module Generic.Data.Lift where

open import Generic.Core as Core hiding (Lift; lift; lower)

Lift : ∀ {α} β -> Set α -> Set (α ⊔ β)
Lift β A = μ′
         $ (quote Core.lift , A ⇒ pos)
         ∷ []

pattern lift x = !#₀ (x , lrefl)

lower : ∀ {α} {A : Set α} β -> Lift β A -> A
lower β (lift x) = x
