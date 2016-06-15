module Generic.Data.Lift where

open import Generic.Core hiding (Lift; lift; lower)

Lift : ∀ {α} β -> Set α -> Set (α ⊔ β)
Lift β A = μ′
         $ (A ⇒ pos)
         ∷ []

pattern lift x = !#₀ (x , lrefl)

lower : ∀ {α} {A : Set α} β -> Lift β A -> A
lower β (lift x) = x
