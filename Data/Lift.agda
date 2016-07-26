module Generic.Data.Lift where

open import Generic.Main as Main hiding (Lift; lift; lower)

-- `readData Main.Lift` doesn't work.

Lift : ∀ {α} β -> Set α -> Set (α ⊔ β)
Lift β A = μ′ (packData (quote Main.Lift) 3 ((A ⇒ pos) ∷ []) (quote Main.lift , tt))

pattern lift x = !#₀ (x , lrefl)

lower : ∀ {α} {A : Set α} β -> Lift β A -> A
lower β (lift x) = x
