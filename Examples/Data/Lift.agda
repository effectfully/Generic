module Generic.Examples.Data.Lift where

open import Generic.Main as Main hiding (Lift; lift; lower)

-- `readData Main.Lift` doesn't work, because of the same issue with implicits.

postulate
  whatever : {A : Set} -> A

Lift : ∀ {α} β -> Set α -> Set (α ⊔ β)
Lift β A = μ′ $ packData (quote Main.Lift) whatever whatever ((A ⇒ pos) ∷ []) (quote Main.lift , tt)

pattern lift x = !#₀ (x , lrefl)

lower : ∀ {α} {A : Set α} β -> Lift β A -> A
lower β (lift x) = x
