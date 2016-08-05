module Generic.Lib.Data.Sets where

open import Generic.Lib.Intro
open import Generic.Lib.Data.Nat
open import Generic.Lib.Data.Pow

infixl 6 _⊔ⁿ_

_⊔ⁿ_ : ∀ {n} -> Level ^ n -> Level -> Level
_⊔ⁿ_ = flip $ foldPow _ _⊔_

Sets : ∀ {n} -> (αs : Level ^ n) -> Set (mapPow lsuc αs ⊔ⁿ lzero)
Sets {0}      _       = ⊤
Sets {suc _} (α , αs) = Set α × Sets αs

Fold : ∀ {n β αs} -> Sets {n} αs -> Set β -> Set (αs ⊔ⁿ β)
Fold {0}      tt      B = B
Fold {suc _} (A , As) B = A -> Fold As B

HList : ∀ {n} {αs} -> Sets {n} αs -> Set (αs ⊔ⁿ lzero)
HList {0}      tt      = ⊤
HList {suc _} (A , As) = A × HList As

applyFold : ∀ {n β αs} {As : Sets {n} αs} {B : Set β} -> Fold As B -> HList As -> B
applyFold {0}     y  tt      = y
applyFold {suc n} f (x , xs) = applyFold (f x) xs
