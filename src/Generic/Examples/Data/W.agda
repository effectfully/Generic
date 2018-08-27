module Generic.Examples.Data.W where

open import Generic.Main

import Data.W as W

W : ∀ {α β} -> (A : Set α) -> (A -> Set β) -> Set (α ⊔ β)
W = readData W.W

pattern sup x g = !#₀ (relv x , g , lrefl)

elimW : ∀ {α β π} {A : Set α} {B : A -> Set β}
      -> (P : W A B -> Set π)
      -> (∀ {x} {g : B x -> W A B} -> (∀ y -> P (g y)) -> P (sup x g))
      -> ∀ w
      -> P w
elimW {B = B} P h (sup x g) = h (λ y -> elimW {B = B} P h (g y))
