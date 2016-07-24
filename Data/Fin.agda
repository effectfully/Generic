module Generic.Data.Fin where

open import Generic.Main

import Data.Fin as Fin

Fin : ℕ -> Set
Fin = readData Fin.Fin

pattern fzero {n}   = #₀  (n , lrefl)
pattern fsuc  {n} i = !#₁ (n , i , lrefl)

elimFin : ∀ {n π}
        -> (P : ∀ {n} -> Fin n -> Set π)
        -> (∀ {n} {i : Fin n} -> P i -> P (fsuc i))
        -> (∀ {n} -> P {suc n} fzero)
        -> (i : Fin n)
        -> P i
elimFin P f x  fzero   = x
elimFin P f x (fsuc i) = f (elimFin P f x i)
