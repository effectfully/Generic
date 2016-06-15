module Generic.Data.List where

open import Generic.Core

infixr 5 _∷ₗ_

List : ∀ {α} -> Set α -> Set α
List A = μ′
      $ pos
      ∷ (A ⇒ pos ⊛ pos)
      ∷ []

pattern []ₗ       = #₀ lrefl
pattern _∷ₗ_ x xs = !#₁ (x , xs , lrefl)

elimList : ∀ {α π} {A : Set α}
         -> (P : List A -> Set π)
         -> (∀ {xs} x -> P xs -> P (x ∷ₗ xs))
         -> P []ₗ
         -> ∀ xs
         -> P xs
elimList P f z  []ₗ      = z
elimList P f z (x ∷ₗ xs) = f x (elimList P f z xs)
