module Generic.Data.Maybe where

open import Generic.Core

Maybe : ∀ {α} -> Set α -> Set α
Maybe A = μ′
        $ pos
        ⊕ (A ⇒ pos)

pattern nothing = #₀   lrefl
pattern just x  = !#₁ (x , lrefl)

nothing′ : ∀ {α} {A : Set α} -> Maybe A
nothing′ = nothing

just′ : ∀ {α} {A : Set α} -> A -> Maybe A
just′ = just
