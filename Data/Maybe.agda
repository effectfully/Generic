module Generic.Data.Maybe where

open import Generic.Main

import Data.Maybe.Base as Maybe

Maybe : ∀ {α} -> Set α -> Set α
Maybe = readData Maybe.Maybe

pattern just x  = #₀ (x , lrefl)
pattern nothing = !#₁ lrefl

just′ : ∀ {α} {A : Set α} -> A -> Maybe A
just′ = just

nothing′ : ∀ {α} {A : Set α} -> Maybe A
nothing′ = nothing
