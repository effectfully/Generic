module Generic.Examples.Data.Maybe where

open import Generic.Main as Main hiding (Maybe; just; nothing)

Maybe : ∀ {α} -> Set α -> Set α
Maybe = readData Main.Maybe

pattern just x  = #₀ (x , lrefl)
pattern nothing = !#₁ lrefl

just′ : ∀ {α} {A : Set α} -> A -> Maybe A
just′ = just

nothing′ : ∀ {α} {A : Set α} -> Maybe A
nothing′ = nothing
