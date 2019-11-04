module Generic.Examples.Data.Maybe where

open import Generic.Main as Main hiding (Maybe; just; nothing)

Maybe : ∀ {α} -> Set α -> Set α
Maybe = readData Main.Maybe

pattern nothing = #₀ lrefl
pattern just x  = !#₁ (relv x , lrefl)

just′ : ∀ {α} {A : Set α} -> A -> Maybe A
just′ = just

nothing′ : ∀ {α} {A : Set α} -> Maybe A
nothing′ = nothing
