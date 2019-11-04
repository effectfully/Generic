module Generic.Lib.Data.Maybe where

open import Data.Maybe.Base using (Maybe; just; nothing; maybe; maybe′; from-just; fromMaybe) public

open import Generic.Lib.Intro
open import Generic.Lib.Category

infixr 0 _?>_

instance
  MaybeMonad : ∀ {α} -> RawMonad {α} Maybe
  MaybeMonad = record
    { return = just
    ; _>>=_  = Data.Maybe.Base._>>=_
    }

  MaybeApplicative : ∀ {α} -> RawApplicative {α} Maybe
  MaybeApplicative = rawIApplicative

  MaybeFunctor : ∀ {α} -> RawFunctor {α} Maybe
  MaybeFunctor = rawFunctor

_?>_ : ∀ {α} {A : Set α} -> Bool -> A -> Maybe A
true  ?> x = just x
false ?> x = nothing
