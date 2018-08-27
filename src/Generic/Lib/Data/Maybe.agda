module Generic.Lib.Data.Maybe where

open import Data.Maybe.Base using (Maybe; just; nothing; maybe; maybe′; from-just) public

open import Generic.Lib.Intro
open import Generic.Lib.Category
open import Data.Maybe

infixr 0 _?>_

instance
  MaybeMonad : ∀ {α} -> RawMonad {α} Maybe
  MaybeMonad = monad

  MaybeApplicative : ∀ {α} -> RawApplicative {α} Maybe
  MaybeApplicative = rawIApplicative

  MaybeFunctor : ∀ {α} -> RawFunctor {α} Maybe
  MaybeFunctor = rawFunctor

fromMaybe : ∀ {α} {A : Set α} -> A -> Maybe A -> A
fromMaybe y (just x) = x
fromMaybe y  nothing = y

_?>_ : ∀ {α} {A : Set α} -> Bool -> A -> Maybe A
true  ?> x = just x
false ?> x = nothing
