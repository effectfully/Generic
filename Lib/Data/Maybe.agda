module Generic.Lib.Data.Maybe where

open import Data.Maybe.Base using (Maybe; just; nothing; maybe; from-just) public

open import Generic.Lib.Category
open import Data.Maybe

instance
  MaybeMonad : ∀ {α} -> RawMonad {α} Maybe
  MaybeMonad = monad

  MaybeApplicative : ∀ {α} -> RawApplicative {α} Maybe
  MaybeApplicative = rawIApplicative

  MaybeFunctor : ∀ {α} -> RawFunctor {α} Maybe
  MaybeFunctor = rawFunctor
