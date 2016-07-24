module Generic.Lib.Category where

open import Category.Functor public
open import Category.Applicative public
open import Category.Monad public

open RawFunctor {{...}} public
open RawApplicative {{...}} hiding (_<$>_; _<$_; zipWith) renaming (_⊛_ to _<*>_) public
open RawMonad {{...}} hiding ( _<$>_; _<$_; _⊛_; _<⊛_; _⊛>_; _⊗_; rawFunctor; zipWith) public

open import Data.Maybe.Base
import Data.Maybe as Maybe
open import Data.List.Base
import Data.List as List

fmap = _<$>_

mapM : ∀ {α β} {A : Set α} {B : Set β} {M : Set β -> Set β} {{mMonad : RawMonad M}}
     -> (A -> M B) -> List A -> M (List B)
mapM {{mMonad}} = List.mapM mMonad

instance
  MaybeMonad : ∀ {α} -> RawMonad {α} Maybe
  MaybeMonad = Maybe.monad

  MaybeApplicative : ∀ {α} -> RawApplicative {α} Maybe
  MaybeApplicative = rawIApplicative

  MaybeFunctor : ∀ {α} -> RawFunctor {α} Maybe
  MaybeFunctor = rawFunctor
