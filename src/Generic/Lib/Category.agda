module Generic.Lib.Category where

open import Category.Functor public hiding (Morphism)
open import Category.Applicative public
open import Category.Monad public

open RawFunctor {{...}} public
open RawApplicative {{...}} hiding (_<$>_; _<&>_; _<$_; zip; zipWith) renaming (_⊛_ to _<*>_) public
open RawMonad {{...}} hiding (pure; _<$>_; _<&>_; _<$_; _⊛_; _<⊛_; _⊛>_; _⊗_; rawFunctor; zip; zipWith) public

fmap = _<$>_
