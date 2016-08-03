module Generic.Lib.Category where

open import Category.Functor public
open import Category.Applicative public
open import Category.Monad public

open RawFunctor {{...}} public
open RawApplicative {{...}} hiding (_<$>_; _<$_; zipWith) renaming (_⊛_ to _<*>_) public
open RawMonad {{...}} hiding ( _<$>_; _<$_; _⊛_; _<⊛_; _⊛>_; _⊗_; rawFunctor; zipWith) public

fmap = _<$>_
