module Generic.Lib.Intro where

open import Level renaming (zero to lzero; suc to lsuc) public
open import Function public
open import Data.Bool.Base hiding (_<_; _≤_) public

infixl 10 _%
infixl 2  _>>>_

data ⊥ {α} : Set α where
record ⊤ {α} : Set α where
  instance constructor tt

⊥₀ = ⊥ {lzero}
⊤₀ = ⊤ {lzero}

tt₀ : ⊤₀
tt₀ = tt

_% = _∘_

_>>>_ : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : ∀ {x} -> B x -> Set γ}
      -> (f : ∀ x -> B x) -> (∀ {x} -> (y : B x) -> C y) -> ∀ x -> C (f x)
(f >>> g) x = g (f x)
