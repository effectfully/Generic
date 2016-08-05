module Generic.Lib.Intro where

open import Level renaming (zero to lzero; suc to lsuc) public
open import Function public
open import Data.Bool.Base hiding (_≟_) public
open import Data.Sum renaming (map to smap) public
open import Data.Product renaming (map to pmap; zip to pzip) public

infixl 10 _%
infixl 2  _>>>_

data ⊥ {α} : Set α where
record ⊤ {α} : Set α where
  constructor tt

⊥₀ = ⊥ {lzero}
⊤₀ = ⊤ {lzero}

tt₀ : ⊤₀
tt₀ = tt

_% = _∘_

_>>>_ : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : ∀ {x} -> B x -> Set γ}
      -> (f : ∀ x -> B x) -> (∀ {x} -> (y : B x) -> C y) -> ∀ x -> C (f x)
(f >>> g) x = g (f x)

first : ∀ {α β γ} {A : Set α} {B : Set β} {C : A -> Set γ}
      -> (∀ x -> C x) -> (p : A × B) -> C (proj₁ p) × B
first f (x , y) = f x , y

second : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : A -> Set γ}
       -> (∀ {x} -> B x -> C x) -> Σ A B -> Σ A C
second g (x , y) = x , g y

instance
  ,-inst : ∀ {α β} {A : Set α} {B : A -> Set β} {{x : A}} {{y : B x}} -> Σ A B
  ,-inst {{x}} {{y}} = x , y
