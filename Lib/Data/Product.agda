module Generic.Lib.Data.Product where

open import Data.Product renaming (map to pmap; zip to pzip) public

open import Generic.Lib.Intro
open import Generic.Lib.Category

first : ∀ {α β γ} {A : Set α} {B : Set β} {C : A -> Set γ}
      -> (∀ x -> C x) -> (p : A × B) -> C (proj₁ p) × B
first f (x , y) = f x , y

second : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : A -> Set γ}
       -> (∀ {x} -> B x -> C x) -> Σ A B -> Σ A C
second g (x , y) = x , g y

-- `B` and `C` are in the same universe.
firstF : ∀ {α β} {A : Set α} {B : Set β} {C : A -> Set β}
           {F : Set β -> Set β} {{fFunctor : RawFunctor F}}
       -> (∀ x -> F (C x)) -> (p : A × B) -> F (C (proj₁ p) × B)
firstF f (x , y) = flip _,_ y <$> f x

-- `A` and `C` are in the same universe.
secondF : ∀ {α β} {A : Set α} {B : A -> Set β} {C : A -> Set α}
            {F : Set α -> Set α} {{fFunctor : RawFunctor F}}
        -> (∀ {x} -> B x -> F (C x)) -> Σ A B -> F (Σ A C)
secondF g (x , y) = _,_ x <$> g y

instance
  ,-inst : ∀ {α β} {A : Set α} {B : A -> Set β} {{x : A}} {{y : B x}} -> Σ A B
  ,-inst {{x}} {{y}} = x , y
