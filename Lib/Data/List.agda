module Generic.Lib.Data.List where

open import Data.List.Base hiding ([]) renaming (fromMaybe to maybeToList) public
open List public

open import Generic.Lib.Intro
open import Generic.Lib.Equality.Propositional
open import Generic.Lib.Decidable
open import Generic.Lib.Category
open import Generic.Lib.Data.Nat
open import Generic.Lib.Data.Maybe
open import Generic.Lib.Data.Sum
open import Generic.Lib.Data.Product

import Data.List as List

infix 4 _∈_

foldr₁ : ∀ {α} {A : Set α} -> (A -> A -> A) -> A -> List A -> A
foldr₁ f z  []          = z
foldr₁ f z (x ∷ [])     = x
foldr₁ f z (x ∷ y ∷ xs) = f x (foldr₁ f z (y ∷ xs))

mapInd : ∀ {α β} {A : Set α} {B : Set β} -> (ℕ -> A -> B) -> List A -> List B
mapInd f  []      = []
mapInd f (x ∷ xs) = f 0 x ∷ mapInd (f ∘ suc) xs

mapMaybe : ∀ {α β} {A : Set α} {B : Set β} -> (A -> Maybe B) -> List A -> List B
mapMaybe f  []      = []
mapMaybe f (x ∷ xs) = maybe (_∷ mapMaybe f xs) (mapMaybe f xs) (f x)

mapM : ∀ {α β} {A : Set α} {B : Set β} {M : Set β -> Set β} {{mMonad : RawMonad M}}
     -> (A -> M B) -> List A -> M (List B)
mapM {{mMonad}} = List.mapM mMonad

downFromTo : ℕ -> ℕ -> List ℕ
downFromTo n m = map (m +_) (downFrom (n ∸ m))

Any : ∀ {α β} {A : Set α} -> (A -> Set β) -> List A -> Set β
Any B  []      = ⊥
Any B (x ∷ []) = B x
Any B (x ∷ xs) = B x ⊎ Any B xs

_∈_ : ∀ {α} {A : Set α} -> A -> List A -> Set
x ∈ xs = Any (x ≡_) xs

here : ∀ {α β} {A : Set α} {B : A -> Set β} {x} xs -> B x -> Any B (x ∷ xs)
here  []      y = y
here (x ∷ xs) y = inj₁ y

phere : ∀ {α} {A : Set α} {x : A} xs -> x ∈ x ∷ xs
phere xs = here xs refl

there : ∀ {α β} {A : Set α} {B : A -> Set β} {x} xs -> Any B xs -> Any B (x ∷ xs)
there  []      ()
there (x ∷ xs) a  = inj₂ a

mapAny : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : A -> Set γ}
       -> ∀ xs -> (∀ {x} -> B x -> C x) -> Any B xs -> Any C xs
mapAny  []           g  ()
mapAny (x ∷ [])      g  y       = g y
mapAny (x ∷ x′ ∷ xs) g (inj₁ y) = inj₁ (g y)
mapAny (x ∷ x′ ∷ xs) g (inj₂ r) = inj₂ (mapAny (x′ ∷ xs) g r)

All : ∀ {α β} {A : Set α} -> (A -> Set β) -> List A -> Set β
All B  []      = ⊤
All B (x ∷ xs) = B x × All B xs

allToList : ∀ {α β} {A : Set α} {B : Set β} {xs : List A} -> All (const B) xs -> List B
allToList {xs = []}      tt      = []
allToList {xs = x ∷ xs} (y , ys) = y ∷ allToList ys

allIn : ∀ {α β} {A : Set α} {B : A -> Set β} -> ∀ xs -> (∀ {x} -> x ∈ xs -> B x) -> All B xs
allIn  []      g = tt
allIn (x ∷ xs) g = g (phere xs) , allIn xs (g ∘ there xs)

mapAll : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : A -> Set γ} {xs : List A}
       -> (∀ {x} -> B x -> C x) -> All B xs -> All C xs
mapAll {xs = []}     g  tt      = tt
mapAll {xs = x ∷ xs} g (y , ys) = g y , mapAll g ys

unmap : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : Set γ} {xs : List A}
      -> (∀ {x} -> B x -> C) -> All B xs -> List C
unmap g = allToList ∘ mapAll g

mapAllInd : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : A -> Set γ} {xs}
          -> (∀ {x} -> ℕ -> B x -> C x) -> All B xs -> All C xs
mapAllInd {xs = []}     g  tt      = tt
mapAllInd {xs = x ∷ xs} g (y , ys) = g 0 y , mapAllInd (g ∘ suc) ys

traverseAll : ∀ {α β γ} {A : Set α} {B : A -> Set β} {C : A -> Set γ} {xs : List A}
                {F : Set γ -> Set γ} {{fFunctor : RawFunctor F}} {{fApplicative : RawApplicative F}}
            -> (∀ {x} -> B x -> F (C x)) -> All B xs -> F (All C xs)
traverseAll {xs = []}     g  tt      = pure tt
traverseAll {xs = x ∷ xs} g (y , ys) = _,_ <$> g y <*> traverseAll g ys

splitList : ∀ {α β} {A : Set α} {B : A -> Set β} -> List (Σ A B) -> Σ (List A) (All B)
splitList  []            = [] , tt
splitList ((x , y) ∷ ps) = pmap (_∷_ x) (_,_ y) (splitList ps)

lookupAllConst : ∀ {α β} {A : Set α} {B : Set β} {{bEq : Eq B}} {xs : List A}
               -> B -> All (const B) xs -> Maybe (∃ (_∈ xs))
lookupAllConst {xs = []}     y  tt      = nothing
lookupAllConst {xs = x ∷ xs} y (z , ys) = if y == z
  then just (, phere xs)
  else second (there xs) <$> lookupAllConst y ys
