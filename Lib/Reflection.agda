module Generic.Lib.Reflection where

open import Reflection
  renaming (visible to expl; hidden to impl; instance′ to inst;
    relevant to rel; irrelevant to irr; pi to rpi; lam to rlam; var to rvar)
  hiding (_≟_) public

open import Generic.Lib.Category
open import Generic.Lib.Decidable

open import Function
open import Data.Unit.Base
open import Data.Nat.Base
open import Data.String.Base
open import Data.Maybe.Base hiding (map)
open import Data.Product hiding (map)
open import Data.List.Base

infixl 3 _·_

record Reify {α} (A : Set α) : Set α where
  field reify : A -> Term

  macro
    reflect : A -> Term -> TC _
    reflect = unify ∘ reify
open Reify {{...}} public

pattern earg x = arg (arg-info expl rel) x
{-# DISPLAY arg (arg-info expl relevant) = earg #-}

pattern iarg x = arg (arg-info impl rel) x
{-# DISPLAY arg (arg-info impl relevant) = iarg #-}

vis : {A : Set} -> (A -> List (Arg Term) -> Term) -> A -> List Term -> Term
vis k x = k x ∘ map earg

vis₀ : {A : Set} -> (A -> List (Arg Term) -> Term) -> A -> Term
vis₀ k x = vis k x []

vis₁ : {A : Set} -> (A -> List (Arg Term) -> Term) -> A -> Term -> Term
vis₁ k f x₁ = vis k f (x₁ ∷ [])

vis₂ : {A : Set} -> (A -> List (Arg Term) -> Term) -> A -> Term -> Term -> Term
vis₂ k f x₁ x₂ = vis k f (x₁ ∷ x₂ ∷ [])

vis₃ : {A : Set} -> (A -> List (Arg Term) -> Term) -> A -> Term -> Term -> Term -> Term
vis₃ k f x₁ x₂ x₃ = vis k f (x₁ ∷ x₂ ∷ x₃ ∷ [])

elam : String -> Term -> Term
elam s = rlam expl ∘ abs s

_·_ : Term -> Term -> Term
f · x = vis₂ def (quote id) f x

unarg : ∀ {A} -> Arg A -> A
unarg (arg _ x) = x

instance
  NameEq : Eq Name
  NameEq = viaBase _≟-Name_

  TermReify : Reify Term
  TermReify = record
    { reify = id
    }

  NameReify : Reify Name
  NameReify = record
    { reify = lit ∘′ name
    }

  VisibilityReify : Reify Visibility
  VisibilityReify = record
    { reify = λ
        { expl -> quoteTerm expl
        ; impl -> quoteTerm impl
        ; inst -> quoteTerm inst
        }
    }

  ProdReify : ∀ {α β} {A : Set α} {B : A -> Set β}
                {{aReify : Reify A}} {{bReify : ∀ {x} -> Reify (B x)}} -> Reify (Σ A B)
  ProdReify = record
    { reify = uncurry λ x y -> vis₂ con (quote _,_) (reify x) (reify y)
    }                

  ℕReify : Reify ℕ
  ℕReify = record
    { reify = fold (quoteTerm 0) (vis₁ con (quote suc))
    }

  ListReify : ∀ {α} {A : Set α} {{aReify : Reify A}} -> Reify (List A)
  ListReify = record
    { reify = foldr (λ x r -> vis₂ con (quote _∷_) (reify x) r) (quoteTerm (List Term ∋ []))
    }  

  ArgFunctor : RawFunctor Arg
  ArgFunctor = record
    { _<$>_ = λ{ f (arg i x) -> arg i (f x) }
    }

  AbsFunctor : RawFunctor Abs
  AbsFunctor = record
    { _<$>_ = λ{ f (abs s x) -> abs s (f x) }
    }

  TCMonad : ∀ {α} -> RawMonad {α} TC
  TCMonad = record
    { return = returnTC
    ; _>>=_  = bindTC
    }

  TCApplicative : ∀ {α} -> RawApplicative {α} TC
  TCApplicative = rawIApplicative

  TCFunctor : ∀ {α} -> RawFunctor {α} TC
  TCFunctor = rawFunctor

unshift : Term -> Term
unshift t = elam "_" t · quoteTerm tt

keep : (ℕ -> ℕ) -> ℕ -> ℕ
keep ι  0      = 0
keep ι (suc n) = suc (ι n)

{-# TERMINATING #-}
mutual
  ren : (ℕ -> ℕ) -> Term -> Term
  ren ι (rvar x xs)     = rvar (ι x) (rens ι xs)
  ren ι (con c xs)      = con c (rens ι xs)
  ren ι (def f xs)      = def f (rens ι xs)
  ren ι (rlam v t)      = rlam v (ren (keep ι) <$> t)
  ren ι (pat-lam cs xs) = undefined where postulate undefined : _
  ren ι (rpi a b)       = rpi (ren ι <$> a) (ren (keep ι) <$> b)
  ren ι (sort s)        = sort (renSort ι s)
  ren ι (lit l)         = lit l
  ren ι (meta x xs)     = meta x (rens ι xs)
  ren ι  unknown        = unknown

  rens : (ℕ -> ℕ) -> List (Arg Term) -> List (Arg Term)
  rens ι = map (fmap (ren ι))

  renSort : (ℕ -> ℕ) -> Sort -> Sort
  renSort ι (set t) = set (ren ι t)
  renSort ι (lit n) = lit n
  renSort ι unknown = unknown

shiftBy : ℕ -> Term -> Term
shiftBy = ren ∘ _+_

takePi : ℕ -> Type -> Maybe Type
takePi  0       a                = just unknown
takePi (suc n) (rpi a (abs s b)) = rpi a ∘ abs s <$> takePi n b
takePi  _       _                = nothing

dropPi : ℕ -> Type -> Maybe Type
dropPi  0       a                = just a
dropPi (suc n) (rpi a (abs s b)) = dropPi n b
dropPi  _       _                = nothing

craftLams : Type -> Term -> Term
craftLams (rpi (earg a ) (abs s b)) t = elam s (craftLams b t)
craftLams (rpi  _        (abs s b)) t = craftLams b t
craftLams  _                        t = t

getData : Name -> TC (ℕ × List (Name × Type))
getData = getDefinition >=> λ
  { (data-type n cs) -> _,_ n <$> mapM (λ c -> _,_ c <$> getType c) cs
  ;  _               -> typeError (strErr "not a data" ∷ [])
  }
