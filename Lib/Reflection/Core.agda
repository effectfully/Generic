module Generic.Lib.Reflection.Core where

open import Reflection
  renaming (visible to expl; hidden to impl; instance′ to inst;
    relevant to rel; irrelevant to irr; pi to rpi; lam to rlam; var to rvar)
  hiding (_≟_) public

open import Generic.Lib.Intro
open import Generic.Lib.Decidable
open import Generic.Lib.Category
open import Generic.Lib.Data.Nat
open import Generic.Lib.Data.String
open import Generic.Lib.Data.Maybe
open import Generic.Lib.Data.Product
open import Generic.Lib.Data.List

import Data.Nat.Base as Nat

infixl 3 _·_

named : String -> String
named s = if s == "_" then "x" else s

record Reify {α} (A : Set α) : Set α where
  field reify : A -> Term

  macro
    reflect : A -> Term -> TC _
    reflect = unify ∘ reify
open Reify {{...}} public

pattern earg  x = arg (arg-info expl rel) x
pattern iarg  x = arg (arg-info impl rel) x
pattern iiarg x = arg (arg-info inst rel) x

{-# DISPLAY arg (arg-info expl rel) = earg  #-}
{-# DISPLAY arg (arg-info impl rel) = iarg  #-}
{-# DISPLAY arg (arg-info inst rel) = iiarg #-}

pattern elam  s t = rlam expl (abs s t)
pattern ilam  s t = rlam impl (abs s t)
pattern iilam s t = rlam inst (abs s t)

{-# DISPLAY rlam expl (abs s t) = elam  s t #-}
{-# DISPLAY rlam impl (abs s t) = ilam  s t #-}
{-# DISPLAY rlam inst (abs s t) = iilam s t #-}

pattern api a s b = rpi a (abs s b)

{-# DISPLAY rpi a (abs s b) = api a s b #-}

pattern aepi  a s b = api (earg  a) s b
pattern aipi  a s b = api (iarg  a) s b
pattern aiipi a s b = api (iiarg a) s b

-- "Pattern not allowed in DISPLAY pragma"
-- {-# DISPLAY rpi (earg  a) (abs s b) = repi  a s b #-}
-- {-# DISPLAY rpi (iarg  a) (abs s b) = ripi  a s b #-}
-- {-# DISPLAY rpi (iiarg a) (abs s b) = riipi a s b #-}

pattern _‵→_ a b = rpi (earg a) (abs "_" b)

-- "Pattern not allowed in DISPLAY pragma"
-- {-# DISPLAY rpi (earg a) (abs "_" b) = _‵→_ a b #-}

pattern ivar i = rvar i []

-- "Ambiguous constructor rvar"
-- {-# DISPLAY rvar i [] = ivar i #-}

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

vis₄ : {A : Set} -> (A -> List (Arg Term) -> Term) -> A -> Term -> Term -> Term -> Term -> Term
vis₄ k f x₁ x₂ x₃ x₄ = vis k f (x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ [])

vis₅ : {A : Set}
     -> (A -> List (Arg Term) -> Term) -> A -> Term -> Term -> Term -> Term -> Term -> Term
vis₅ k f x₁ x₂ x₃ x₄ x₅ = vis k f (x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ [])

_·_ : Term -> Term -> Term
f · x = vis₂ def (quote id) f x

argInfo : ∀ {A} -> Arg A -> _
argInfo (arg i x) = i

argVal : ∀ {A} -> Arg A -> A
argVal (arg i x) = x

unExpl : ∀ {A} -> Arg A -> Maybe A
unExpl (earg t) = just t
unExpl  _       = nothing

absName : ∀ {A} -> Abs A -> String
absName (abs s x) = s

absVal : ∀ {A} -> Abs A -> A
absVal (abs s x) = x

pvars : List String -> List (Arg Pattern)
pvars = map (earg ∘ rvar ∘ named)

record Data {α} (A : Set α) : Set α where
  no-eta-equality
  constructor packData
  field
    dataName  : Name
    parsTele  : Type
    indsTele  : Type
    consTypes : List A
    consNames : All (const Name) consTypes
open Data public

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
    { reify = Nat.fold (quoteTerm 0) (vis₁ con (quote suc))
    }

  ListReify : ∀ {α} {A : Set α} {{aReify : Reify A}} -> Reify (List A)
  ListReify = record
    { reify = foldr (vis₂ con (quote _∷_) ∘ reify) (quoteTerm (List Term ∋ []))
    }  

  AllReify : ∀ {α β} {A : Set α} {B : A -> Set β} {xs} {{bReify : ∀ {x} -> Reify (B x)}}
           -> Reify (All B xs)
  AllReify {B = B} {{bReify}} = record
    { reify = go _
    } where
        go : ∀ xs -> All B xs -> Term
        go  []       tt      = def (quote tt₀) []
        go (x ∷ xs) (y , ys) = vis₂ con (quote _,_) (reify {{bReify}} y) (go xs ys)

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

keep : (ℕ -> ℕ) -> ℕ -> ℕ
keep ι  0      = 0
keep ι (suc n) = suc (ι n)

{-# TERMINATING #-}
mutual
  ren : (ℕ -> ℕ) -> Term -> Term
  ren ι (rvar v xs)     = rvar (ι v) (rens ι xs)
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

shift : Term -> Term
shift = shiftBy 1

unshiftBy : ℕ -> Term -> Term
unshiftBy n = ren (_∸ n)

unshift′ : Term -> Term
unshift′ t = elam "_" t · def (quote tt₀) []

isSomeName : Name -> Term -> Bool
isSomeName n (def m _) = n == m
isSomeName n (con m _) = n == m
isSomeName n  t        = false

explsOnly : List (Arg Term) -> List Term
explsOnly = mapMaybe unExpl

takePis : ℕ -> Type -> Maybe Type
takePis  0       a          = just unknown
takePis (suc n) (api a s b) = rpi a ∘ abs s <$> takePis n b
takePis  _       _          = nothing

dropPis : ℕ -> Type -> Maybe Type
dropPis  0       a          = just a
dropPis (suc n) (api a s b) = dropPis n b
dropPis  _       _          = nothing

appendType : Type -> Type -> Type
appendType (api a s b) c = api a s (appendType b c)
appendType  _          c = c

elamsBy : Type -> Term -> Term
elamsBy (aepi a s b) t = elam s (elamsBy b t)
elamsBy (api  _ s b) t = elamsBy b t
elamsBy  _           t = t

resType : Type -> Type
resType = go 0 where
  go : ℕ -> Type -> Type
  go n (api a s b) = go (suc n) b
  go n  a          = unshiftBy n a

implPis : Type -> Type
implPis (aepi  a        s b) = aipi a        s (implPis b)
implPis (api  (arg i a) s b) = api (arg i a) s (implPis b)
implPis  b                   = b

leadImpls : Type -> List (Abs Term)
leadImpls (rpi (iarg a) (abs s b)) = abs s a ∷ leadImpls b
leadImpls  a                       = []

pisToAbsArgTypes : Type -> List (Abs (Arg Type))
pisToAbsArgTypes (api a s b) = abs s a ∷ pisToAbsArgTypes b
pisToAbsArgTypes  b          = []

episToAbsTypes : Type -> List (Abs Type)
episToAbsTypes (aepi a s b) = abs s a ∷ episToAbsTypes b
episToAbsTypes (api  _ s b) = episToAbsTypes b
episToAbsTypes  b           = []

episToNames : Type -> List String
episToNames = map absName ∘ episToAbsTypes

countPis : Type -> ℕ
countPis = length ∘ pisToAbsArgTypes

countEPis : Type -> ℕ
countEPis = length ∘ episToAbsTypes

pisToAbsArgVars : ℕ -> Type -> List (Abs (Arg Term))
pisToAbsArgVars (suc n) (api (arg i a) s b) = abs s (arg i (ivar n)) ∷ pisToAbsArgVars n b
pisToAbsArgVars  n       b                  = []

pisToArgVars : ℕ -> Type -> List (Arg Term)
pisToArgVars = map absVal % ∘ pisToAbsArgVars

episToAbsVars : ℕ -> Type -> List (Abs Term)
episToAbsVars (suc n) (aepi a s b) = abs s (ivar n) ∷ episToAbsVars n b
episToAbsVars (suc n) (api  _ s b) = episToAbsVars n b
episToAbsVars  n       b           = []

{-# TERMINATING #-}
mutual
  mapName : (ℕ -> List (Arg Term) -> Term) -> Name -> Term -> Term
  mapName f n (rvar v xs)     = rvar v (mapNames f n xs)
  mapName f n (con m xs)      =
    (if n == m then f 0 else Term.con m) (mapNames f n xs)
  mapName f n (def m xs)      =
    (if n == m then f 0 else Term.def m) (mapNames f n xs)
  mapName f n (rlam v t)      = rlam v (mapName (f ∘ suc) n <$> t)
  mapName f n (pat-lam cs xs) = undefined where postulate undefined : _
  mapName f n (rpi a b)       = rpi (mapName f n <$> a) (mapName (f ∘ suc) n <$> b)
  mapName f n (sort s)        = sort (mapNameSort f n s)
  mapName f n (lit l)         = lit l
  mapName f n (meta x xs)     = meta x (mapNames f n xs)
  mapName f n  unknown        = unknown

  mapNames : (ℕ -> List (Arg Term) -> Term) -> Name -> List (Arg Term) -> List (Arg Term)
  mapNames f n = map (fmap (mapName f n))

  mapNameSort : (ℕ -> List (Arg Term) -> Term) -> Name -> Sort -> Sort
  mapNameSort f n (set t) = set (mapName f n t)
  mapNameSort f n (lit l) = lit l
  mapNameSort f n unknown = unknown

toTuple : List Term -> Term
toTuple = foldr₁ (vis₂ con (quote _,_)) (def (quote tt₀) [])

curryBy : Type -> Term -> Term
curryBy = go 0 where
  go : ℕ -> Type -> Term -> Term
  go n (api (arg (arg-info v r) a) s b) t = rlam v ∘ abs s $ go (suc n) b t
  go n  _                               t = shiftBy n t · toTuple (map ivar (downFrom n))

euncurryBy : Type -> Term -> Term
euncurryBy a f = elam "x" $ def (quote id) (earg (shift f) ∷ go a (ivar 0)) where
  go : Term -> Term -> List (Arg Term)
  go (aepi a s b@(rpi _ _)) p = earg (vis₁ def (quote proj₁) p) ∷ go b (vis₁ def (quote proj₂) p)
  go (api  _ s b@(rpi _ _)) p = go b (vis₁ def (quote proj₂) p)
  go (aepi a _ _)           x = earg x ∷ []
  go  _                     t = []

throw : ∀ {α} {A : Set α} -> String -> TC A
throw s = typeError (strErr s ∷ [])

panic : ∀ {α} {A : Set α} -> String -> TC A
panic s = throw $ "panic: " ++ˢ s

defineSimpleFun : Name -> Term -> TC _
defineSimpleFun n t = defineFun n (clause [] t ∷ [])

-- Able to normalize a Setω.
normalize : Term -> TC Term
normalize (api (arg v a) s b) =
  (λ na -> api (arg v na) s) <$> normalize a <*> extendContext (arg v a) (normalize b)
normalize  t                  = normalise t

getData : Name -> TC (Data Type)
getData d = getType d >>= λ ab -> getDefinition d >>= λ
  { (data-type p cs) ->
       mapM (λ c -> _,_ c ∘ dropPis p <$> (getType c >>= normalize)) cs >>= λ mans ->
         case takePis p ab ⊗ (dropPis p ab ⊗ (mapM (uncurry λ c ma -> flip _,_ c <$> ma) mans)) of λ
           {  nothing             -> panic "getData: data"
           ; (just (a , b , acs)) -> return ∘ uncurry (packData d a b) $ splitList acs
           }
  ; (record′ c)      -> getType c >>= λ a -> case dropPis (countPis ab) a of λ
       {  nothing  -> panic "getData: record"
       ; (just a′) -> return $ packData d ab unknown (a′ ∷ []) (c , tt)
       }
  ;  _               -> throw "not a data"
  }

macro
  TypeOf : Term -> Term -> TC _
  TypeOf t ?r = inferType t >>= unify ?r
