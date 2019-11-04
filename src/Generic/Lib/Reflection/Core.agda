module Generic.Lib.Reflection.Core where

open import Reflection
  renaming (visible to expl; hidden to impl; instance′ to inst;
    relevant to rel; irrelevant to irr; pi to absPi; lam to absLam; def to appDef)
  hiding (var; con; meta; _≟_; return; _>>=_; _>>_) public
open import Agda.Builtin.Reflection using (withNormalisation) public
open Term    using () renaming (var to appVar; con to appCon; meta to appMeta) public
open Pattern using () renaming (var to patVar; con to patCon) public
open Literal using () renaming (meta to litMeta) public

open import Generic.Lib.Intro
open import Generic.Lib.Equality.Propositional
open import Generic.Lib.Decidable
open import Generic.Lib.Category
open import Generic.Lib.Data.Nat
open import Generic.Lib.Data.String
open import Generic.Lib.Data.Maybe
open import Generic.Lib.Data.Product
open import Generic.Lib.Data.List

open import Data.Vec using (toList)
open import Data.Vec.N-ary using (N-ary; curryⁿ)

infixr 5 _‵→_
infixl 3 _·_

listCurryⁿ : ∀ {α β} {A : Set α} {B : Set β} n -> (List A -> B) -> N-ary n A B
listCurryⁿ n f = curryⁿ {n = n} (f ∘ toList)

named : String -> String
named s = if s == "_" then "x" else s

record Reify {α} (A : Set α) : Set α where
  field reify : A -> Term

  macro
    reflect : A -> Term -> TC _
    reflect = unify ∘ reify
open Reify {{...}} public

pattern pureVar  n = appVar  n []
pattern pureCon  c = appCon  c []
pattern pureDef  f = appDef  f []
pattern pureMeta m = appMeta m []

{-# DISPLAY appVar  i [] = pureVar  i #-}
{-# DISPLAY appCon  c [] = pureCon  c #-}
{-# DISPLAY appDef  f [] = pureDef  f #-}
{-# DISPLAY appMeta m [] = pureMeta m #-}

pattern explInfo r = arg-info expl r
pattern implInfo r = arg-info impl r
pattern instInfo r = arg-info inst r

{-# DISPLAY arg-info expl r = explInfo r #-}
{-# DISPLAY arg-info impl r = implInfo r #-}
{-# DISPLAY arg-info inst r = instInfo r #-}

pattern explRelInfo = explInfo rel
pattern explIrrInfo = explInfo irr
pattern implRelInfo = implInfo rel
pattern implIrrInfo = implInfo irr
pattern instRelInfo = instInfo rel
pattern instIrrInfo = instInfo irr

{-# DISPLAY explInfo rel = explRelInfo #-}
{-# DISPLAY explInfo irr = explIrrInfo #-}
{-# DISPLAY implInfo rel = implRelInfo #-}
{-# DISPLAY implInfo irr = implIrrInfo #-}
{-# DISPLAY instInfo rel = instRelInfo #-}
{-# DISPLAY instInfo irr = instIrrInfo #-}

pattern explArg r x = arg (explInfo r) x
pattern implArg r x = arg (implInfo r) x
pattern instArg r x = arg (instInfo r) x

{-# DISPLAY arg (explInfo r) = explArg r #-}
{-# DISPLAY arg (implInfo r) = implArg r #-}
{-# DISPLAY arg (instInfo r) = instArg r #-}

pattern explRelArg x = explArg rel x
pattern implRelArg x = implArg rel x
pattern instRelArg x = instArg rel x

{-# DISPLAY explArg rel x = explRelArg x #-}
{-# DISPLAY implArg rel x = implRelArg x #-}
{-# DISPLAY instArg rel x = instRelArg x #-}

pattern pi s a b = absPi a (abs s b)

{-# DISPLAY absPi a (abs s b) = pi s a b #-}

pattern explPi r s a b = pi s (explArg r a) b
pattern implPi r s a b = pi s (implArg r a) b
pattern instPi r s a b = pi s (instArg r a) b

{-# DISPLAY pi (explArg r a) s b = explPi r s a b #-}
{-# DISPLAY pi (implArg r a) s b = implPi r s a b #-}
{-# DISPLAY pi (instArg r a) s b = instPi r s a b #-}

pattern explRelPi s a b = explPi rel a s b
pattern explIrrPi s a b = explPi irr a s b
pattern implRelPi s a b = implPi rel a s b
pattern implIrrPi s a b = implPi irr a s b
pattern instRelPi s a b = instPi rel a s b
pattern instIrrPi s a b = instPi irr a s b

{-# DISPLAY explPi rel a s b = explRelPi s a b #-}
{-# DISPLAY explPi irr a s b = explIrrPi s a b #-}
{-# DISPLAY implPi rel a s b = implRelPi s a b #-}
{-# DISPLAY implPi irr a s b = implIrrPi s a b #-}
{-# DISPLAY instPi rel a s b = instRelPi s a b #-}
{-# DISPLAY instPi irr a s b = instIrrPi s a b #-}

pattern lam v s t = absLam v (abs s t)

{-# DISPLAY absLam v (abs s t) = lam v s t #-}

pattern explLam s t = lam expl s t
pattern implLam s t = lam impl s t
pattern instLam s t = lam inst s t

{-# DISPLAY lam expl s t = explLam s t #-}
{-# DISPLAY lam impl s t = implLam s t #-}
{-# DISPLAY lam inst s t = instLam s t #-}

pattern _‵→_ a b = pi "_" (explRelArg a) b

-- No longer parses for whatever reason.
-- {-# DISPLAY pi "_" (explRelArg a) b = a ‵→ b #-}

mutual
  <_>_ : ∀ {α} -> Relevance -> Set α -> Set α
  <_>_ = flip RelValue

  data RelValue {α} (A : Set α) : Relevance -> Set α where
    relv :  A -> < rel > A
    irrv : .A -> < irr > A

elimRelValue : ∀ {r α π} {A : Set α}
             -> (P : ∀ {r} -> < r > A -> Set π)
             -> (∀  x -> P (relv x))
             -> (∀ .x -> P (irrv x))
             -> (x : < r > A)
             -> P x
elimRelValue P f g (relv x) = f x
elimRelValue P f g (irrv x) = g x

unrelv : ∀ {α} {A : Set α} -> < rel > A -> A
unrelv (relv x) = x

-- Is it possible to handle this in some other way that doesn't require a postulate?
-- See the `appRel` function below. Or is the postulate fine?
postulate
  .unirrv : ∀ {α} {A : Set α} -> < irr > A -> A

<_>_~>_ : ∀ {α β} -> Relevance -> Set α -> Set β -> Set (α ⊔ β)
< rel > A ~> B =  A -> B
< irr > A ~> B = .A -> B

lamRel : ∀ {r α β} {A : Set α} {B : Set β} -> (< r > A -> B) -> < r > A ~> B
lamRel {rel} f = λ x -> f (relv x)
lamRel {irr} f = λ x -> f (irrv x)

-- The laziness is intentional.
appRel : ∀ {r α β} {A : Set α} {B : Set β} -> (< r > A ~> B) -> < r > A -> B
appRel {rel} f rx = f (unrelv rx)
appRel {irr} f rx = f (unirrv rx)

Pi : ∀ {α β} i -> (A : Set α) -> (< relevance i > A -> Set β) -> Set (α ⊔ β)
Pi explRelInfo A B =   (x : A)  -> B (relv x)
Pi explIrrInfo A B = . (x : A)  -> B (irrv x)
Pi implRelInfo A B =   {x : A}  -> B (relv x)
Pi implIrrInfo A B = . {x : A}  -> B (irrv x)
Pi instRelInfo A B =  {{x : A}} -> B (relv x)
Pi instIrrInfo A B = .{{x : A}} -> B (irrv x)

lamPi : ∀ {α β} {A : Set α} i {B : < relevance i > A -> Set β} -> (∀ x -> B x) -> Pi i A B
lamPi explRelInfo f = λ x -> f (relv x)
lamPi explIrrInfo f = λ x -> f (irrv x)
lamPi implRelInfo f = f _
lamPi implIrrInfo f = f _
lamPi instRelInfo f = f _
lamPi instIrrInfo f = f _

appPi : ∀ {α β} {A : Set α} i {B : < relevance i > A -> Set β} -> Pi i A B -> ∀ x -> B x
appPi explRelInfo f (relv x) = f x
appPi explIrrInfo f (irrv x) = f x
appPi implRelInfo y (relv x) = y
appPi implIrrInfo y (irrv x) = y
appPi instRelInfo y (relv x) = y {{x}}
appPi instIrrInfo y (irrv x) = y {{x}}

RelEq : ∀ {α} -> Relevance -> Set α -> Set α
RelEq rel A = Eq A
RelEq irr A = ⊤

vis : {A : Set} -> (A -> List (Arg Term) -> Term) -> A -> List Term -> Term
vis k x = k x ∘ map explRelArg

vis# : ∀ {A : Set} n -> (A -> List (Arg Term) -> Term) -> A -> N-ary n Term Term
vis# n k = listCurryⁿ n ∘ vis k

isRelevant : Relevance -> Bool
isRelevant rel = true
isRelevant irr = false

argInfo : ∀ {α} {A : Set α} -> Arg A -> _
argInfo (arg i x) = i

argVal : ∀ {α} {A : Set α} -> Arg A -> A
argVal (arg i x) = x

unExpl : ∀ {α} {A : Set α} -> Arg A -> Maybe A
unExpl (explArg r x) = just x
unExpl  _            = nothing

absName : ∀ {α} {A : Set α} -> Abs A -> String
absName (abs s x) = s

absVal : ∀ {α} {A : Set α} -> Abs A -> A
absVal (abs s x) = x

patVars : List String -> List (Arg Pattern)
patVars = map (explRelArg ∘ patVar ∘ named)

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

  EqRelValue : ∀ {α r} {A : Set α} {{aEq : RelEq r A}} -> Eq (< r > A)
  EqRelValue {A = A} {{aEq}} = record
    { _≟_ = go
    } where
        relv-inj : {x y : A} -> relv x ≡ relv y -> x ≡ y
        relv-inj refl = refl

        go : ∀ {r} {{aEq : RelEq r A}} -> IsSet (< r > A)
        go (relv x) (relv y) = dcong relv relv-inj (x ≟ y)
        go (irrv x) (irrv y) = yes refl

  ArgFunctor : ∀ {α} -> RawFunctor {α} Arg
  ArgFunctor = record
    { _<$>_ = λ{ f (arg i x) -> arg i (f x) }
    }

  AbsFunctor : ∀ {α} -> RawFunctor {α} Abs
  AbsFunctor = record
    { _<$>_ = λ{ f (abs s x) -> abs s (f x) }
    }

  TCMonad : ∀ {α} -> RawMonad {α} TC
  TCMonad = record
    { return = Reflection.return
    ; _>>=_  = Reflection._>>=_
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
  ren ι (appVar v xs)   = appVar (ι v) (rens ι xs)
  ren ι (appCon c xs)   = appCon c (rens ι xs)
  ren ι (appDef f xs)   = appDef f (rens ι xs)
  ren ι (lam v s t)     = lam v s (ren (keep ι) t)
  ren ι (pat-lam cs xs) = undefined where postulate undefined : _
  ren ι (pi s a b)      = pi s (ren ι <$> a) (ren (keep ι) b)
  ren ι (sort s)        = sort (renSort ι s)
  ren ι (lit l)         = lit l
  ren ι (appMeta x xs)  = appMeta x (rens ι xs)
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

isSomeName : Name -> Term -> Bool
isSomeName n (appDef m _) = n == m
isSomeName n (appCon m _) = n == m
isSomeName n  t           = false

{-# TERMINATING #-}
mutual
  mapName : (ℕ -> List (Arg Term) -> Term) -> Name -> Term -> Term
  mapName f n (appVar v xs)   = appVar v (mapNames f n xs)
  mapName f n (appCon m xs)   = (if n == m then f 0 else appCon m) (mapNames f n xs)
  mapName f n (appDef m xs)   = (if n == m then f 0 else appDef m) (mapNames f n xs)
  mapName f n (lam v s t)     = lam v s (mapName (f ∘ suc) n t)
  mapName f n (pat-lam cs xs) = undefined where postulate undefined : _
  mapName f n (pi s a b)      = pi s (mapName f n <$> a) (mapName (f ∘ suc) n b)
  mapName f n (sort s)        = sort (mapNameSort f n s)
  mapName f n (lit l)         = lit l
  mapName f n (appMeta x xs)  = appMeta x (mapNames f n xs)
  mapName f n  unknown        = unknown

  mapNames : (ℕ -> List (Arg Term) -> Term) -> Name -> List (Arg Term) -> List (Arg Term)
  mapNames f n = map (fmap (mapName f n))

  mapNameSort : (ℕ -> List (Arg Term) -> Term) -> Name -> Sort -> Sort
  mapNameSort f n (set t) = set (mapName f n t)
  mapNameSort f n (lit l) = lit l
  mapNameSort f n unknown = unknown

explsOnly : List (Arg Term) -> List Term
explsOnly = mapMaybe unExpl

initType : Type -> Type
initType (pi s a b) = pi s a (initType b)
initType  b         = unknown

lastType : Type -> Type
lastType (pi s a b) = lastType b
lastType  b         = b

-- These two should return just `Type` like everything else.
takePis : ℕ -> Type -> Maybe Type
takePis  0       a         = just unknown
takePis (suc n) (pi s a b) = pi s a <$> takePis n b
takePis  _       _         = nothing

dropPis : ℕ -> Type -> Maybe Type
dropPis  0       a         = just a
dropPis (suc n) (pi s a b) = dropPis n b
dropPis  _       _         = nothing

monoLastType : Type -> Type
monoLastType = go 0 where
  go : ℕ -> Type -> Type
  go n (pi s a b) = go (suc n) b
  go n  b         = unshiftBy n b

appendType : Type -> Type -> Type
appendType (pi s a b) c = pi s a (appendType b c)
appendType  b         c = c

explLamsBy : Type -> Term -> Term
explLamsBy (explPi r s a b) t = explLam s (explLamsBy b t)
explLamsBy (pi       s a b) t = explLamsBy b t
explLamsBy  b               t = t

implicitize : Type -> Type
implicitize (explPi r s a b) = implPi r s a (implicitize b)
implicitize (pi       s a b) = pi       s a (implicitize b)
implicitize  b               = b

leadImpls : Type -> List (Abs Term)
leadImpls (implPi r s a b) = abs s a ∷ leadImpls b
leadImpls  b               = []

pisToAbsArgTypes : Type -> List (Abs (Arg Type))
pisToAbsArgTypes (pi s a b) = abs s a ∷ pisToAbsArgTypes b
pisToAbsArgTypes  b         = []

explPisToAbsTypes : Type -> List (Abs Type)
explPisToAbsTypes (explPi r s a b) = abs s a ∷ explPisToAbsTypes b
explPisToAbsTypes (pi       s a b) = explPisToAbsTypes b
explPisToAbsTypes  b               = []

explPisToNames : Type -> List String
explPisToNames = map absName ∘ explPisToAbsTypes

countPis : Type -> ℕ
countPis = length ∘ pisToAbsArgTypes

countExplPis : Type -> ℕ
countExplPis = length ∘ explPisToAbsTypes

pisToAbsArgVars : ℕ -> Type -> List (Abs (Arg Term))
pisToAbsArgVars (suc n) (pi s (arg i a) b) = abs s (arg i (pureVar n)) ∷ pisToAbsArgVars n b
pisToAbsArgVars  n       b                 = []

pisToArgVars : ℕ -> Type -> List (Arg Term)
pisToArgVars = map absVal % ∘ pisToAbsArgVars

explPisToAbsVars : ℕ -> Type -> List (Abs Term)
explPisToAbsVars (suc n) (explPi r s a b) = abs s (pureVar n) ∷ explPisToAbsVars n b
explPisToAbsVars (suc n) (pi       s a b) = explPisToAbsVars n b
explPisToAbsVars  n       b               = []

throw : ∀ {α} {A : Set α} -> String -> TC A
throw s = typeError (strErr s ∷ [])

panic : ∀ {α} {A : Set α} -> String -> TC A
panic s = throw $ "panic: " ++ˢ s

-- I'll merge these later.
macro
  sate : Name -> Term -> TC _
  sate f ?r =
    getType f >>= λ a ->
    let res = λ app -> quoteTC (vis# (countExplPis a) app f) >>= unify ?r in
    getDefinition f >>= λ
      { (constructor′ _) -> res appCon
      ;  _               -> res appDef
      }

  sateMacro : Name -> Term -> TC _
  sateMacro f ?r =
    getType f >>= λ a ->
    quoteTC (vis# (pred (countExplPis a)) appDef f) >>= unify ?r

_·_ : Term -> Term -> Term
_·_ = sate _$_

unshift′ : Term -> Term
unshift′ t = explLam "_" t · sate tt₀

-- A note for myself: `foldℕ (sate lsuc) (sate lzero) n` is not `reify n`:
-- it's damn `lsuc` -- not `suc`.
termLevelOf : Term -> Maybe Term
termLevelOf (sort (set t)) = just t
termLevelOf (sort (lit n)) = just (foldℕ (sate lsuc) (sate lzero) n)
termLevelOf (sort unknown) = just unknown
termLevelOf _ = nothing

instance
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
        { expl -> sate expl
        ; impl -> sate impl
        ; inst -> sate inst
        }
    }

  RelevanceReify : Reify Relevance
  RelevanceReify = record
    { reify = λ
        { rel -> sate rel
        ; irr -> sate irr
        }
    }

  ArgInfoReify : Reify Arg-info
  ArgInfoReify = record
    { reify = λ{ (arg-info v r) -> sate arg-info (reify v) (reify r) }
    }

  ProdReify : ∀ {α β} {A : Set α} {B : A -> Set β}
                {{aReify : Reify A}} {{bReify : ∀ {x} -> Reify (B x)}} -> Reify (Σ A B)
  ProdReify = record
    { reify = uncurry λ x y -> sate _,_ (reify x) (reify y)
    }

  ℕReify : Reify ℕ
  ℕReify = record
    { reify = foldℕ (sate suc) (sate zero)
    }

  ListReify : ∀ {α} {A : Set α} {{aReify : Reify A}} -> Reify (List A)
  ListReify = record
    { reify = foldr (sate _∷_ ∘ reify) (sate [])
    }

  AllReify : ∀ {α β} {A : Set α} {B : A -> Set β} {xs} {{bReify : ∀ {x} -> Reify (B x)}}
           -> Reify (All B xs)
  AllReify {B = B} {{bReify}} = record
    { reify = go _
    } where
        go : ∀ xs -> All B xs -> Term
        go  []       tt      = sate tt₀
        go (x ∷ xs) (y , ys) = sate _,_ (reify {{bReify}} y) (go xs ys)

toTuple : List Term -> Term
toTuple = foldr₁ (sate _,_) (sate tt₀)

curryBy : Type -> Term -> Term
curryBy = go 0 where
  go : ℕ -> Type -> Term -> Term
  go n (pi s (arg (arg-info v r) a) b) t = lam v s $ go (suc n) b t
  go n  _                              t = shiftBy n t · toTuple (map pureVar (downFrom n))

explUncurryBy : Type -> Term -> Term
explUncurryBy a f = explLam "x" $ appDef (quote id) (explArg rel (shift f) ∷ go a (pureVar 0)) where
  go : Term -> Term -> List (Arg Term)
  go (explPi r s a b@(pi _ _ _)) p = explArg r (sate proj₁ p) ∷ go b (sate proj₂ p)
  go (pi       s a b@(pi _ _ _)) p = go b (sate proj₂ p)
  go (explPi r s a b)            x = explArg r x ∷ []
  go  _                          t = []

defineTerm : Name -> Term -> TC _
defineTerm n t =
  getType n >>= λ a ->
  defineFun n (clause (map (implRelArg ∘ patVar ∘ named ∘ absName) (leadImpls a)) t ∷ [])

-- Able to normalize a Setω.
normalize : Term -> TC Term
normalize (pi s (arg i a) b) =
  pi s ∘ arg i <$> normalize a <*> extendContext (arg i a) (normalize b)
normalize  t                 = normalise t

getNormType : Name -> TC Type
getNormType = getType >=> normalize

inferNormType : Term -> TC Type
inferNormType = inferType >=> normalize

getData : Name -> TC (Data Type)
getData d = getNormType d >>= λ ab -> getDefinition d >>= λ
  { (data-type p cs) ->
       mapM (λ c -> _,_ c ∘ dropPis p <$> getNormType c) cs >>= λ mans ->
         case takePis p ab ⊗ (dropPis p ab ⊗ (mapM (uncurry λ c ma -> flip _,_ c <$> ma) mans)) of λ
           {  nothing             -> panic "getData: data"
           ; (just (a , b , acs)) -> return ∘ uncurry (packData d a b) $ splitList acs
           }
  ; (record′ c _)    -> getNormType c >>= dropPis (countPis ab) >>> λ
       {  nothing  -> panic "getData: record"
       ; (just a′) -> return $ packData d (initType ab) (lastType ab) (a′ ∷ []) (c , tt)
       }
  ;  _               -> throw "not a data"
  }

macro
  TypeOf : Term -> Term -> TC _
  TypeOf t ?r = inferNormType t >>= unify ?r

  runTC : ∀ {α} {A : Set α} -> TC A -> Term -> TC _
  runTC a ?r = bindTC a quoteTC >>= unify ?r
