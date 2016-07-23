module Generic.Reflection.ReadData where

open import Generic.Core hiding (⊤; tt; pi; ipi; lam; apply)

open import Data.Unit.Base
open import Data.Bool.Base
open import Data.String.Base
open import Data.Maybe.Base hiding (map)
import Data.Maybe as Maybe
open import Data.List.Base hiding ([_])
import Data.List as List
open import Category.Monad
open import Reflection

open RawMonad {{...}} renaming (_⊛_ to _<*>_)

infixl 3 _·_

fmap = _<$>_

mapM : ∀ {α β} {A : Set α} {B : Set β} {M : Set β -> Set β} {{mMonad : RawMonad M}}
     -> (A -> M B) -> List A -> M (List B)
mapM {{mMonad}} = List.mapM mMonad

module _ where
  import Relation.Binary.PropositionalEquality as B

  liftBase : ∀ {α} {A : Set α} {x y : A} -> x B.≡ y -> x ≡ y
  liftBase B.refl = refl

  lowerBase : ∀ {α} {A : Set α} {x y : A} -> x ≡ y -> x B.≡ y
  lowerBase refl = B.refl

  viaBase : ∀ {α} {A : Set α} -> Decidable (B._≡_ {A = A}) -> Eq A
  viaBase d = record
    { _≟_ = flip (via-injection {A = ≡-Setoid _} {B = B.setoid _}) d $ record
      { to = record
        { _⟨$⟩_ = id
        ; cong  = lowerBase
        }
      ; injective = liftBase
      }
    }

instance
  NameEq : Eq Name
  NameEq = viaBase _≟-Name_

  MaybeMonad : ∀ {α} -> RawMonad {α} Maybe
  MaybeMonad = Maybe.monad

  TCMonad : ∀ {α} -> RawMonad {α} TC
  TCMonad = record
    { return = returnTC
    ; _>>=_  = bindTC
    }

getData : Name -> TC (ℕ × List Type)
getData d = getDefinition d >>= λ
  { (data-type n cs) -> _,_ n <$> mapM getType cs
  ;  _               -> typeError (strErr "not a data" ∷ [])
  }

postulate
  undefined : ∀ {α} {A : Set α} -> A

trustFromJust : ∀ {α} {A : Set α} -> Maybe A -> A
trustFromJust (just x) = x
trustFromJust  nothing = undefined

isVisible : Arg-info -> Bool
isVisible (arg-info visible   _) = true
isVisible (arg-info hidden    _) = false
isVisible (arg-info instance′ _) = undefined

pattern varg x = arg (arg-info visible relevant) x
{-# DISPLAY arg (arg-info visible relevant) = varg #-}

pattern harg x = arg (arg-info hidden  relevant) x
{-# DISPLAY arg (arg-info hidden  relevant) = harg #-}

visibles : List Term -> List (Arg Term)
visibles = map (arg (arg-info visible relevant))

vis : {A : Set} -> (A -> List (Arg Term) -> Term) -> A -> List Term -> Term
vis k x = k x ∘ visibles

vlam : String -> Term -> Term
vlam s = lam visible ∘ abs s

_·_ : Term -> Term -> Term
f · x = vis def (quote id) $ f ∷ x ∷ []

unshift : Term -> Term
unshift t = vlam "_" t · quoteTerm tt

takePi : ℕ -> Type -> Maybe Type
takePi  0       a               = just unknown
takePi (suc n) (pi a (abs s b)) = pi a ∘ abs s <$> takePi n b
takePi  _       _               = nothing

dropPi : ℕ -> Type -> Maybe Type
dropPi  0       a               = just a
dropPi (suc n) (pi a (abs s b)) = dropPi n b
dropPi  _       _               = nothing

craftLams : Type -> Term -> Term
craftLams (pi (varg a ) (abs s b)) t = vlam s (craftLams b t)
craftLams (pi  _        (abs s b)) t = craftLams b t
craftLams  _                       t = t

quoteBool : Bool -> Term
quoteBool b = if b then quoteTerm true else quoteTerm false

quoteList : List Term -> Term
quoteList = foldr (λ x r -> vis con (quote _∷_) $ x ∷ r ∷ []) (quoteTerm (List Term ∋ []))

qπ : Arg-info -> String -> Term -> Term -> Term 
qπ i s a b = vis con (quote π)
           $ unknown
           ∷ quoteBool (isVisible i)
           ∷ vis con (quote coerce) (vis con (quote _,_) (a ∷ vlam s b ∷ []) ∷ [])
           ∷ []

quoteHyp : Name -> Type -> Maybe (Maybe Term)
quoteHyp d   (pi (arg i a) (abs s b)) =
  quoteHyp d a >>= maybe (const nothing) (fmap (qπ i s a) <$> quoteHyp d b)
quoteHyp d t@(def n _)                =
  just $ if d == n then just (def (quote pos) []) else nothing
quoteHyp d t                          = just nothing

quoteCons : Name -> Type -> Maybe Term
quoteCons d (pi (arg i a) (abs s b)) =
  (λ ma' b' -> maybe (λ a' -> vis con (quote _⊛_) $ a' ∷ unshift b' ∷ []) (qπ i s a b') ma')
    <$> quoteHyp d a <*> quoteCons d b
quoteCons d  t                       = join $ quoteHyp d t

quoteData : Name -> TC Term
quoteData d = getData d >>= uncurry λ n as ->
  case mapM (quoteCons d ∘′ trustFromJust ∘′ dropPi n) as of λ
    {  nothing  -> typeError (strErr "failed" ∷ [])
    ; (just ts) -> (λ b -> craftLams (trustFromJust (takePi n b)) $
                        vis def (quote μ′) (quoteList ts ∷ []))
                      <$> getType d
    }

-- unquote (unify (from-just (quoteCons (quote ℕ) (quoteTerm ℕ))))

-- case initLast ts of λ
--         {  []         -> typeError (strErr "I'll fix this" ∷ [])
--         ; (ts' ∷ʳ' t) -> (λ b -> craftLams (trustFromJust (takePi n b)) $
--               vis def (quote μ′) $ foldr (λ t s -> vis con (quote _⊕_) (t ∷ s ∷ [])) t ts' ∷ [])
--             <$> getType d
--         }
--     }

macro
  readData : Name -> Term -> TC ⊤
  readData d ?r = quoteData d >>= unify ?r
