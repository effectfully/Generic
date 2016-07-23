module Generic.Reflection.ReadData where

open import Generic.Core

open import Data.Unit.Base
open import Data.Maybe.Base hiding (map)

postulate
  undefined : ∀ {α} {A : Set α} -> A

trustFromJust : ∀ {α} {A : Set α} -> Maybe A -> A
trustFromJust (just x) = x
trustFromJust  nothing = undefined

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

getData : Name -> TC (ℕ × List Type)
getData = getDefinition >=> λ
  { (data-type n cs) -> _,_ n <$> mapM getType cs
  ;  _               -> typeError (strErr "not a data" ∷ [])
  }

qπ : Visibility -> String -> Term -> Term -> Term 
qπ v s a b = vis con (quote π)
           $ unknown
           ∷ deepQuote v
           ∷ vis con (quote coerce) (vis con (quote _,_) (a ∷ elam s b ∷ []) ∷ [])
           ∷ []

quoteHyp : Name -> Type -> Maybe (Maybe Term)
quoteHyp d   (rpi (arg (arg-info v _) a) (abs s b)) =
  quoteHyp d a >>= maybe (const nothing) (fmap (qπ v s a) <$> quoteHyp d b)
quoteHyp d t@(def n _)                              =
  just $ if d == n then just (def (quote pos) []) else nothing
quoteHyp d t                                        = just nothing

quoteCons : Name -> Type -> Maybe Term
quoteCons d (rpi (arg (arg-info v _) a) (abs s b)) =
  (λ ma' b' -> maybe (λ a' -> vis con (quote _⊛_) $ a' ∷ unshift b' ∷ []) (qπ v s a b') ma')
    <$> quoteHyp d a <*> quoteCons d b
quoteCons d  t                                     = join $ quoteHyp d t

quoteData : Name -> TC Term
quoteData d = getData d >>= uncurry λ n as ->
  case mapM (quoteCons d ∘′ trustFromJust ∘′ dropPi n) as of λ
    {  nothing  -> typeError (strErr "failed" ∷ [])
    ; (just ts) -> (λ b -> craftLams (trustFromJust (takePi n b)) $
                        vis def (quote μ′) (deepQuote ts ∷ []))
                      <$> getType d
    }

macro
  readData : Name -> Term -> TC _
  readData d ?r = quoteData d >>= unify ?r
