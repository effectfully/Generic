module Generic.Reflection.ReadData where

open import Generic.Core

open import Data.Unit.Base
open import Data.Maybe.Base hiding (map)

pack₀ : List Term -> Term
pack₀ = foldr  (vis₂ con (quote _,_)) (vis₀ def (quote tt₀))

pack₁ : List Term -> Term
pack₁ = foldr₁ (vis₂ con (quote _,_)) (vis₀ def (quote tt₀))

curryBy : Type -> Term -> Term
curryBy = go 0 where
  go : ℕ -> Type -> Term -> Term
  go n (rpi (arg (arg-info v r) a) (abs s b)) t = rlam v ∘ abs s $ go (suc n) b t
  go n  _                                     t =
    shiftBy n t · pack₁ (map (λ m -> rvar m []) $ downFrom n)

qπ : Visibility -> String -> Term -> Term -> Term 
qπ v s a b = vis₃ con (quote π) unknown (reify v) $
               vis₁ con (quote coerce) (vis₂ con (quote _,_) a (elam s b))

quoteHyp : Name -> ℕ -> Type -> Maybe (Maybe Term)
quoteHyp d p   (rpi (arg (arg-info v _) a) (abs s b)) =
  quoteHyp d p a >>= maybe (const nothing) (fmap (qπ v s a) <$> quoteHyp d p b)
quoteHyp d p t@(def n is)                             =
  just $ if d == n
    then just (vis₁ con (quote var) ∘′ pack₁ ∘′ map unarg ∘′ drop p $ is)
    else nothing
quoteHyp d p t                                        = just nothing

quoteDesc : Name -> ℕ -> Type -> Maybe Term
quoteDesc d p (rpi (arg (arg-info v _) a) (abs s b)) =
  (λ ma' b' -> maybe (λ a' -> vis₂ con (quote _⊛_) a' (unshift b')) (qπ v s a b') ma')
    <$> quoteHyp d p a <*> quoteDesc d p b
quoteDesc d p  t                                     = join $ quoteHyp d p t

quoteData : Name -> TC Term
quoteData d =
  getData d >>= uncurry λ p nas ->
  getType d >>= λ ab ->
    case takePi p ab ⊗ (dropPi p ab ⊗ mapM (dropPi p >=> quoteDesc d p) (map proj₂ nas)) of λ
      {  nothing            -> typeError (strErr "can't read a non-strictly positive data type" ∷ [])
      ; (just (a , b , cs)) -> return ∘′ craftLams a ∘′ curryBy b ∘′ vis₁ def (quote μ) $
          vis₄ con (quote packData) (reify d) (reify p) (reify cs) (pack₀ (map (reify ∘ proj₁) nas))
      }

macro
  readData : Name -> Term -> TC _
  readData d ?r = quoteData d >>= unify ?r
