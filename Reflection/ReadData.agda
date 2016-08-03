module Generic.Reflection.ReadData where

open import Generic.Core
open import Generic.Function.FoldMono

pack₀ : List Term -> Term
pack₀ = foldr  (vis₂ con (quote _,_)) (def (quote tt₀) [])

pack₁ : List Term -> Term
pack₁ = foldr₁ (vis₂ con (quote _,_)) (def (quote tt₀) [])

curryBy : Type -> Term -> Term
curryBy = go 0 where
  go : ℕ -> Type -> Term -> Term
  go n (rpi (arg (arg-info v r) a) (abs s b)) t = rlam v ∘ abs s $ go (suc n) b t
  go n  _                                     t =
    shiftBy n t · pack₁ (map (λ m -> rvar m []) $ downFrom n)

euncurryBy : Type -> Term -> Term
euncurryBy a f = elam "x" $ def (quote id) (earg (shift f) ∷ go a (rvar 0 [])) where
  go : Term -> Term -> List (Arg Term)
  go (rpi (earg a)    (abs s b@(rpi _ _))) p = earg (vis₁ def (quote proj₁) p)
                                             ∷ go b (vis₁ def (quote proj₂) p)
  go (rpi  _          (abs s b@(rpi _ _))) p = go b (vis₁ def (quote proj₂) p)
  go (rpi (earg a) _)                      x = earg x ∷ []
  go  _                                    t = []

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
  (λ ma' b' -> maybe (λ a' -> vis₂ con (quote _⊛_) a' (unshift′ b')) (qπ v s a b') ma')
    <$> quoteHyp d p a <*> quoteDesc d p b
quoteDesc d p  t                                     = join $ quoteHyp d p t

quoteData : Name -> TC Term
quoteData d =
  getData d >>= λ{ (packData _ pt it cs ns) ->
    case mapM (quoteDesc d (countPi pt)) cs of λ
      {  nothing   -> throw "can't read a data type"
      ; (just cs′) -> (λ qpt qit -> elamsBy pt ∘′ curryBy it ∘′ vis₁ def (quote μ) $
             vis₅ con (quote packData) (reify d) qpt qit (reify cs′) (reify ns))
           <$> quoteTC pt <*> quoteTC it
      }
   }

panic : ∀ {α} {A : Set α} -> TC A
panic = throw "panic: something happened"

-- This doesn't work, because `quoteData` doesn't generate implicit lambdas,
-- because otherwise nothing would work due to the #2118 issue.
readDataTo : Name -> Name -> TC _
readDataTo d′ d = getType d >>= declareDef (earg d′)
               >> quoteData d >>= λ qd -> defineFun d′ (clause [] qd ∷ [])

macro
  readData : Name -> Term -> TC _
  readData d ?r = quoteData d >>= unify ?r

  uncoerce : ∀ {ι β} {I : Set ι} {D : Data (Desc I β)} {j} -> μ D j -> Term -> TC _
  uncoerce {D = packData n a b Ds ns} d ?r =
    quoteTC d >>= λ qd -> unify ?r ∘′ vis def (quote curryFoldMono)
      $ euncurryBy b (vis def n (replicate (countEPi a) unknown))
      ∷ qd
      ∷ map (λ n -> con n []) (allToList ns)

  readCons : Name -> Term -> TC _
  readCons c ?r = inferType ?r >>= resType >>> λ
    { (def (quote μ) as) -> case explOnly as of λ
         { (D₀@(con (quote packData) xs) ∷ _) -> case explOnly xs of λ
              { (_ ∷ _ ∷ _ ∷ Ds ∷ cs ∷ []) ->
                   unify ?r ∘′ vis₂ def (quote cons) D₀ ∘′ vis₁ def (quote proj₂)
                     ∘′ vis₁ def (quote from-just) $ vis₂ def (quote lookupAllConst) (reify c) cs
              ;  _                         -> panic
              }
         ;  _                                 -> panic
         }
    ;  _                 -> throw "can't read"
    }
