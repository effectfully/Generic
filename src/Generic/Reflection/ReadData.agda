module Generic.Reflection.ReadData where

open import Generic.Core
open import Generic.Function.FoldMono

‵π : Arg-info -> String -> Term -> Term -> Term
‵π i s a b = sate π (reify i) (sate refl) ∘ sate coerce ∘ sate _,_ a $
  appDef (quote appRel) (implRelArg (reify (relevance i)) ∷ explRelArg (explLam s b) ∷ [])

quoteHyp : Name -> ℕ -> Type -> Maybe (Maybe Term)
quoteHyp d p   (pi s (arg i a) b) =
  quoteHyp d p a >>= maybe (const nothing) (fmap (‵π i s a) <$> quoteHyp d p b)
quoteHyp d p t@(appDef n is)      = just $ d == n ?> sate var (toTuple ∘ map argVal $ drop p is)
quoteHyp d p t                    = just nothing

quoteDesc : Name -> ℕ -> Type -> Maybe Term
quoteDesc d p (pi s (arg i a) b) =
  (λ ma' b' -> maybe (λ a' -> sate _⊛_ a' (unshift′ b')) (‵π i s a b') ma')
    <$> quoteHyp d p a <*> quoteDesc d p b
quoteDesc d p  t                 = join $ quoteHyp d p t

-- We didn't need that `β` previously. Why do we need it now?
-- Or, perhaps, why didn't we need it earlier? It kinda makes sense.
quoteData : Data Type -> TC Term
quoteData (packData d a b cs ns) =
  case termLevelOf (monoLastType b) ⊗ mapM (quoteDesc d (countPis a)) cs of λ
    {  nothing         -> throw "can't read a data type"
    ; (just (β , cs′)) -> (λ qa qb -> explLamsBy a ∘ curryBy b ∘ appDef (quote μ)
           $ implRelArg unknown
           ∷ implRelArg β
           ∷ explRelArg (sate packData (reify d) qa qb (reify cs′) (reify ns))
           ∷ [])
         <$> quoteTC a <*> quoteTC b
    }

onFinalMu : ∀ {α} {A : Set α} -> (∀ {ι β} {I : Set ι} -> Data (Desc I β) -> TC A) -> Type -> TC A
onFinalMu k = monoLastType >>> λ
  { (appDef (quote μ) (implRelArg qι ∷ implRelArg qβ ∷ implRelArg qI ∷ explRelArg qD ∷ _)) ->
       bindTC (unquoteTC qι) λ ι ->
       bindTC (unquoteTC qβ) λ β ->
       bindTC (unquoteTC qI) λ I ->
       bindTC (unquoteTC qD) λ D -> k {ι} {β} {I} D
  ;  _                                                                                     ->
       throw "the return type must be μ"
  }

guncoercePure : Data Type -> Term
guncoercePure (packData d a b cs ns) = explLam "x" ∘ vis appDef (quote curryFoldMono)
  $ explUncurryBy b (vis appDef d (replicate (countExplPis a) unknown))
  ∷ pureVar 0
  ∷ unmap pureCon ns

macro
  readData : Name -> Term -> TC _
  readData d ?r = getData d >>= quoteData >>= unify ?r

  gcoerce : Name -> Term -> TC _
  gcoerce fd ?r = inferNormType ?r >>= onFinalMu λ{ D@(packData _ _ b _ _) ->
      quoteTC (μ D) >>= λ μD ->
      traverseAll quoteTC (allCons D) >>= λ cs′ ->
      unify ?r $ vis appDef fd (curryBy b μD ∷ allToList cs′)
    }

  guncoerce : ∀ {ι β} {I : Set ι} {D : Data (Desc I β)} {j} -> μ D j -> Term -> TC _
  guncoerce {D = packData d a b cs ns} e ?r =
    quoteTC e >>= λ qe -> unify ?r ∘ vis appDef (quote curryFoldMono)
      $ explUncurryBy b (vis appDef d (replicate (countExplPis a) unknown))
      ∷ qe
      ∷ unmap pureCon ns
