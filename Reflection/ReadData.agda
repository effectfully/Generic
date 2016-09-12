module Generic.Reflection.ReadData where

open import Generic.Core
open import Generic.Function.FoldMono

‵π : Arg-info -> String -> Term -> Term -> Term 
‵π i s a b = sate π (reify i) unknown ∘ sate coerce ∘ sate _,_ a $
  appDef (quote appᵣ) (implRelArg (reify (relevance i)) ∷ explRelArg (explLam s b) ∷ [])

quoteHyp : Name -> ℕ -> Type -> Maybe (Maybe Term)
quoteHyp d p   (pi s (arg i a) b) =
  quoteHyp d p a >>= maybe (const nothing) (fmap (‵π i s a) <$> quoteHyp d p b)
quoteHyp d p t@(appDef n is)      = just $ d == n ?> sate var ∘ toTuple ∘ map argVal ∘ drop p $ is
quoteHyp d p t                    = just nothing

quoteDesc : Name -> ℕ -> Type -> Maybe Term
quoteDesc d p (pi s (arg i a) b) =
  (λ ma' b' -> maybe (λ a' -> sate _⊛_ a' (unshift′ b')) (‵π i s a b') ma')
    <$> quoteHyp d p a <*> quoteDesc d p b
quoteDesc d p  t                 = join $ quoteHyp d p t

-- Move it to the lib.
levelOf : Term -> Maybe Term
levelOf (sort (set t)) = just t
levelOf (sort (lit n)) = just (fold ℕ _ (sate lzero) (sate lsuc) n)
levelOf (sort unknown) = just unknown
levelOf  _             = nothing

-- We didn't need that `β` previously. Why do we need it now?
-- Or, perhaps, why didn't we need it earlier? It kinda makes sense.
quoteData : Name -> TC Term
quoteData d =
  getData d >>= λ{ (packData _ a b cs ns) ->
      case levelOf (resType b) ⊗ mapM (quoteDesc d (countPis a)) cs of λ
        {  nothing         -> throw "can't read a data type"
        ; (just (β , cs′)) -> (λ qa qb -> explLamsBy a ∘ curryBy b ∘ appDef (quote μ)
               $ implRelArg unknown
               ∷ implRelArg β
               ∷ explRelArg (sate packData (reify d) qa qb (reify cs′) (reify ns))
               ∷ [])
             <$> quoteTC a <*> quoteTC b
        }
    }

-- This doesn't work, because `quoteData` doesn't generate implicit lambdas,
-- because otherwise nothing would work due to the #2118 issue.
readDataTo : Name -> Name -> TC _
readDataTo d′ d = getType d >>= declareDef (explRelArg d′)
               >> quoteData d >>= λ qd -> defineSimpleFun d′ qd

onFinalMu : ∀ {α} {A : Set α} -> (∀ {ι β} {I : Set ι} -> Data (Desc I β) -> TC A) -> Type -> TC A
onFinalMu k a = case resType a of λ
  { (appDef (quote μ) (implRelArg qι ∷ implRelArg qβ ∷ implRelArg qI ∷ explRelArg qD ∷ _)) ->
       bindTC (unquoteTC qι) λ ι ->
       bindTC (unquoteTC qβ) λ β ->
       bindTC (unquoteTC qI) λ (I : Set ι) ->
       bindTC (unquoteTC qD) λ (D : Data (Desc I β)) -> k D
  ;  _                                                          ->
       throw "the return type must be μ"
  }

macro
  readData : Name -> Term -> TC _
  readData d ?r = quoteData d >>= unify ?r

  gcoerce : Name -> Term -> TC _
  gcoerce fd ?r = inferType ?r >>= onFinalMu λ{ D@(packData _ _ b _ _) ->
      quoteTC (μ D) >>= λ μD ->
      traverseAll quoteTC (allCons D) >>= λ cs′ ->
      unify ?r $ vis appDef fd (curryBy b μD ∷ allToList cs′)
    }

  guncoerce : ∀ {ι β} {I : Set ι} {D : Data (Desc I β)} {j} -> μ D j -> Term -> TC _
  guncoerce {D = packData d a b cs ns} e ?r =
    quoteTC e >>= λ qe -> unify ?r ∘ vis appDef (quote curryFoldMono) $
      explUncurryBy b (vis appDef d (replicate (countExplPis a) unknown)) ∷ qe ∷ unmap (λ n -> appCon n []) ns
