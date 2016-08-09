module Generic.Reflection.ReadData where

open import Generic.Core
open import Generic.Function.FoldMono

‵π : Visibility -> String -> Term -> Term -> Term 
‵π v s a b = vis₃ con (quote π) unknown (reify v) $
               vis₁ con (quote coerce) (vis₂ con (quote _,_) a (elam s b))

quoteHyp : Name -> ℕ -> Type -> Maybe (Maybe Term)
quoteHyp d p   (rpi (arg (arg-info v _) a) (abs s b)) =
  quoteHyp d p a >>= maybe (const nothing) (fmap (‵π v s a) <$> quoteHyp d p b)
quoteHyp d p t@(def n is)                             =
  just $ if d == n
    then just (vis₁ con (quote var) ∘ toTuple ∘ map argVal ∘ drop p $ is)
    else nothing
quoteHyp d p t                                        = just nothing

quoteDesc : Name -> ℕ -> Type -> Maybe Term
quoteDesc d p (rpi (arg (arg-info v _) a) (abs s b)) =
  (λ ma' b' -> maybe (λ a' -> vis₂ con (quote _⊛_) a' (unshift′ b')) (‵π v s a b') ma')
    <$> quoteHyp d p a <*> quoteDesc d p b
quoteDesc d p  t                                     = join $ quoteHyp d p t

quoteData : Name -> TC Term
quoteData d =
  getData d >>= λ{ (packData _ a b cs ns) ->
      case mapM (quoteDesc d (countPis a)) cs of λ
        {  nothing   -> throw "can't read a data type"
        ; (just cs′) -> (λ qa qb -> elamsBy a ∘ curryBy b ∘ vis₁ def (quote μ) $
               vis₅ con (quote packData) (reify d) qa qb (reify cs′) (reify ns))
             <$> quoteTC a <*> quoteTC b
        }
    }

-- This doesn't work, because `quoteData` doesn't generate implicit lambdas,
-- because otherwise nothing would work due to the #2118 issue.
readDataTo : Name -> Name -> TC _
readDataTo d′ d = getType d >>= declareDef (earg d′)
               >> quoteData d >>= λ qd -> defineSimpleFun d′ qd

onFinalMu : ∀ {α} {A : Set α} -> (∀ {ι β} {I : Set ι} -> Data (Desc I β) -> TC A) -> Type -> TC A
onFinalMu k a = case resType a of λ
  { (def (quote μ) (iarg qι ∷ iarg qβ ∷ iarg qI ∷ earg qD ∷ _)) ->
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

  gcoerce : Term -> TC _
  gcoerce ?r = inferType ?r >>= onFinalMu λ{ D@(packData d _ b _ _) ->
      freshName "fold ++ showName d" >>= λ fd ->
      deriveFoldTo fd d >>
      quoteTC (μ D) >>= λ μD ->
      traverseAll quoteTC (allCons D) >>= λ cs′ ->
      unify ?r $ vis def fd (curryBy b μD ∷ allToList cs′)
    }

  guncoerce : ∀ {ι β} {I : Set ι} {D : Data (Desc I β)} {j} -> μ D j -> Term -> TC _
  guncoerce {D = packData d a b Ds ns} e ?r =
    quoteTC e >>= λ qe -> unify ?r ∘ vis def (quote curryFoldMono) $
      euncurryBy b (vis def d (replicate (countEPis a) unknown)) ∷ qe ∷ unmap (λ n -> con n []) ns
