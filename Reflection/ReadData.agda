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
    then just (vis₁ con (quote var) ∘ pack ∘ map unarg ∘ drop p $ is)
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
    case mapM (quoteDesc d (countPi a)) cs of λ
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

-- This can be typed, but the inlined version should be faster.
quoteCons : Name -> Term -> Term -> Term
quoteCons n D ns = vis₂ def (quote cons) D ∘ vis₁ def (quote proj₂) ∘
                     vis₁ def (quote from-just) $ vis₂ def (quote lookupAllConst) (reify n) ns

unifyWhenMu : Term -> (∀ {ι β} {I : Set ι} -> Data (Desc I β) -> Term -> Term -> Term) -> TC _
unifyWhenMu ?r k = inferType ?r >>= resType >>> λ
  { (def (quote μ) (iarg qι ∷ iarg qβ ∷ iarg qI ∷ earg qD ∷ _)) ->
       unquoteTC qι >>= λ ι ->
       unquoteTC qβ >>= λ β ->
       bindTC (unquoteTC qI) λ (I : Set ι) ->
       bindTC (unquoteTC qD) λ (D : Data (Desc I β)) -> case D of λ{
         (packData d a b cs ns) -> quoteTC ns >>= unify ?r ∘ k D qD
       }
  ;  _                                                          ->
       throw "the return type must be μ"
  }
  
macro
  readData : Name -> Term -> TC _
  readData d ?r = quoteData d >>= unify ?r

  readCons : Name -> Term -> TC _
  readCons n ?r = unifyWhenMu ?r λ _ -> quoteCons n

  gcoerce : Name -> Term -> TC _
  gcoerce fd ?r = unifyWhenMu ?r λ{ (packData d a b cs ns) qD qns ->
      let cs′ = unmap (λ n -> quoteCons n qD qns) ns in
      vis def fd (curryBy b (vis₁ def (quote μ) qD) ∷ cs′)
    }

  uncoerce : ∀ {ι β} {I : Set ι} {D : Data (Desc I β)} {j} -> μ D j -> Term -> TC _
  uncoerce {D = packData d a b Ds ns} e ?r =
    quoteTC e >>= λ qe -> unify ?r ∘ vis def (quote curryFoldMono) $
      euncurryBy b (vis def d (replicate (countEPi a) unknown)) ∷ qe ∷ unmap (λ n -> con n []) ns
