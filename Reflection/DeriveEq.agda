module Generic.Reflection.DeriveEq where

open import Generic.Core
open import Generic.Function.FoldMono
open import Generic.Reflection.ReadData

fromToClausesOf : Data Type -> Name -> List Clause
fromToClausesOf (packData d a b cs ns) f = unmap (λ {a} -> clauseOf a) ns where
  vars : ℕ -> ℕ -> Type -> List (Maybe (String × ℕ) × ℕ)
  vars (suc i) j (explPi r s a b) = if isSomeName d a
    then (just (s , j) , i) ∷ vars i (suc j) b
    else (nothing      , i) ∷ vars i  j      b
  vars  i      j (pi       s a b) = vars i j b
  vars  i      j  b               = []

  clauseOf : Type -> Name -> Clause
  clauseOf c n = clause lhs rhs where
    es   = explPisToNames c
    i    = length es
    mxs  = vars i 0 c
    xs   = mapMaybe proj₁ mxs
    k    = length xs
    lhs  = explRelArg (patCon n (patVars es)) ∷ []
    lams = λ t -> foldr (explLam ∘ proj₁) t xs
    each = λ m i -> maybe (proj₂ >>> λ j -> pureVar (k ∸ suc j)) (pureVar (i + k)) m
    args = map (uncurry each) mxs
    grow = lams (vis appCon n args)
    rs   = mapMaybe (uncurry λ m i -> vis₁ appDef f (pureVar i) <$ m) mxs
    rhs  = vis appDef (quote congn) $ reify k ∷ grow ∷ rs

toTypeOf : Data Type -> Name -> Type
toTypeOf (packData d a b cs ns) d′ = let ab = appendType a b; k = countPis ab in
  appendType (implicitize ab) $ appDef d (pisToArgVars k ab) ‵→ appDef d′ (pisToArgVars (suc k) ab)

fromTypeOf : Data Type -> Name -> Type
fromTypeOf (packData d a b cs ns) d′ = let ab = appendType a b; k  = countPis ab in
  appendType (implicitize ab) $ appDef d′ (pisToArgVars k ab) ‵→ appDef d (pisToArgVars (suc k) ab)

fromToTypeOf : Data Type -> Name -> Name -> Name -> Type
fromToTypeOf (packData d a b cs ns) d′ to from = let ab = appendType a b; k = countPis ab in
  appendType (implicitize ab) ∘ pi "x" (explRelArg (appDef d (pisToArgVars k ab))) $
    sate _≡_ (vis₁ appDef from (vis₁ appDef to (pureVar 0))) (pureVar 0)

injTypeOf : Data Type -> Name -> Type
injTypeOf (packData d a b cs ns) d′ =
  let ab  = appendType a b
      k   = countPis ab
      avs = pisToArgVars k ab
  in appendType (implicitize ab) $ sate _↦_ (appDef d avs) (appDef d′ avs)

deriveDesc : Data Type -> Name -> TC Name
deriveDesc D d =
  freshName (showName d ++ˢ "′") >>= λ d′ ->
  getType d >>= λ a ->
  declareDef (explRelArg d′) a >>
  d′ <$ (quoteData D >>= defineTerm d′)

deriveTo : Data Type -> Name -> Name -> TC Name
deriveTo D d′ fd =
  freshName ("to" ++ˢ showName d′) >>= λ to ->
  declareDef (explRelArg to) (toTypeOf D d′) >>
  to <$ defineTerm to (sateMacro gcoerce (pureDef fd))

deriveFrom : Data Type -> Name -> TC Name
deriveFrom D d′ =
  freshName ("from" ++ˢ showName d′) >>= λ from ->
  declareDef (explRelArg from) (fromTypeOf D d′) >>
  from <$ defineTerm from (guncoercePure D)

deriveFromTo : Data Type -> Name -> Name -> Name -> TC Name
deriveFromTo D d′ to from =
  freshName ("fromTo" ++ˢ showName d′) >>= λ from-to ->
  declareDef (explRelArg from-to) (fromToTypeOf D d′ to from) >>
  from-to <$ defineFun from-to (fromToClausesOf D from-to)

deriveInj : Data Type -> Name -> Name -> Name -> Name -> TC Name
deriveInj D d′ to from from-to =
  freshName ("inj" ++ˢ showName d′) >>= λ inj ->
  declareDef (explRelArg inj) (injTypeOf D d′) >>
  inj <$ defineTerm inj (sate packInj (pureDef to) (pureDef from) (pureDef from-to))

deriveEqTo : Name -> Name -> TC _
deriveEqTo f d =
  getData d >>= λ D ->
  deriveDesc D d >>= λ d′ ->
  deriveFold d >>= λ fd ->
  deriveTo D d′ fd >>= λ to ->
  deriveFrom D d′ >>= λ from ->
  deriveFromTo D d′ to from >>= λ from-to ->
  deriveInj D d′ to from from-to >>= λ inj ->
  defineTerm f (sate viaInj (pureDef inj))
