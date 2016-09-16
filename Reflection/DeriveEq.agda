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

uncoerce : Data Type -> Term
uncoerce (packData d a b cs ns) = explLam "x" ∘ vis appDef (quote curryFoldMono) $
  explUncurryBy b (vis appDef d (replicate (countExplPis a) unknown)) ∷ pureVar 0 ∷ unmap pureCon ns

-- Waits to be refactored.
deriveEqTo : Name -> Name -> TC _
deriveEqTo f d =
  getType d >>= λ a ->
  getData d >>= λ D ->
  freshName (showName d ++ˢ "′") >>= λ d′ ->
  -- quoteData D >>= λ D′ -> defineSimpleFun d′ D′ -- https://github.com/agda/agda/issues/2191
  declareDef (explRelArg d′) a >>
  defineSimpleFun d′ (sateMacro readData (pureDef d)) >>
  deriveFold d >>= λ fd ->
  freshName ("to" ++ˢ showName d′) >>= λ to ->
  declareDef (explRelArg to) (toTypeOf D d′) >>
  defineSimpleFun to (sateMacro gcoerce (pureDef fd)) >>
  freshName ("from" ++ˢ showName d′) >>= λ from ->
  declareDef (explRelArg from) (fromTypeOf D d′) >>
  defineSimpleFun from (uncoerce D) >>
  freshName (showName from ++ˢ "-" ++ˢ showName to) >>= λ from-to ->
  declareDef (explRelArg from-to) (fromToTypeOf D d′ to from) >>
  defineFun from-to (fromToClausesOf D from-to) >>
  freshName (showName d ++ˢ "Inj") >>= λ dInj ->
  declareDef (explRelArg dInj) (injTypeOf D d′) >>
  defineSimpleFun dInj (sate packInj (pureDef to) (pureDef from) (pureDef from-to)) >>
  defineSimpleFun f (sate viaInj (pureDef dInj))

open import Generic.Property.Eq

test : {A : Set} {{eqA : Eq A}} -> Eq (List A)
unquoteDef test = deriveEqTo test (quote List)
