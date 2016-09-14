module Generic.Reflection.DeriveEq where

open import Generic.Core
open import Generic.Function.FoldMono
open import Generic.Reflection.ReadData

fromToClausesOf : Data Type -> Name -> List Clause
fromToClausesOf (packData d a b cs ns) f = unmap (λ {a} -> clauseOf a) ns where
  fromPis : ℕ -> ℕ -> Type -> List (Maybe (String × ℕ) × ℕ)
  fromPis (suc i) j (explPi r s a b) = if isSomeName d a
    then (just (s , j) , i) ∷ fromPis i (suc j) b
    else (nothing      , i) ∷ fromPis i  j      b
  fromPis  i      j (pi       s a b) = fromPis i j b
  fromPis  i      j  b               = []

  clauseOf : Type -> Name -> Clause
  clauseOf c n =
    let es  = explPisToNames c
        i   = length es
        mxs = fromPis i 0 c
        xs  = mapMaybe proj₁ mxs
        p   = length xs
    in clause (explRelArg (patCon n (patVars es)) ∷ []) ∘ vis appDef (quote congn)
         $ reify p
         ∷ foldr (explLam ∘ proj₁) (vis appCon n $ map (uncurry λ m i ->
             maybe (proj₂ >>> λ j -> pureVar (p ∸ suc j)) (pureVar (i + p)) m) mxs) xs
         ∷ mapMaybe (uncurry λ m i -> vis₁ appDef f (pureVar i) <$ m) mxs

toTypeOf : Data Type -> Name -> Type
toTypeOf (packData d a b cs ns) d′ = let ab = appendType a b; k = countPis ab in
  appendType (implicitize ab) $ appDef d (pisToArgVars k ab) ‵→ appDef d′ (pisToArgVars (suc k) ab)

fromTypeOf : Data Type -> Name -> Type
fromTypeOf (packData d a b cs ns) d′ = let ab = appendType a b; k = countPis ab in
  appendType (implicitize ab) $ appDef d′ (pisToArgVars k ab) ‵→ appDef d (pisToArgVars (suc k) ab)

fromToTypeOf : Data Type -> Name -> Name -> Name -> Type
fromToTypeOf (packData d a b cs ns) d′ to from = let ab = appendType a b; k = countPis ab in
  appendType (implicitize ab) ∘ pi "x" (explRelArg (appDef d (pisToArgVars k ab))) $
    sate _≡_ (vis₁ appDef from (vis₁ appDef to (pureVar 0))) (pureVar 0)

injTypeOf : Data Type -> Name -> Type
injTypeOf (packData d a b cs ns) d′ = let ab = appendType a b; k = countPis ab in
  appendType (implicitize ab) $
    sate _↦_ (appDef d (pisToArgVars k ab)) (appDef d′ (pisToArgVars k ab))

uncoerce : Data Type -> Term
uncoerce (packData d a b cs ns) = explLam "x" ∘ vis appDef (quote curryFoldMono) $
  explUncurryBy b (vis appDef d (replicate (countExplPis a) unknown)) ∷ pureVar 0 ∷ unmap pureCon ns

-- Waits to be refactored.
deriveEqTo : Name -> Name -> TC _
deriveEqTo f d =
  getType d >>= λ a ->
  getData d >>= λ D ->
  freshName (showName d ++ˢ "′") >>= λ d′ ->
  -- quoteData D >>= λ D′ -> -- I have no idea why (defineSimpleFun d′ D′) doesn't work.
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
