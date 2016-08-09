module Generic.Reflection.DeriveEq where

open import Generic.Core
open import Generic.Function.FoldMono
open import Generic.Reflection.ReadData

fromToClausesOf : Data Type -> Name -> List Clause
fromToClausesOf (packData d a b cs ns) f = unmap (λ {a} -> clauseOf a) ns where
  
  fromPis : ℕ -> ℕ -> Type -> List (Maybe (String × ℕ) × ℕ)
  fromPis (suc i) j (rpi (earg a) (abs s b)) = if isSomeName d a
    then (just (s , j) , i) ∷ fromPis i (suc j) b
    else (nothing , i)      ∷ fromPis i j b
  fromPis  i      j (rpi  _       (abs s b)) = fromPis i j b
  fromPis  i      j  b                       = []

  clauseOf : Type -> Name -> Clause
  clauseOf c n =
    let es = episToNames c; i = length es
        mxs = fromPis i 0 c; xs = mapMaybe proj₁ mxs; p = length xs
    in clause (earg (con n (pvars es)) ∷ []) ∘ vis def (quote congn)
         $ reify p
         ∷ foldr (elam ∘ proj₁) (vis con n $ map (uncurry λ m i ->
             maybe (proj₂ >>> λ j -> ivar (p ∸ suc j)) (ivar (i + p)) m) mxs) xs
         ∷ mapMaybe (uncurry λ m i -> vis₁ def f (ivar i) <$ m) mxs

toTypeOf : Data Type -> Name -> Type
toTypeOf (packData d a b cs ns) d′ = let ab = appendType a b; k = countPis ab in
  appendType (implPis ab) $ def d (pisToArgVars k ab) ‵→ def d′ (pisToArgVars (suc k) ab)

fromTypeOf : Data Type -> Name -> Type
fromTypeOf (packData d a b cs ns) d′ = let ab = appendType a b; k = countPis ab in
  appendType (implPis ab) $ def d′ (pisToArgVars k ab) ‵→ def d (pisToArgVars (suc k) ab)

fromToTypeOf : Data Type -> Name -> Name -> Name -> Type
fromToTypeOf (packData d a b cs ns) d′ to from = let ab = appendType a b; k = countPis ab in
  appendType (implPis ab) ∘ rpi (earg (def d (pisToArgVars k ab))) ∘ abs "x" $
    vis₂ def (quote _≡_) (vis₁ def from (vis₁ def to (ivar 0))) (ivar 0)

injTypeOf : Data Type -> Name -> Type
injTypeOf (packData d a b cs ns) d′ = let ab = appendType a b; k = countPis ab in
  appendType (implPis ab) $
    vis₂ def (quote _↦_) (def d (pisToArgVars k ab)) (def d′ (pisToArgVars k ab))

uncoerce : Data Type -> Term
uncoerce (packData d a b cs ns) = elam "x" ∘ vis def (quote curryFoldMono) $
  euncurryBy b (vis def d (replicate (countEPis a) unknown)) ∷ ivar 0 ∷ unmap (λ n -> con n []) ns

deriveEqTo : Name -> Name -> TC _
deriveEqTo f d =
  getType d >>= λ a ->
  getData d >>= λ D ->
  freshName (showName d ++ˢ "′") >>= λ d′ ->
  declareDef (earg d′) a >>
  defineSimpleFun d′ (vis₁ def (quote readData) (def d [])) >>
  deriveFold d >>= λ fd ->
  freshName ("to" ++ˢ showName d′) >>= λ to ->
  declareDef (earg to) (toTypeOf D d′) >>
  defineSimpleFun to (vis₁ def (quote gcoerce) (def fd [])) >>
  freshName ("from" ++ˢ showName d′) >>= λ from ->
  declareDef (earg from) (fromTypeOf D d′) >>
  defineSimpleFun from (uncoerce D) >>
  freshName (showName from ++ˢ "-" ++ˢ showName to) >>= λ from-to ->
  declareDef (earg from-to) (fromToTypeOf D d′ to from) >>
  defineFun from-to (fromToClausesOf D from-to) >>
  freshName (showName d ++ˢ "Inj") >>= λ dInj ->
  declareDef (earg dInj) (injTypeOf D d′) >>
  defineSimpleFun dInj (vis₃ con (quote packInj) (def to []) (def from []) (def from-to [])) >>
  defineSimpleFun f (vis₁ def (quote viaInj) (def dInj []))
