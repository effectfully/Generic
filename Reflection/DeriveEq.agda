module Generic.Reflection.DeriveEq where

open import Generic.Core
open import Generic.Lib.Equality.Congn

fromToClausesOf : Data Type -> Name -> List Clause
fromToClausesOf (packData d a b cs ns) f = unmap (λ {a} -> clauseOf a) ns where
  
  fromPi : ℕ -> ℕ -> Type -> List (Maybe (String × ℕ) × ℕ)
  fromPi (suc i) j (rpi (earg a) (abs s b)) =
    if isSomeName d a then (just (s , j) , i) ∷ fromPi i (suc j) b else (nothing , i) ∷ fromPi i j b
  fromPi  i      j (rpi  _       (abs s b)) = fromPi i j b
  fromPi  i      j  b                       = []

  clauseOf : Type -> Name -> Clause
  clauseOf c n =
    let es = epiToStrs c; i = length es
        mxs = fromPi i 0 c; xs = mapMaybe proj₁ mxs; p = length xs
    in clause (earg (con n (pvars es)) ∷ []) ∘ vis def (quote congn)
         $ reify p
         ∷ foldr (elam ∘ proj₁) (vis con n $ map (uncurry λ m i ->
             maybe (proj₂ >>> λ j -> ivar (p ∸ suc j)) (ivar (i + p)) m) mxs) xs
         ∷ mapMaybe (uncurry λ m i -> vis₁ def f (ivar i) <$ m) mxs

toTypeOf : Data Type -> Name -> Type
toTypeOf (packData d a b cs ns) d′ = let ab = appendType a b; k = countPi ab in
  appendType (implPi ab) $ def d (piToArgs k ab) ‵→ def d′ (piToArgs (suc k) ab)

fromTypeOf : Data Type -> Name -> Type
fromTypeOf (packData d a b cs ns) d′ = let ab = appendType a b; k = countPi ab in
  appendType (implPi ab) $ def d′ (piToArgs k ab) ‵→ def d (piToArgs (suc k) ab)

fromToTypeOf : Name -> Name -> Data Type -> Name -> Type
fromToTypeOf from to (packData d a b cs ns) d′ = let ab = appendType a b; k = countPi ab in
  appendType (implPi ab) ∘ rpi (earg (def d (piToArgs k ab))) ∘ abs "x" $
    vis₂ def (quote _≡_) (vis₁ def from (vis₁ def to (ivar 0))) (ivar 0)

injTypeOf : Data Type -> Name -> Type
injTypeOf (packData d a b cs ns) d′ = let ab = appendType a b; k = countPi ab in
  appendType (implPi ab) $ vis₂ def (quote _↦_) (def d (piToArgs k ab)) (def d′ (piToArgs k ab))

macro
  TypeOfBy : (Data Type -> Name -> Type) -> Name -> Name -> Term -> TC _
  TypeOfBy k d d′ ?r = getData d >>= λ D -> unify ?r $ k D d′

deriveFromToTo : Name -> Name -> TC _
deriveFromToTo f d = getData d >>= λ D -> defineFun f (fromToClausesOf D f)
