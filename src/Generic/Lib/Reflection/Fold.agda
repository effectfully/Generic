module Generic.Lib.Reflection.Fold where

open import Generic.Lib.Intro
open import Generic.Lib.Decidable
open import Generic.Lib.Category
open import Generic.Lib.Data.Nat
open import Generic.Lib.Data.String
open import Generic.Lib.Data.Maybe
open import Generic.Lib.Data.List
open import Generic.Lib.Reflection.Core

foldTypeOf : Data Type -> Type
foldTypeOf (packData d a b cs ns) = appendType iab ∘ pi "π" π ∘ pi "P" P $ cs ʰ→ from ‵→ to where
  infixr 5 _ʰ→_
  i    = countPis a
  j    = countPis b
  ab   = appendType a b
  iab  = implicitize ab
  π    = implRelArg (quoteTerm Level)
  P    = explRelArg ∘ appendType (shiftBy (suc j) b) ∘ agda-sort ∘ set $ pureVar j
  hyp  = mapName (λ p -> appVar p ∘ drop i) d ∘ shiftBy (2 + j)
  _ʰ→_ = flip $ foldr (λ c r -> hyp c ‵→ shift r)
  from = appDef d (pisToArgVars (2 + i + j) ab)
  to   = appVar 1 (pisToArgVars (3 + j) b)

foldClausesOf : Name -> Data Type -> List Clause
foldClausesOf f (packData d a b cs ns) = allToList $ mapAllInd (λ {a} n -> clauseOf n a) ns where
  k = length cs

  clauseOf : ℕ -> Type -> Name -> Clause
  clauseOf i c n = clause lhs rhs where
    args = explPisToNames c
    j    = length args
    lhs  = patVars ("P" ∷ unmap (λ n -> "f" ++ˢ showName n) ns)
         ∷ʳ explRelArg (patCon n (patVars args))

    tryHyp : ℕ -> ℕ -> Type -> Maybe Term
    tryHyp m l (explPi r s a b) = explLam s <$> tryHyp (suc m) l b
    tryHyp m l (pi       s a b) = tryHyp m l b
    tryHyp m l (appDef e _)     = d == e ?> vis appDef f (pars ∷ʳ rarg) where
      pars = map (λ i -> pureVar (m + i)) $ downFromTo (suc k + j) j
      rarg = vis appVar (m + l) $ map pureVar (downFrom m)
    tryHyp m l  b               = nothing

    hyps : ℕ -> Type -> List Term
    hyps (suc l) (explPi r s a b) = fromMaybe (pureVar l) (tryHyp 0 l a) ∷ hyps l b
    hyps  l      (pi       s a b) = hyps l b
    hyps  l       b               = []

    rhs = vis appVar (k + j ∸ suc i) (hyps j c)

    -- i = 1: f
    -- j = 3: x t r
    -- k = 2: g f
    --      5 4 3       2 1 0    3 2       4 3 1     1 0         6 5  2 1 0
    -- fold P g f (cons x t r) = f x (fold g f t) (λ y u -> fold g f (r y u))

defineFold : Name -> Data Type -> TC _
defineFold f D =
  declareDef (explRelArg f) (foldTypeOf D) >>
  defineFun f (foldClausesOf f D)

deriveFold : Name -> Data Type -> TC Name
deriveFold d D =
  freshName ("fold" ++ˢ showName d) >>= λ f ->
  f <$ defineFold f D

deriveFoldTo : Name -> Name -> TC _
deriveFoldTo f = getData >=> defineFold f
