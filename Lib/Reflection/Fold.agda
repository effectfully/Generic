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
foldTypeOf (packData d a b cs ns) = let i = countPi a; j = countPi b; ab = appendType a b in
  appendType (implPi ab) ∘ rpi (iarg (quoteTerm Level)) ∘ abs "π" ∘
    rpi (earg ∘ appendType (shiftBy (j + 1) b) ∘ sort ∘ set $ ivar j) ∘ abs "P" $
      foldr (λ c r -> mapName (λ p -> rvar p ∘ drop i) d (shiftBy (j + 2) c) ‵→ shift r)
            (def d (piToArgs (i + j + 2) ab) ‵→ rvar 1 (piToArgs (j + 3) b))
             cs

foldClausesOf : Data Type -> Name -> List Clause
foldClausesOf (packData d a b cs ns) f = allToList $ mapAllInd (λ {a} n -> clauseOf n a) ns where
  k = length cs

  tryHyp : (ℕ -> List String -> Term -> Term) -> ℕ -> Type -> Maybe Term
  tryHyp rec n = go id where
    go : (List String -> List String) -> Type -> Maybe Term
    go l (rpi (earg a) (abs s b)) = go (l ∘ (s ∷_)) b
    go l (rpi  _       (abs s b)) = go l b
    go l (def e _)                = let p = length (l []) in if d == e
      then just $ rec p (l []) (vis rvar (n + p) (map ivar(downFrom p)))
      else nothing
    go l  _                       = nothing

  fromPi : (ℕ -> List String -> Term -> Term) -> ℕ -> Type -> List Term
  fromPi rec (suc n) (rpi (earg a) (abs s b)) =
    maybe id (ivar n) (tryHyp rec n a) ∷ fromPi rec n b
  fromPi rec  n      (rpi  _       (abs s b)) = fromPi rec n b
  fromPi rec  n       b                       = []

  clauseOf : ℕ -> Type -> Name -> Clause
  clauseOf i c n = let es = epiToStrs c; j = length es in
    clause (pvars ("P" ∷ unmap (λ n -> "f" ++ˢ showName n) ns) ∷ʳ earg (con n (pvars es)))
      (vis rvar (k + j ∸ suc i) (fromPi (λ p l t -> foldr elam
        (vis def f (map (λ v -> ivar (v + p)) (downFromTo (suc k + j) j) ∷ʳ t)) l) j c))

deriveFoldTo : Name -> Name -> TC _
deriveFoldTo f d =
  getData d >>= λ D ->
  declareDef (earg f) (foldTypeOf D) >>
  defineFun f (foldClausesOf D f)

-- This doesn't seem to define the most general fold for some reason.
deriveFold : Name -> TC Name
deriveFold d =
  freshName ("fold" ++ˢ showName d) >>= λ fd ->
  deriveFoldTo fd d >>
  return fd

-- This drops leading implicit arguments, because `fd` is "applied" to the empty spine.
macro
  fold : Name -> Term -> TC _
  fold d ?r = deriveFold d >>= λ fd -> unify ?r (def fd [])
