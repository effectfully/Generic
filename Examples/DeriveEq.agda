module Generic.Examples.DeriveEq where

open import Generic.Main
open import Generic.Function.Elim

open import Data.Vec as Vec using (Vec) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)

module DeriveEqVec where
  module _ where
    private
      Vec′ : TypeOf Vec
      Vec′ = readData Vec

    unquoteDecl foldVec = deriveFoldTo foldVec (quote Vec)

    toVec′ : TypeOfBy toTypeOf Vec Vec′
    toVec′ = gcoerce foldVec

    fromVec′ : TypeOfBy fromTypeOf Vec Vec′
    fromVec′ xs = uncoerce xs

    fromToVec′ : TypeOfBy (fromToTypeOf (quote fromVec′) (quote toVec′)) Vec Vec′

    unquoteDef fromToVec′ = deriveFromToTo fromToVec′ (quote Vec)

    VecInj : TypeOfBy injTypeOf Vec Vec′
    VecInj = packInj toVec′ fromVec′ fromToVec′

  instance
    VecEq : ∀ {n α} {A : Set α} {{aEq : Eq A}} -> Eq (Vec A n)
    VecEq = viaInj VecInj

  xs : Vec ℕ 3
  xs = 2 ∷ᵥ 4 ∷ᵥ 1 ∷ᵥ []ᵥ

  test : xs ≟ xs ≡ yes refl
  test = refl

  module _ where
    private open module Dummy {n α A} = _↦_ (VecInj {n} {α} {A})

    elimVec : ∀ {n α π} {A : Set α}
            -> (P : ∀ {n} -> Vec A n -> Set π)
            -> (∀ {n} {xs : Vec A n} x -> P xs -> P (x ∷ᵥ xs))
            -> P []ᵥ
            -> (xs : Vec A n)
            -> P xs
    elimVec P f z xs = subst P (from-to xs)
                     $ elim (P ∘ from) (lift z , λ x r -> lift (f x r)) (to xs)

module DeriveEqD where
  data D {α β} (A : Set α) (B : A -> Set β) : ∀ {n x} -> Vec (B x) n -> ℕ -> Set (α ⊔ β) where
    c₁ : ∀ {x n} (ys : Vec (B x) n) m -> A -> D A B ys m
    c₂ : ∀ {x n m y} {ys zs : Vec (B x) n}
       -> D A B (y ∷ᵥ ys) 0 -> Vec A m -> D A B ys (suc n) -> D A B zs n

  private
    D′ : TypeOf D
    D′ = readData D

    unquoteDecl foldD = deriveFoldTo foldD (quote D)

    toD′ : TypeOfBy toTypeOf D D′
    toD′ = gcoerce foldD

    fromD′ : TypeOfBy fromTypeOf D D′
    fromD′ xs = uncoerce xs

    fromToD′ : TypeOfBy (fromToTypeOf (quote fromD′) (quote toD′)) D D′

    unquoteDef fromToD′ = deriveFromToTo fromToD′ (quote D)

    DInj : TypeOfBy injTypeOf D D′
    DInj = packInj toD′ fromD′ fromToD′

  -- `VecEq` is in scope.
  instance
    DEq : ∀ {α β} {A : Set α} {B : A -> Set β} {n m x} {ys : Vec (B x) n}
            {{aEq : Eq A}} {{bEq : ∀ {x} -> Eq (B x)}} -> Eq (D A B ys m)
    DEq = viaInj DInj
