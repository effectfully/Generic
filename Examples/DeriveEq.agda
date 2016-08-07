module Generic.Examples.DeriveEq where

open import Generic.Main
open import Generic.Function.Elim

open import Data.Vec as Vec using (Vec) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)

module DeriveEqVec where
  private
    Vec′ : TypeOf Vec
    Vec′ = readData Vec

    unquoteDecl foldVec = deriveFoldTo foldVec (quote Vec)

    toVec′ : TypeOfBy toTypeOf Vec Vec′
    toVec′ = gcoerce foldVec

    fromVec′ : TypeOfBy fromTypeOf Vec Vec′
    fromVec′ x = uncoerce x

  instance VecEq : ∀ {n α} {A : Set α} {{aEq : Eq A}} -> Eq (Vec A n)
  unquoteDef VecEq = deriveEqTo VecEq (quote Vec) (quote Vec′) (quote toVec′) (quote fromVec′)

module Test where
  xs : Vec ℕ 3
  xs = 2 ∷ᵥ 4 ∷ᵥ 1 ∷ᵥ []ᵥ

  test : xs ≟ xs ≡ yes refl
  test = refl

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
    fromD′ x = uncoerce x

  instance DEq : ∀ {α β} {A : Set α} {B : A -> Set β} {n m x} {ys : Vec (B x) n}
                   {{aEq : Eq A}} {{bEq : ∀ {x} -> Eq (B x)}} -> Eq (D A B ys m)
  unquoteDef DEq = deriveEqTo DEq (quote D) (quote D′) (quote toD′) (quote fromD′)
