module Generic.Examples.DeriveEq where

open import Generic.Main

open import Data.Vec using (Vec) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)

module DeriveEqStar where
  open import Relation.Binary
  open import Relation.Binary.Construct.Closure.ReflexiveTransitive

  instance StarEq : ∀ {i t} {I : Set i} {T : Rel I t} {i j}
                      {{iEq : Eq I}} {{tEq : ∀ {i j} -> Eq (T i j)}} -> Eq (Star T i j)
  unquoteDef StarEq = deriveEqTo StarEq (quote Star)

module DeriveEqVec where
  instance VecEq : ∀ {n α} {A : Set α} {{aEq : Eq A}} -> Eq (Vec A n)
  unquoteDef VecEq = deriveEqTo VecEq (quote Vec)

  xs : Vec ℕ 3
  xs = 2 ∷ᵥ 4 ∷ᵥ 1 ∷ᵥ []ᵥ

  test₁ : xs ≟ xs ≡ yes refl
  test₁ = refl

  test₂ : xs ≟ (2 ∷ᵥ 4 ∷ᵥ 2 ∷ᵥ []ᵥ) ≡ no _
  test₂ = refl

module DeriveEqD where
  data D {α β} (A : Set α) (B : A -> Set β) : ∀ {n x} -> Vec (B x) n -> ℕ -> Set (α ⊔ β) where
    c₁ : ∀ {x n} (ys : Vec (B x) n) m -> .A -> D A B ys m
    c₂ : ∀ {x n m y} {ys zs : Vec (B x) n}
       -> D A B (y ∷ᵥ ys) 0 -> Vec A m -> D A B ys (suc n) -> D A B zs n

  -- `VecEq` is in scope.
  instance DEq : ∀ {α β} {A : Set α} {B : A -> Set β} {n m x} {ys : Vec (B x) n}
                   {{aEq : Eq A}} {{bEq : ∀ {x} -> Eq (B x)}} -> Eq (D A B ys m)
  unquoteDef DEq = deriveEqTo DEq (quote D)

-- -- Seems like the problem is that irrelevance and metavariables resolution do not play well.
-- module DeriveEqE where
--   data E {α} (A : Set α) : ∀ {n} -> .(Vec A n) -> Set α where
--     c₁ : ∀ {n} -> .(xs : Vec A n) -> E A xs

--   instance EEq : ∀ {α n} {A : Set α} .{xs : Vec A n} -> Eq (E A xs)
--   unquoteDef EEq = deriveEqTo EEq (quote E)
--   -- Variable xs is declared irrelevant, so it cannot be used here
--   -- when checking that the expression xs has type _B_76 A _ n₁ _ n₁

module DeriveEqF where
  data F {α} (A : Set α) : Set α where
    c₁ : ∀ {n} -> .(Vec A n) -> F A

  instance FEq : ∀ {α} {A : Set α} -> Eq (F A)
  unquoteDef FEq = deriveEqTo FEq (quote F)
