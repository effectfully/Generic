module Generic.Lib.Data.Nat where

open import Data.Nat.Base hiding (_⊔_; _≟_; fold) public

open import Generic.Lib.Decidable

instance
  ℕEq : Eq ℕ
  ℕEq = viaBase Nat._≟_ where
    import Data.Nat.Base as Nat

foldℕ : ∀ {α} {A : Set α} -> (A -> A) -> A -> ℕ -> A
foldℕ f x  0      = x
foldℕ f x (suc n) = f (foldℕ f x n)
