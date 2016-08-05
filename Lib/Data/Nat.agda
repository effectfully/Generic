module Generic.Lib.Data.Nat where

open import Data.Nat.Base hiding (_⊔_; _≟_; fold) public

open import Generic.Lib.Decidable

instance
  ℕEq : Eq ℕ
  ℕEq = viaBase Nat._≟_ where
    import Data.Nat.Base as Nat
