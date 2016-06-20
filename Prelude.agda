module Generic.Prelude where

open import Level renaming (zero to lzero; suc to lsuc) public
open import Function public
open import Data.Bool.Base hiding (_≟_) public
open import Data.Nat.Base hiding (_≟_; _⊔_) public
open import Data.Sum renaming (map to smap) public
open import Data.Product renaming (map to pmap; zip to pzip) public

open import Generic.Lib.Propositional public
open import Generic.Lib.Heteroindexed public
open import Generic.Lib.Decidable hiding (map) public

infixr 5 _∷_

data ⊥ {α} : Set α where
record ⊤ {α} : Set α where
  constructor tt

⊥₀ = ⊥ {lzero}
⊤₀ = ⊤ {lzero}

record Apply {α β} {A : Set α} (B : A -> Set β) x : Set β where
  constructor tag
  field detag : B x
open Apply public

tagWith : ∀ {α β} {A : Set α} {B : A -> Set β} x -> B x -> Apply B x
tagWith x = tag

record Eq {α} (A : Set α) : Set α where
  infixl 5 _≟_ _==_

  field _≟_ : IsSet A

  _==_ : A -> A -> Bool
  x == y = ⌊ x ≟ y ⌋ 
open Eq {{...}} public

data IList {ι α} {I : Set ι} (A : I -> Set α) : Set (ι ⊔ α) where
  []  : IList A
  _∷_ : ∀ {i} -> A i -> IList A -> IList A

Any : ∀ {ι α β} {I : Set ι} {A : I -> Set α} -> (∀ {i} -> A i -> Set β) -> IList A -> Set β
Any B  []      = ⊥
Any B (x ∷ []) = B x
Any B (x ∷ xs) = B x ⊎ Any B xs

All : ∀ {ι α β} {I : Set ι} {A : I -> Set α} -> (∀ {i} -> A i -> Set β) -> IList A -> Set β
All B  []      = ⊤
All B (x ∷ xs) = B x × All B xs

findInd : ∀ {ι α β} {I : Set ι} {A : I -> Set α} {B : ∀ {i} -> A i -> Set β}
        -> (xs : IList A) -> (a : Any B xs) -> I
findInd  []                       ()
findInd (_∷_ {i = i} x  [])       z       = i
findInd (_∷_ {i = i} x (y ∷ xs)) (inj₁ z) = i
findInd (x ∷ y ∷ xs)             (inj₂ a) = findInd (y ∷ xs) a

findEl : ∀ {ι α β} {I : Set ι} {A : I -> Set α} {B : ∀ {i} -> A i -> Set β}
       -> (xs : IList A) -> (a : Any B xs) -> A (findInd xs a)
findEl  []           ()
findEl (x ∷ [])      z       = x
findEl (x ∷ y ∷ xs) (inj₁ z) = x
findEl (x ∷ y ∷ xs) (inj₂ a) = findEl (y ∷ xs) a

find : ∀ {ι α β} {I : Set ι} {A : I -> Set α} {B : ∀ {i} -> A i -> Set β}
     -> (xs : IList A) -> (a : Any B xs) -> B (findEl xs a)
find  []           ()
find (x ∷ [])      z       = z
find (x ∷ y ∷ xs) (inj₁ z) = z
find (x ∷ y ∷ xs) (inj₂ a) = find (y ∷ xs) a

,-inj : ∀ {α β} {A : Set α} {B : A -> Set β} {x₁ x₂} {y₁ : B x₁} {y₂ : B x₂}
      -> (x₁ , y₁) ≡ (x₂ , y₂) -> [ B ] y₁ ≅ y₂
,-inj refl = irefl

tag-inj : ∀ {α β} {A : Set α} {B : A -> Set β} {x} {y₁ y₂ : B x}
        -> tag {B = B} y₁ ≡ tag y₂ -> y₁ ≡ y₂
tag-inj refl = refl

inj₁-inj : ∀ {α β} {A : Set α} {B : Set β} {x₁ x₂ : A}
         -> inj₁ {B = B} x₁ ≡ inj₁ x₂ -> x₁ ≡ x₂
inj₁-inj refl = refl

inj₂-inj : ∀ {α β} {A : Set α} {B : Set β} {y₁ y₂ : B}
         -> inj₂ {A = A} y₁ ≡ inj₂ y₂ -> y₁ ≡ y₂
inj₂-inj refl = refl

_<,>ᵈ_ : ∀ {α β} {A : Set α} {B : Set β} {x₁ x₂ : A} {y₁ y₂ : B}
       -> x₁ # x₂ -> y₁ # y₂ -> x₁ , y₁ # x₂ , y₂
_<,>ᵈ_ = dcong₂ _,_ (inds-homo ∘ ,-inj)

_<,>ᵈᵒ_ : ∀ {α β} {A : Set α} {B : A -> Set β} {x₁ x₂} {y₁ : B x₁} {y₂ : B x₂}
        -> x₁ # x₂ -> (∀ y₂ -> y₁ # y₂) -> x₁ , y₁ # x₂ , y₂
_<,>ᵈᵒ_ = dhcong₂ _,_ ,-inj

instance
  ,-inst : ∀ {α β} {A : Set α} {B : A -> Set β} {{x : A}} {{y : B x}} -> Σ A B
  ,-inst {{x}} {{y}} = x , y

  ℕEq : Eq ℕ
  ℕEq = record { _≟_ = go } where
    suc-inj : ∀ {n m} -> suc n ≡ suc m -> n ≡ m
    suc-inj refl = refl

    go : IsSet ℕ
    go  0       0      = yes refl
    go (suc n) (suc m) = dcong suc suc-inj (go n m)
    go  0      (suc _) = no λ()
    go (suc n)  0      = no λ()
