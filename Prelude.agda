module Generic.Prelude where

open import Level renaming (zero to lzero; suc to lsuc) public
open import Function public
open import Data.Bool.Base hiding (_≟_) public
open import Data.Nat.Base as Nat hiding (_≟_; _⊔_) public
open import Data.String.Base renaming (_++_ to _++ˢ_) public
open import Data.Sum renaming (map to smap) public
open import Data.Product renaming (map to pmap; zip to pzip) hiding (_,′_) public
open import Data.List.Base public
open import Category.Monad public
open import Reflection
  renaming (visible to expl; hidden to impl; instance′ to inst;
    relevant to rel; irrelevant to irr; pi to rpi; lam to rlam)
  hiding (_≟_) public

open import Generic.Lib.Propositional public
open import Generic.Lib.Heteroindexed public
open import Generic.Lib.Decidable hiding (map) public

open RawMonad {{...}} renaming (_⊛_ to _<*>_) hiding (zipWith) public

open import Data.Maybe.Base hiding (Any; All; map)
import Data.Maybe as Maybe
import Data.List as List

infixl 3 _·_

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

record Quote {α} (A : Set α) : Set α where
  field deepQuote : A -> Term
open Quote {{...}} public

Any : ∀ {α β} {A : Set α} -> (A -> Set β) -> List A -> Set β
Any B  []      = ⊥
Any B (x ∷ []) = B x
Any B (x ∷ xs) = B x ⊎ Any B xs

All : ∀ {α β} {A : Set α} -> (A -> Set β) -> List A -> Set β
All B  []      = ⊤
All B (x ∷ xs) = B x × All B xs

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

decSum : ∀ {α β} {A : Set α} {B : Set β} -> IsSet A -> IsSet B -> IsSet (A ⊎ B)
decSum f g (inj₁ x₁) (inj₁ x₂) = dcong inj₁ inj₁-inj (f x₁ x₂)
decSum f g (inj₂ y₁) (inj₂ y₂) = dcong inj₂ inj₂-inj (g y₁ y₂)
decSum f g (inj₁ x₁) (inj₂ y₂) = no λ()
decSum f g (inj₂ y₁) (inj₁ x₂) = no λ()

fmap = _<$>_

mapM : ∀ {α β} {A : Set α} {B : Set β} {M : Set β -> Set β} {{mMonad : RawMonad M}}
     -> (A -> M B) -> List A -> M (List B)
mapM {{mMonad}} = List.mapM mMonad

module _ where
  import Relation.Binary.PropositionalEquality as B

  liftBase : ∀ {α} {A : Set α} {x y : A} -> x B.≡ y -> x ≡ y
  liftBase B.refl = refl

  lowerBase : ∀ {α} {A : Set α} {x y : A} -> x ≡ y -> x B.≡ y
  lowerBase refl = B.refl

  viaBase : ∀ {α} {A : Set α} -> Decidable (B._≡_ {A = A}) -> Eq A
  viaBase d = record
    { _≟_ = flip (via-injection {A = ≡-Setoid _} {B = B.setoid _}) d $ record
      { to = record
        { _⟨$⟩_ = id
        ; cong  = lowerBase
        }
      ; injective = liftBase
      }
    }

pattern earg x = arg (arg-info expl rel) x
{-# DISPLAY arg (arg-info expl relevant) = earg #-}

pattern iarg x = arg (arg-info impl rel) x
{-# DISPLAY arg (arg-info impl relevant) = iarg #-}

vis : {A : Set} -> (A -> List (Arg Term) -> Term) -> A -> List Term -> Term
vis k x = k x ∘ map earg

elam : String -> Term -> Term
elam s = rlam expl ∘ abs s

_·_ : Term -> Term -> Term
f · x = vis def (quote id) $ f ∷ x ∷ []

-- Using `⊤₀` here results in unsolved metas later.
unshift : Term -> Term
unshift t = elam "_" t · quoteTerm (Unit.⊤ ∋ _)
  where import Data.Unit.Base as Unit

instance
  ,-inst : ∀ {α β} {A : Set α} {B : A -> Set β} {{x : A}} {{y : B x}} -> Σ A B
  ,-inst {{x}} {{y}} = x , y

  ℕEq : Eq ℕ
  ℕEq = viaBase Nat._≟_

  NameEq : Eq Name
  NameEq = viaBase _≟-Name_

  TermQuote : Quote Term
  TermQuote = record { deepQuote = id }

  VisibilityQuote : Quote Visibility
  VisibilityQuote = record
    { deepQuote = λ
      { expl -> quoteTerm expl
      ; impl -> quoteTerm impl
      ; inst -> quoteTerm inst
      }
    }

  VisibilityList : ∀ {α} {A : Set α} {{aQuote : Quote A}} -> Quote (List A)
  VisibilityList = record
    { deepQuote = foldr (λ x r -> vis con (quote _∷_) $ deepQuote x ∷ r ∷ [])
                        (quoteTerm (List Term ∋ []))
    }  

  MaybeMonad : ∀ {α} -> RawMonad {α} Maybe
  MaybeMonad = Maybe.monad

  TCMonad : ∀ {α} -> RawMonad {α} TC
  TCMonad = record
    { return = returnTC
    ; _>>=_  = bindTC
    }
