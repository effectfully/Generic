-- Everything is positive, but Agda doesn't see this.
{-# OPTIONS --no-positivity-check #-}

module Generic.Core where

open import Generic.Prelude public

infix  4 _≤ℓ_
infixr 5 _⇒_ _⊕_ _⊛_
infixr 4 _,′_

_≤ℓ_ : Level -> Level -> Set
α ≤ℓ β = α ⊔ β ≡ β

codLevel : ∀ {α β} {A : Set α} -> (A -> Set β) -> Level
codLevel {β = β} _ = β

Pi : ∀ {α β} -> Bool -> (A : Set α) -> (A -> Set β) -> Set (α ⊔ β)
Pi true  A B = (x : A) -> B x
Pi false A B = {x : A} -> B x

lam : ∀ {α β} {A : Set α} {B : A -> Set β} b -> (∀ x -> B x) -> Pi b A B
lam true  f = f
lam false f = f _

apply : ∀ {α β} {A : Set α} {B : A -> Set β} b -> Pi b A B -> ∀ x -> B x
apply true  f x = f x
apply false y x = y

data Coerce {β} : ∀ {α} -> α ≡ β -> Set α -> Set β where
  coerce : ∀ {A} -> A -> Coerce refl A

coerce′ : ∀ {α β} {A : Set α} {q : α ≡ β} -> A -> Coerce q A
coerce′ {q = refl} = coerce

mutual
  Binder : ∀ {ι} α β γ -> ι ⊔ lsuc (α ⊔ β) ≡ γ -> Set ι -> Set γ
  Binder α β γ q I = Coerce q (∃ λ (A : Set α) -> A -> Desc I β)

  data Desc {ι} (I : Set ι) β : Set (ι ⊔ lsuc β) where
    var     : I -> Desc I β
    π       : ∀ {α}
            -> (q : α ≤ℓ β) -> Bool -> Binder α β _ (cong (λ αβ -> ι ⊔ lsuc αβ) q) I -> Desc I β
    _⊕_ _⊛_ : Desc I β -> Desc I β -> Desc I β

pattern pi  A D = π _ true  (coerce (A , D))
pattern ipi A D = π _ false (coerce (A , D))

_⇒_ : ∀ {ι α β} {I : Set ι} {{q : α ≤ℓ β}} -> Set α -> Desc I β -> Desc I β
_⇒_ {{q}} A D = π q true (coerce′ (A , λ _ -> D))

mutual
  ⟦_⟧ : ∀ {ι β} {I : Set ι} -> Desc I β -> (I -> Set β) -> Set β
  ⟦ var i   ⟧ B = B i
  ⟦ π q b C ⟧ B = ⟦ C ⟧ᶜ q b B
  ⟦ D ⊕ E   ⟧ B = ⟦ D ⟧ B ⊎ ⟦ E ⟧ B
  ⟦ D ⊛ E   ⟧ B = ⟦ D ⟧ B × ⟦ E ⟧ B

  ⟦_⟧ᶜ : ∀ {α ι β γ q} {I : Set ι}
       -> Binder α β γ q I -> α ≤ℓ β -> Bool -> (I -> Set β) -> Set β
  ⟦ coerce (A , D) ⟧ᶜ q b B = Coerce q $ Pi b A λ x -> ⟦ D x ⟧ B

mutual
  Extend : ∀ {ι β} {I : Set ι} -> Desc I β -> (I -> Set β) -> I -> Set β
  Extend (var i)   B j = Lift (i ≡ j)
  Extend (π q b C) B j = Extendᶜ C q b B j
  Extend (D ⊕ E)   B j = Extend D B j ⊎ Extend E B j
  Extend (D ⊛ E)   B j = ⟦ D ⟧ B × Extend E B j

  Extendᶜ : ∀ {α ι β γ q} {I : Set ι}
          -> Binder α β γ q I -> α ≤ℓ β -> Bool -> (I -> Set β) -> I -> Set β
  Extendᶜ (coerce (A , D)) q b B j = Coerce q $ ∃ λ x -> Extend (D x) B j

module _ {ι β} {I : Set ι} (D : Desc I β) where
  mutual
    data μ j : Set β where
      node : Node j -> μ j

    Node : I -> Set β
    Node = Extend D μ

node-inj : ∀ {i β} {I : Set i} {D : Desc I β} {j} {e₁ e₂ : Node D j}
         -> node {D = D} e₁ ≡ node e₂ -> e₁ ≡ e₂
node-inj refl = refl

μ′ : ∀ {β} -> Desc ⊤₀ β -> Set β
μ′ D = μ D tt

pos : ∀ {β} -> Desc ⊤₀ β
pos = var tt

pattern #₀ p = node (inj₁ p)
pattern #₁ p = node (inj₂ (inj₁ p))
pattern #₂ p = node (inj₂ (inj₂ (inj₁ p)))
pattern #₃ p = node (inj₂ (inj₂ (inj₂ (inj₁ p))))
pattern #₄ p = node (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ p)))))
pattern #₅ p = node (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ p))))))

pattern !#₀ p = node p
pattern !#₁ p = node (inj₂ p)
pattern !#₂ p = node (inj₂ (inj₂ p))
pattern !#₃ p = node (inj₂ (inj₂ (inj₂ p)))
pattern !#₄ p = node (inj₂ (inj₂ (inj₂ (inj₂ p))))
pattern !#₅ p = node (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ p)))))

pattern _,′_ x y = coerce (x , y)
