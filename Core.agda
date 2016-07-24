-- Everything is strictly positive, but Agda doesn't see this.
{-# OPTIONS --no-positivity-check #-}

module Generic.Core where

open import Generic.Prelude public

infix  4 _≤ℓ_
infixr 5 _⇒_ _⊛_

_≤ℓ_ : Level -> Level -> Set
α ≤ℓ β = α ⊔ β ≡ β

Pi : ∀ {α β} -> Visibility -> (A : Set α) -> (A -> Set β) -> Set (α ⊔ β)
Pi expl A B =  (x : A)  -> B x
Pi impl A B =  {x : A}  -> B x
Pi inst A B = {{x : A}} -> B x

lam : ∀ {α β} {A : Set α} {B : A -> Set β} v -> (∀ x -> B x) -> Pi v A B
lam expl f = f
lam impl f = f _
lam inst f = f _

app : ∀ {α β} {A : Set α} {B : A -> Set β} v -> Pi v A B -> ∀ x -> B x
app expl f x = f x
app impl y x = y
app inst y x = y

Coerce′ : ∀ {α β} -> α ≡ β -> Set α -> Set β
Coerce′ refl = id

uncoerce′ : ∀ {α β} {A : Set α} -> (q : α ≡ β) -> Coerce′ q A -> A
uncoerce′ refl = id

split : ∀ {α β γ δ} {A : Set α} {B : A -> Set β} {C : Set γ}
       -> (q : α ⊔ β ≡ δ) -> Coerce′ q (Σ A B) -> (∀ x -> B x -> C) -> C
split q p g = uncurry g (uncoerce′ q p)

splitWith₂ : ∀ {α β γ δ} {A : Set α} {B : A -> Set β}
           -> (q : α ⊔ β ≡ δ)
           -> (C : ∀ {δ} {r : α ⊔ β ≡ δ} -> Coerce′ r (Σ A B) -> Coerce′ r (Σ A B) -> Set γ)
           -> (p₁ p₂ : Coerce′ q (Σ A B))
           -> (∀ x₁ x₂ y₁ y₂ -> C {r = refl} (x₁ , y₁) (x₂ , y₂))
           -> C {r = q} p₁ p₂
splitWith₂ refl C (x₁ , y₁) (x₂ , y₂) g = g x₁ x₂ y₁ y₂

data Coerce {β} : ∀ {α} -> α ≡ β -> Set α -> Set β where
  coerce : ∀ {A} -> A -> Coerce refl A

gcoerce : ∀ {α β} {A : Set α} {q : α ≡ β} -> A -> Coerce q A
gcoerce {q = refl} = coerce

mutual
  Binder : ∀ {ι} α β γ -> ι ⊔ lsuc (α ⊔ β) ≡ γ -> Set ι -> Set γ
  Binder α β γ q I = Coerce q (∃ λ (A : Set α) -> A -> Cons I β)

  data Cons {ι} (I : Set ι) β : Set (ι ⊔ lsuc β) where
    var : I -> Cons I β
    π   : ∀ {α}
        -> (q : α ≤ℓ β) -> Visibility -> Binder α β _ (cong (λ αβ -> ι ⊔ lsuc αβ) q) I -> Cons I β
    _⊛_ : Cons I β -> Cons I β -> Cons I β

pattern pi   A D = π _ expl (coerce (A , D))
pattern ipi  A D = π _ impl (coerce (A , D))
pattern iipi A D = π _ inst (coerce (A , D))

{-# DISPLAY π q expl (coerce (A , D)) = pi   A D #-}
{-# DISPLAY π q impl (coerce (A , D)) = ipi  A D #-}
{-# DISPLAY π q inst (coerce (A , D)) = iipi A D #-}

_⇒_ : ∀ {ι α β} {I : Set ι} {{q : α ≤ℓ β}} -> Set α -> Cons I β -> Cons I β
_⇒_ {{q}} A D = π q expl (gcoerce (A , λ _ -> D))

mutual
  ⟦_⟧ : ∀ {ι β} {I : Set ι} -> Cons I β -> (I -> Set β) -> Set β
  ⟦ var i   ⟧ B = B i
  ⟦ π q v C ⟧ B = ⟦ C ⟧ᵇ q v B
  ⟦ D ⊛ E   ⟧ B = ⟦ D ⟧ B × ⟦ E ⟧ B

  ⟦_⟧ᵇ : ∀ {α ι β γ q} {I : Set ι}
       -> Binder α β γ q I -> α ≤ℓ β -> Visibility -> (I -> Set β) -> Set β
  ⟦ coerce (A , D) ⟧ᵇ q v B = Coerce′ q $ Pi v A λ x -> ⟦ D x ⟧ B

mutual
  Extend : ∀ {ι β} {I : Set ι} -> Cons I β -> (I -> Set β) -> I -> Set β
  Extend (var i)   B j = Lift (i ≡ j)
  Extend (π q v C) B j = Extendᵇ C q B j
  Extend (D ⊛ E)   B j = ⟦ D ⟧ B × Extend E B j

  Extendᵇ : ∀ {α ι β γ q} {I : Set ι}
          -> Binder α β γ q I -> α ≤ℓ β -> (I -> Set β) -> I -> Set β
  Extendᵇ (coerce (A , D)) q B j = Coerce′ q $ ∃ λ x -> Extend (D x) B j

Desc : ∀ {ι} -> Set ι -> ∀ β -> Set (ι ⊔ lsuc β)
Desc I β = List (Name × Cons I β)

module _ {ι β} {I : Set ι} (D : Desc I β) where
  mutual
    data μ j : Set β where
      node : Node j -> μ j

    Node : I -> Set β
    Node j = Any (proj₂ >>> λ C -> Extend C μ j) D

node-inj : ∀ {i β} {I : Set i} {D : Desc I β} {j} {e₁ e₂ : Node D j}
         -> node {D = D} e₁ ≡ node e₂ -> e₁ ≡ e₂
node-inj refl = refl

μ′ : ∀ {β} -> Desc ⊤₀ β -> Set β
μ′ D = μ D tt

pos : ∀ {β} -> Cons ⊤₀ β
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
