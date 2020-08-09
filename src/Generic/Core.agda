-- Everything is strictly positive, but Agda doesn't see this.
{-# OPTIONS --no-positivity-check #-}

module Generic.Core where

open import Generic.Lib.Prelude public

infix  4 _≤ℓ_
infixr 5 _⇒_ _⊛_

_≤ℓ_ : Level -> Level -> Set
α ≤ℓ β = α ⊔ β ≡ β

mutual
  Binder : ∀ {ι} α β γ -> ArgInfo -> ι ⊔ lsuc (α ⊔ β) ≡ γ -> Set ι -> Set γ
  Binder α β γ i q I = Coerce q (∃ λ (A : Set α) -> < relevance i > A -> Desc I β)

  data Desc {ι} (I : Set ι) β : Set (ι ⊔ lsuc β) where
    var : I -> Desc I β
    π   : ∀ {α} i
        -> (q : α ≤ℓ β)
        -> Binder α β _ i (cong (λ αβ -> ι ⊔ lsuc αβ) q) I
        -> Desc I β
    _⊛_ : Desc I β -> Desc I β -> Desc I β

pattern DPi i A D = π i refl (coerce (A , D))

{-# DISPLAY π i refl (coerce (A , D)) = DPi i A D #-}

pattern explRelDPi A D = DPi explRelInfo A D
pattern explIrrDPi A D = DPi explIrrInfo A D
pattern implRelDPi A D = DPi implRelInfo A D
pattern implIrrDPi A D = DPi implIrrInfo A D
pattern instRelDPi A D = DPi instRelInfo A D
pattern instIrrDPi A D = DPi instIrrInfo A D

{-# DISPLAY DPi explRelInfo A D = explRelDPi A D #-}
{-# DISPLAY DPi explIrrInfo A D = explIrrDPi A D #-}
{-# DISPLAY DPi implRelInfo A D = implRelDPi A D #-}
{-# DISPLAY DPi implIrrInfo A D = implIrrDPi A D #-}
{-# DISPLAY DPi instRelInfo A D = instRelDPi A D #-}
{-# DISPLAY DPi instIrrInfo A D = instIrrDPi A D #-}

_⇒_ : ∀ {ι α β} {I : Set ι} {{q : α ≤ℓ β}} -> Set α -> Desc I β -> Desc I β
_⇒_ {{q}} A D = π (explRelInfo) q (qcoerce (A , λ _ -> D))

mutual
  ⟦_⟧ : ∀ {ι β} {I : Set ι} -> Desc I β -> (I -> Set β) -> Set β
  ⟦ var i   ⟧ B = B i
  ⟦ π i q C ⟧ B = ⟦ i / C ⟧ᵇ q B
  ⟦ D ⊛ E   ⟧ B = ⟦ D ⟧ B × ⟦ E ⟧ B

  ⟦_/_⟧ᵇ : ∀ {α ι β γ q} {I : Set ι} i
         -> Binder α β γ i q I -> α ≤ℓ β -> (I -> Set β) -> Set β
  ⟦ i / coerce (A , D) ⟧ᵇ q B = Coerce′ q $ Pi i A λ x -> ⟦ D x ⟧ B

mutual
  Extend : ∀ {ι β} {I : Set ι} -> Desc I β -> (I -> Set β) -> I -> Set β
  Extend (var i)   B j = Lift _ (i ≡ j)
  Extend (π i q C) B j = Extendᵇ i C q B j
  Extend (D ⊛ E)   B j = ⟦ D ⟧ B × Extend E B j

  Extendᵇ : ∀ {ι α β γ q} {I : Set ι} i
          -> Binder α β γ i q I -> α ≤ℓ β -> (I -> Set β) -> I -> Set β
  Extendᵇ i (coerce (A , D)) q B j = Coerce′ q $ ∃ λ x -> Extend (D x) B j

module _ {ι β} {I : Set ι} (D : Data (Desc I β)) where
  mutual
    data μ j : Set β where
      node : Node D j -> μ j

    Node : Data (Desc I β) -> I -> Set β
    Node D j = Any (λ C -> Extend C μ j) (consTypes D)

mutual
  Cons : ∀ {ι β} {I : Set ι} -> (I -> Set β) -> Desc I β -> Set β
  Cons B (var i)   = B i
  Cons B (π i q C) = Consᵇ B i C q
  Cons B (D ⊛ E)   = ⟦ D ⟧ B -> Cons B E

  Consᵇ : ∀ {ι α β γ q} {I : Set ι}
        -> (I -> Set β) -> ∀ i -> Binder α β γ i q I -> α ≤ℓ β -> Set β
  Consᵇ B i (coerce (A , D)) q = Coerce′ q $ Pi i A λ x -> Cons B (D x)

cons : ∀ {ι β} {I : Set ι} {D} -> (D₀ : Data (Desc I β)) -> D ∈ consTypes D₀ -> Cons (μ D₀) D
cons {D = D} D₀ p = go D λ e ->
  node (mapAny (consTypes D₀) (λ q -> subst (λ E -> Extend E _ _) q e) p) where
    mutual
      go : ∀ {ι β} {I : Set ι} {B : I -> Set β}
         -> (D : Desc I β) -> (∀ {j} -> Extend D B j -> B j) -> Cons B D
      go (var i)   k = k lrefl
      go (π a q C) k = goᵇ a C k
      go (D ⊛ E)   k = λ x -> go E (k ∘ _,_ x)

      goᵇ : ∀ {ι α β γ q q′} {I : Set ι} {B : I -> Set β} i
          -> (C : Binder α β γ i q′ I) -> (∀ {j} -> Extendᵇ i C q B j -> B j) -> Consᵇ B i C q
      goᵇ {q = q} i (coerce (A , D)) k =
        coerce′ q $ lamPi i λ x -> go (D x) (k ∘ coerce′ q ∘ _,_ x)

allCons : ∀ {ι β} {I : Set ι} -> (D : Data (Desc I β)) -> All (Cons (μ D)) (consTypes D)
allCons D = allIn _ (cons D)

node-inj : ∀ {i β} {I : Set i} {D : Data (Desc I β)} {j} {e₁ e₂ : Node D D j}
         -> node {D = D} e₁ ≡ node e₂ -> e₁ ≡ e₂
node-inj refl = refl

μ′ : ∀ {β} -> Data (Desc ⊤₀ β) -> Set β
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
