-- Everything is strictly positive, but Agda doesn't see this.
{-# OPTIONS --no-positivity-check #-}

module Generic.Core where

open import Generic.Lib.Prelude public

infix  4 _≤ℓ_
infixr 5 _⇒_ _⊛_

_≤ℓ_ : Level -> Level -> Set
α ≤ℓ β = α ⊔ β ≡ β

Pi : ∀ {α β} i -> (A : Set α) -> (< relevance i > A -> Set β) -> Set (α ⊔ β)
Pi (arg-info expl rel) A B =   (x : A)  -> B (relv x)
Pi (arg-info expl irr) A B = . (x : A)  -> B (irrv x)
Pi (arg-info impl rel) A B =   {x : A}  -> B (relv x)
Pi (arg-info impl irr) A B = . {x : A}  -> B (irrv x)
Pi (arg-info inst rel) A B =  {{x : A}} -> B (relv x)
Pi (arg-info inst irr) A B = .{{x : A}} -> B (irrv x)

lamPi : ∀ {α β} {A : Set α} i {B : < relevance i > A -> Set β} -> (∀ x -> B x) -> Pi i A B
lamPi (arg-info expl rel) f = λ x -> f (relv x)
lamPi (arg-info expl irr) f = λ x -> f (irrv x)
lamPi (arg-info impl rel) f = f _
lamPi (arg-info impl irr) f = f _
lamPi (arg-info inst rel) f = f _
lamPi (arg-info inst irr) f = f _

appPi : ∀ {α β} {A : Set α} i {B : < relevance i > A -> Set β} -> Pi i A B -> ∀ x -> B x
appPi (arg-info expl rel) f (relv x) = f x
appPi (arg-info expl irr) f (irrv x) = f x
appPi (arg-info impl rel) y (relv x) = y
appPi (arg-info impl irr) y (irrv x) = y
appPi (arg-info inst rel) y (relv x) = y
appPi (arg-info inst irr) y (irrv x) = y

Coerce′ : ∀ {α β} -> α ≡ β -> Set α -> Set β
Coerce′ refl = id

coerce′ : ∀ {α β} {A : Set α} -> (q : α ≡ β) -> A -> Coerce′ q A
coerce′ refl = id

uncoerce′ : ∀ {α β} {A : Set α} -> (q : α ≡ β) -> Coerce′ q A -> A
uncoerce′ refl = id

inspectUncoerce′ : ∀ {α β} {A : Set α}
                 -> (q : α ≡ β) -> (p : Coerce′ q A) -> ∃ λ x -> p ≡ coerce′ q x
inspectUncoerce′ refl x = x , refl

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

qcoerce : ∀ {α β} {A : Set α} {q : α ≡ β} -> A -> Coerce q A
qcoerce {q = refl} = coerce

mutual
  Binder : ∀ {ι} α β γ -> Arg-info -> ι ⊔ lsuc (α ⊔ β) ≡ γ -> Set ι -> Set γ
  Binder α β γ i q I = Coerce q (∃ λ (A : Set α) -> < relevance i > A -> Desc I β)

  data Desc {ι} (I : Set ι) β : Set (ι ⊔ lsuc β) where
    var : I -> Desc I β
    π   : ∀ {α} i
        -> (q : α ≤ℓ β)
        -> Binder α β _ i (cong (λ αβ -> ι ⊔ lsuc αβ) q) I
        -> Desc I β
    _⊛_ : Desc I β -> Desc I β -> Desc I β

pattern explDPi A D = π (arg-info expl rel) _ (coerce (A , D))
pattern implDPi A D = π (arg-info impl rel) _ (coerce (A , D))
pattern instDPi A D = π (arg-info inst rel) _ (coerce (A , D))

{-# DISPLAY π (arg-info expl rel) _ (coerce (A , D)) = explDPi A D #-}
{-# DISPLAY π (arg-info impl rel) _ (coerce (A , D)) = implDPi A D #-}
{-# DISPLAY π (arg-info inst rel) _ (coerce (A , D)) = instDPi A D #-}

_⇒_ : ∀ {ι α β} {I : Set ι} {{q : α ≤ℓ β}} -> Set α -> Desc I β -> Desc I β
_⇒_ {{q}} A D = π (arg-info expl rel) q (qcoerce (A , λ _ -> D))

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
  Extend (var i)   B j = Lift (i ≡ j)
  Extend (π i q C) B j = Extendᵇ i C q B j
  Extend (D ⊛ E)   B j = ⟦ D ⟧ B × Extend E B j

  Extendᵇ : ∀ {α ι β γ q} {I : Set ι} i
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
