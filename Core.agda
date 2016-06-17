module Generic.Core where

open import Generic.Prelude public
open import Generic.Coerce  public

infixr 5 _⇒_ _⊛_

Pi : ∀ {α β} -> Bool -> (A : Set α) -> (A -> Set β) -> Set (α ⊔ β)
Pi true  A B = (x : A) -> B x
Pi false A B = {x : A} -> B x

lam : ∀ {α β} {A : Set α} {B : A -> Set β} b -> (∀ x -> B x) -> Pi b A B
lam true  f = f
lam false f = f _

apply : ∀ {α β} {A : Set α} {B : A -> Set β} b -> Pi b A B -> ∀ x -> B x
apply true  f x = f x
apply false y x = y

data Shape : Set where
  varˢ : Shape
  πˢ   : Shape -> Shape
  _⊛ˢ_ : Shape -> Shape -> Shape 

data Desc {ι} (I : Set ι) β : Shape -> Set (ι ⊔ lsuc β) where
  var : I -> Desc I β varˢ
  π   : ∀ {α s} {{q : α ⊔ β ≡ β}}
      -> Bool
      -> Coerce (cong (λ αβ -> ι ⊔ lsuc αβ) q) (∃ λ (A : Set α) -> A -> Desc I β s)
      -> Desc I β (πˢ s)
  _⊛_ : ∀ {s t} -> Desc I β s -> Desc I β t -> Desc I β (s ⊛ˢ t)

pattern pi  A D = π true  (tag (A , D))
pattern ipi A D = π false (tag (A , D))

⟦_⟧ : ∀ {ι β s} {I : Set ι} -> Desc I β s -> (I -> Set β) -> Set β
⟦ var i ⟧ B = B i
⟦ π b P ⟧ B = Transform P λ A D -> Pi b A λ x -> ⟦ D x ⟧ B
⟦ D ⊛ E ⟧ B = ⟦ D ⟧ B × ⟦ E ⟧ B

Extend : ∀ {ι β s} {I : Set ι} -> Desc I β s -> (I -> Set β) -> I -> Set β
Extend (var i) B j = Lift (i ≡ j)
Extend (π b P) B j = Transform P λ A D -> ∃ λ x -> Extend (D x) B j
Extend (D ⊛ E) B j = ⟦ D ⟧ B × Extend E B j

Data : ∀ {ι} -> Set ι -> ∀ β -> Set (ι ⊔ lsuc β)
Data I β = IList (Desc I β)

-- record μ {ι β} {I : Set ι} (Ds : Data I β) j : Set β where
--   inductive
--   constructor node
--   field knot : Any (λ D -> Extend D (μ Ds) j) Ds

data μ {ι β} {I : Set ι} (Ds : Data I β) j : Set β where
  node : Any (λ D -> Extend D (μ Ds) j) Ds -> μ Ds j

node-inj : ∀ {i β} {I : Set i} {Ds : Data I β} {j} {e₁ e₂ : Any (λ D -> Extend D (μ Ds) j) Ds}
         -> node {Ds = Ds} e₁ ≡ node e₂ -> e₁ ≡ e₂
node-inj refl = refl

_⇒_ : ∀ {ι α β s} {I : Set ι} {{q : α ⊔ β ≡ β}}
    -> (A : Set α) -> Desc I β s -> Desc I β (πˢ s)
A ⇒ D = π true (coerce (A , λ _ -> D))

μ′ : ∀ {β} -> Data ⊤₀ β -> Set β
μ′ Ds = μ Ds tt

pos : ∀ {β} -> Desc ⊤₀ β varˢ
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
