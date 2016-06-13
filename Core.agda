module Generic.Core where

open import Generic.Prelude

Pi : ∀ {α β} -> Bool -> (A : Set α) -> (A -> Set β) -> Set (α ⊔ β)
Pi true  A B = (x : A) -> B x
Pi false A B = {x : A} -> B x

Coerce′ : ∀ {α β} -> α ≡ β -> Set α -> Set β
Coerce′ refl = id

Coerce : ∀ {α β} -> α ≡ β -> Set α -> Set β
Coerce q A = Apply (λ q -> Coerce′ q A) q

uncoerce : ∀ {α β} {A : Set α} {q : α ≡ β} -> Coerce q A -> A
uncoerce {q = refl} = detag

split : ∀ {α β γ δ} {A : Set α} {B : A -> Set β} {C : Set γ}
      -> (q : α ⊔ β ≡ δ) -> Coerce′ q (Σ A B) -> (∀ x -> B x -> C) -> C
split q p g = uncurry g (uncoerce (tagWith q p))

transform : ∀ {α β γ δ ε} {A : Set α} {B : A -> Set β} {q₁ : α ⊔ β ≡ γ} {{q₂ : δ ≡ ε}}
          -> Coerce q₁ (Σ A B) -> (∀ x -> B x -> Set δ) -> Set ε
transform {q₁ = q₁} {{q₂}} p C = split q₁ (detag p) λ x y -> Coerce′ q₂ (C x y)

splitWith₂ : ∀ {α β γ δ} {A : Set α} {B : A -> Set β}
           -> (q : α ⊔ β ≡ δ)
           -> (C : ∀ {δ} {r : α ⊔ β ≡ δ} -> Coerce′ r (Σ A B) -> Coerce′ r (Σ A B) -> Set γ)
           -> (p₁ p₂ : Coerce′ q (Σ A B))
           -> (∀ x₁ x₂ y₁ y₂ -> C {r = refl} (x₁ , y₁) (x₂ , y₂))
           -> C {r = q} p₁ p₂
splitWith₂ refl C (x₁ , y₁) (x₂ , y₂) g = g x₁ x₂ y₁ y₂

data Shape : Set where
  varˢ : Shape
  piˢ  : Shape -> Shape
  _⊛ˢ_ : Shape -> Shape -> Shape 

module _ {ι} (I : Set ι) β where
  data Desc : Shape -> Set (ι ⊔ lsuc β) where
    var : I -> Desc varˢ
    pi  : ∀ {α s} {{q : α ⊔ β ≡ β}}
        -> Bool
        -> Coerce (cong (λ αβ -> ι ⊔ lsuc αβ) q) (∃ λ (A : Set α) -> A -> Desc s)
        -> Desc (piˢ s)
    _⊛_ : ∀ {s t} -> Desc s -> Desc t -> Desc (s ⊛ˢ t)

pattern π  A D = pi true  (tag (A , D))
pattern πᵢ A D = pi false (tag (A , D))

⟦_⟧ : ∀ {ι β s} {I : Set ι} -> Desc I β s -> (I -> Set β) -> Set β
⟦ var i  ⟧ B = B i
⟦ pi b P ⟧ B = transform P λ A D -> Pi b A λ x -> ⟦ D x ⟧ B
⟦ D ⊛ E  ⟧ B = ⟦ D ⟧ B × ⟦ E ⟧ B

Extend : ∀ {ι β s} {I : Set ι} -> Desc I β s -> (I -> Set β) -> I -> Set β
Extend (var i)  B j = Lift (i ≡ j)
Extend (pi b P) B j = transform P λ A D -> ∃ λ x -> Extend (D x) B j
Extend (D ⊛ E)  B j = ⟦ D ⟧ B × Extend E B j

Data : ∀ {ι} -> Set ι -> ∀ β -> Set (ι ⊔ lsuc β)
Data I β = IList (Desc I β)

record μ {ι β} {I : Set ι} (Ds : Data I β) j : Set β where
  inductive
  constructor node
  field knot : Any (λ D -> Extend D (μ Ds) j) Ds

-- data μ {ι β} {I : Set ι} (Ds : Data I β) j : Set β where
--   node : Any (λ D -> Extend D (μ Ds) j) Ds -> μ Ds j

SemEq : ∀ {i β s} {I : Set i} -> Desc I β s -> Set
SemEq (var i)  = ⊤
SemEq (pi b P) = ⊥
SemEq (D ⊛ E)  = SemEq D × SemEq E

ExtendEq : ∀ {i β s} {I : Set i} -> Desc I β s -> Set β
ExtendEq (var i)  = ⊤
ExtendEq (pi b P) = transform P λ A D -> Eq A × ∀ x -> ExtendEq (D x)
ExtendEq (D ⊛ E)  = SemEq D × ExtendEq E

node-inj : ∀ {i β} {I : Set i} {Ds : Data I β} {j} {e₁ e₂ : Any (λ D -> Extend D (μ Ds) j) Ds}
         -> node {Ds = Ds} e₁ ≡ node e₂ -> e₁ ≡ e₂
node-inj refl = refl

instance
  {-# TERMINATING #-}
  DescEq : ∀ {i β} {I : Set i} {Ds : Data I β} {j} {{eqD : All ExtendEq Ds}} -> Eq (μ Ds j)
  DescEq {ι} {β = β} {I} {Ds = Ds₀} = record { _≟_ = decMu } where
    mutual
      decSem : ∀ {s} -> (D : Desc I β s) {{eqD : SemEq D}} -> IsSet (⟦ D ⟧ (μ Ds₀))
      decSem (var i)                       d₁        d₂       = decMu d₁ d₂
      decSem (pi {{q}} b P) {{()}}
      decSem (D ⊛ E)        {{eqD , eqE}} (x₁ , y₁) (x₂ , y₂) =
        decSem D {{eqD}} x₁ x₂ <,>ᵈ decSem E {{eqE}} y₁ y₂

      decExtend : ∀ {s j} -> (D : Desc I β s) {{eqD : ExtendEq D}} -> IsSet (Extend D (μ Ds₀) j)
      decExtend (var i)                       lrefl     lrefl    = yes refl
      decExtend (pi {{q}} b P) {{eqP}}        p₁        p₂       with uncoerce P
      ... | A , D = split q eqP λ eqA eqD ->
                      splitWith₂ q _#_ p₁ p₂ λ x₁ x₂ e₁ e₂ ->
                        _≟_ {{eqA}} x₁ x₂ <,>ᵈᵒ decExtend (D x₁) {{eqD x₁}} e₁
      decExtend (D ⊛ E)        {{eqD , eqE}} (x₁ , e₁) (x₂ , e₂) =
        decSem D {{eqD}} x₁ x₂ <,>ᵈ decExtend E {{eqE}} e₁ e₂

      decAny : ∀ {j}
             -> (Ds : Data I β) {{eqDs : All ExtendEq Ds}}
             -> IsSet (Any (λ D -> Extend D (μ Ds₀) j) Ds)
      decAny  []                         () ()
      decAny (D ∷ [])     {{eqD , tt  }} e₁ e₂ = decExtend D {{eqD}} e₁ e₂
      decAny (D ∷ E ∷ Ds) {{eqD , eqDs}} (inj₁ e₁) (inj₁ e₂) =
        dcong inj₁ inj₁-inj (decExtend D {{eqD}} e₁ e₂)
      decAny (D ∷ E ∷ Ds) {{eqD , eqDs}} (inj₂ a₁) (inj₂ a₂) =
        dcong inj₂ inj₂-inj (decAny (E ∷ Ds) {{eqDs}} a₁ a₂)
      decAny (D ∷ E ∷ Ds) {{eqD , eqDs}} (inj₁ _ ) (inj₂ _ ) = no λ()
      decAny (D ∷ E ∷ Ds) {{eqD , eqDs}} (inj₂ _ ) (inj₁ _ ) = no λ()

      decMu : ∀ {j} -> IsSet (μ Ds₀ j)
      decMu (node a₁) (node a₂) = dcong node node-inj (decAny Ds₀ a₁ a₂)
