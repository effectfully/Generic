module Generic.Property.Eq where

open import Generic.Core

SemEq : ∀ {i β} {I : Set i} -> Cons I β -> Set
SemEq (var i)   = ⊤
SemEq (π q v C) = ⊥
SemEq (D ⊛ E)   = SemEq D × SemEq E

mutual
  ExtendEq : ∀ {i β} {I : Set i} -> Cons I β -> Set β
  ExtendEq (var i)   = ⊤
  ExtendEq (π q v C) = ExtendEqᵇ C q
  ExtendEq (D ⊛ E)   = SemEq D × ExtendEq E

  ExtendEqᵇ : ∀ {α ι β γ q} {I : Set ι} -> Binder α β γ q I -> α ≤ℓ β -> Set β
  ExtendEqᵇ (coerce (A , D)) q = Coerce′ q $ Eq A × ∀ {x} -> ExtendEq (D x)

instance
  {-# TERMINATING #-} -- Why?
  DescEq : ∀ {i β} {I : Set i} {D : Desc I β} {j} {{eqD : All (ExtendEq ∘ proj₂) D}} -> Eq (μ D j)
  DescEq {ι} {β = β} {I = I} {D = D₀} = record { _≟_ = decMu } where
    mutual
      decSem : ∀ D {{eqD : SemEq D}} -> IsSet (⟦ D ⟧ (μ D₀))
      decSem (var i)                  d₁        d₂       = decMu d₁ d₂
      decSem (π q v C) {{()}}
      decSem (D ⊛ E)   {{eqD , eqE}} (x₁ , y₁) (x₂ , y₂) =
        decSem D {{eqD}} x₁ x₂ <,>ᵈ decSem E {{eqE}} y₁ y₂

      decExtend : ∀ {j} D {{eqD : ExtendEq D}} -> IsSet (Extend D (μ D₀) j)
      decExtend (var i)                  lrefl     lrefl    = yes refl
      decExtend (π q v C)                p₁        p₂       = decExtendᵇ C q p₁ p₂
      decExtend (D ⊛ E)   {{eqD , eqE}} (x₁ , e₁) (x₂ , e₂) =
        decSem D {{eqD}} x₁ x₂ <,>ᵈ decExtend E {{eqE}} e₁ e₂

      decExtendᵇ : ∀ {α γ q j} (C : Binder α β γ q I) q {{eqC : ExtendEqᵇ C q}}
                 -> IsSet (Extendᵇ C q (μ D₀) j)
      decExtendᵇ (coerce (A , D)) q {{eqC}} p₁ p₂ =
        split q eqC λ eqA eqD ->
          splitWith₂ q _#_ p₁ p₂ λ x₁ x₂ e₁ e₂ ->
            _≟_ {{eqA}} x₁ x₂ <,>ᵈᵒ decExtend (D x₁) {{eqD}} e₁

      decAny : ∀ {j} (D : Desc I β) {{eqD : All (ExtendEq ∘ proj₂) D}}
             -> IsSet (Any (proj₂ >>> λ C -> Extend C (μ D₀) j) D)
      decAny  []                          () ()
      decAny (C ∷ [])      {{eqC , _}}    e₁ e₂ = decExtend (proj₂ C) {{eqC}} e₁ e₂
      decAny (C₁ ∷ C₂ ∷ D) {{eqC₁ , eqD}} s₁ s₂ =
        decSum (decExtend (proj₂ C₁) {{eqC₁}}) (decAny (C₂ ∷ D) {{eqD}}) s₁ s₂

      decMu : ∀ {j} -> IsSet (μ D₀ j)
      decMu (node e₁) (node e₂) = dcong node node-inj (decAny D₀ e₁ e₂)
