module Generic.Property.Eq where

open import Generic.Core

SemEq : ∀ {i β} {I : Set i} -> Desc I β -> Set
SemEq (var i)   = ⊤
SemEq (π q b C) = ⊥
SemEq (D ⊕ E)   = SemEq D × SemEq E
SemEq (D ⊛ E)   = SemEq D × SemEq E

mutual
  ExtendEq : ∀ {i β} {I : Set i} -> Desc I β -> Set β
  ExtendEq (var i)   = ⊤
  ExtendEq (π q b C) = ExtendEqᵇ C q b
  ExtendEq (D ⊕ E)   = ExtendEq D × ExtendEq E
  ExtendEq (D ⊛ E)   = SemEq D × ExtendEq E

  ExtendEqᵇ : ∀ {α ι β γ q} {I : Set ι} -> Binder α β γ q I -> α ≤ℓ β -> Bool -> Set β
  ExtendEqᵇ (coerce (A , D)) q b = Coerce′ q $ Eq A × ∀ {x} -> ExtendEq (D x)

instance
  {-# TERMINATING #-} -- Why?
  DescEq : ∀ {i β} {I : Set i} {D : Desc I β} {j} {{eqD : ExtendEq D}} -> Eq (μ D j)
  DescEq {ι} {β = β} {I = I} {D = D₀} = record { _≟_ = decMu } where
    mutual
      decSem : (D : Desc I β) {{eqD : SemEq D}} -> IsSet (⟦ D ⟧ (μ D₀))
      decSem (var i)                  d₁        d₂       = decMu d₁ d₂
      decSem (π q b C) {{()}}
      decSem (D ⊕ E)   {{eqD , eqE}}  s₁        s₂       =
        decSum (decSem D {{eqD}}) (decSem E {{eqE}}) s₁ s₂
      decSem (D ⊛ E)   {{eqD , eqE}} (x₁ , y₁) (x₂ , y₂) =
        decSem D {{eqD}} x₁ x₂ <,>ᵈ decSem E {{eqE}} y₁ y₂

      decExtend : ∀ {j} (D : Desc I β) {{eqD : ExtendEq D}} -> IsSet (Extend D (μ D₀) j)
      decExtend (var i)                  lrefl     lrefl    = yes refl
      decExtend (π q b C)                p₁        p₂       = decExtendᵇ C q b p₁ p₂
      decExtend (D ⊕ E)   {{eqD , eqE}}  s₁        s₂       =
        decSum (decExtend D {{eqD}}) (decExtend E {{eqE}}) s₁ s₂
      decExtend (D ⊛ E)   {{eqD , eqE}} (x₁ , e₁) (x₂ , e₂) =
        decSem D {{eqD}} x₁ x₂ <,>ᵈ decExtend E {{eqE}} e₁ e₂

      decExtendᵇ : ∀ {α γ q j} (C : Binder α β γ q I) q b {{eqC : ExtendEqᵇ C q b}}
                 -> IsSet (Extendᵇ C q b (μ D₀) j)
      decExtendᵇ (coerce (A , D)) q b {{eqC}} p₁ p₂ =
        split q eqC λ eqA eqD ->
          splitWith₂ q _#_ p₁ p₂ λ x₁ x₂ e₁ e₂ ->
            _≟_ {{eqA}} x₁ x₂ <,>ᵈᵒ decExtend (D x₁) {{eqD}} e₁

      decMu : ∀ {j} -> IsSet (μ D₀ j)
      decMu (node e₁) (node e₂) = dcong node node-inj (decExtend D₀ e₁ e₂)
