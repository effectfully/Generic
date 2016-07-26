module Generic.Property.Eq where

open import Generic.Core

SemEq : ∀ {i β} {I : Set i} -> Desc I β -> Set
SemEq (var i)   = ⊤
SemEq (π q v C) = ⊥
SemEq (D ⊛ E)   = SemEq D × SemEq E

mutual
  ExtendEq : ∀ {i β} {I : Set i} -> Desc I β -> Set β
  ExtendEq (var i)   = ⊤
  ExtendEq (π q v C) = ExtendEqᵇ C q
  ExtendEq (D ⊛ E)   = SemEq D × ExtendEq E

  ExtendEqᵇ : ∀ {α ι β γ q} {I : Set ι} -> Binder α β γ q I -> α ≤ℓ β -> Set β
  ExtendEqᵇ (coerce (A , D)) q = Coerce′ q $ Eq A × ∀ {x} -> ExtendEq (D x)

instance
  {-# TERMINATING #-} -- Why?
  DataEq : ∀ {i β} {I : Set i} {D : Data I β} {j}
             {{eqD : All ExtendEq (constructors D)}} -> Eq (μ D j)
  DataEq {ι} {β = β} {I = I} {D = D₀} = record { _≟_ = decMu } where
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
        split q eqC λ eqA eqD -> splitWith₂ q _#_ p₁ p₂ λ x₁ x₂ e₁ e₂ ->
          _≟_ {{eqA}} x₁ x₂ <,>ᵈᵒ decExtend (D x₁) {{eqD}} e₁

      decAny : ∀ {j} (Ds : List (Desc I β)) {{eqD : All ExtendEq Ds}}
             -> ∀ d a b ns -> IsSet (Node D₀ (packData d a b Ds ns) j)
      decAny  []                         d a b  ns      () ()
      decAny (D ∷ [])     {{eqD , _}}    d a b  ns      e₁ e₂ = decExtend D {{eqD}} e₁ e₂
      decAny (D ∷ E ∷ Ds) {{eqD , eqDs}} d a b (_ , ns) s₁ s₂ =
        decSum (decExtend D {{eqD}}) (decAny (E ∷ Ds) {{eqDs}} d a b ns) s₁ s₂

      decMu : ∀ {j} -> IsSet (μ D₀ j)
      decMu (node e₁) (node e₂) = dcong node node-inj $ decAny (constructors D₀)
                                                               (dataName     D₀)
                                                               (paramsType   D₀)
                                                               (indicesType  D₀)
                                                               (consNames    D₀)
                                                                e₁
                                                                e₂
