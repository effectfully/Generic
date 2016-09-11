module Generic.Property.Eq where

open import Generic.Core

SemEq : ∀ {i β} {I : Set i} -> Desc I β -> Set
SemEq (var i)   = ⊤
SemEq (π i q C) = ⊥
SemEq (D ⊛ E)   = SemEq D × SemEq E

mutual
  ExtendEq : ∀ {i β} {I : Set i} -> Desc I β -> Set β
  ExtendEq (var i)   = ⊤
  ExtendEq (π i q C) = ExtendEqᵇ i C q
  ExtendEq (D ⊛ E)   = SemEq D × ExtendEq E

  ExtendEqᵇ : ∀ {α ι β γ q} {I : Set ι} i -> Binder α β γ i q I -> α ≤ℓ β -> Set β
  ExtendEqᵇ (arg-info v r) (coerce (A , D)) q = Coerce′ q $ RelEq r A × ∀ {x} -> ExtendEq (D x)

instance
  {-# TERMINATING #-} -- Why?
  DataEq : ∀ {i β} {I : Set i} {D : Data (Desc I β)} {j}
             {{eqD : All ExtendEq (consTypes D)}} -> Eq (μ D j)
  DataEq {ι} {β = β} {I = I} {D = D₀} = record { _≟_ = decMu } where
    mutual
      decSem : ∀ D {{eqD : SemEq D}} -> IsSet (⟦ D ⟧ (μ D₀))
      decSem (var i)                  d₁        d₂       = decMu d₁ d₂
      decSem (π i q C) {{()}}
      decSem (D ⊛ E)   {{eqD , eqE}} (x₁ , y₁) (x₂ , y₂) =
        decSem D {{eqD}} x₁ x₂ <,>ᵈ decSem E {{eqE}} y₁ y₂

      decExtend : ∀ {j} D {{eqD : ExtendEq D}} -> IsSet (Extend D (μ D₀) j)
      decExtend (var i)                  lrefl     lrefl    = yes refl
      decExtend (π i q C)                p₁        p₂       = decExtendᵇ i C q p₁ p₂
      decExtend (D ⊛ E)   {{eqD , eqE}} (x₁ , e₁) (x₂ , e₂) =
        decSem D {{eqD}} x₁ x₂ <,>ᵈ decExtend E {{eqE}} e₁ e₂

      decExtendᵇ : ∀ {α γ q j} i (C : Binder α β γ i q I) q {{eqC : ExtendEqᵇ i C q}}
                 -> IsSet (Extendᵇ i C q (μ D₀) j)
      decExtendᵇ (arg-info v r) (coerce (A , D)) q {{eqC}} p₁ p₂ =
        split q eqC λ eqA eqD -> splitWith₂ q _#_ p₁ p₂ λ x₁ x₂ e₁ e₂ ->
          _≟_ {{EqRelValue {{eqA}}}} x₁ x₂ <,>ᵈᵒ decExtend (D x₁) {{eqD}} e₁

      decAny : ∀ {j} (Ds : List (Desc I β)) {{eqD : All ExtendEq Ds}}
             -> ∀ d a b ns -> IsSet (Node D₀ (packData d a b Ds ns) j)
      decAny  []                         d a b  tt      () ()
      decAny (D ∷ [])     {{eqD , _}}    d a b (_ , ns) e₁ e₂ = decExtend D {{eqD}} e₁ e₂
      decAny (D ∷ E ∷ Ds) {{eqD , eqDs}} d a b (_ , ns) s₁ s₂ =
        decSum (decExtend D {{eqD}}) (decAny (E ∷ Ds) {{eqDs}} d a b ns) s₁ s₂

      decMu : ∀ {j} -> IsSet (μ D₀ j)
      decMu (node e₁) (node e₂) = dcong node node-inj $ decAny (consTypes D₀)
                                                               (dataName  D₀)
                                                               (parsTele  D₀)
                                                               (indsTele  D₀)
                                                               (consNames D₀)
                                                                e₁
                                                                e₂
