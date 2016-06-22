module Generic.Property.Eq where

open import Generic.Core

SemEq : ∀ {i β s} {I : Set i} -> Desc I β s -> Set
SemEq (var i) = ⊤
SemEq (π b P) = ⊥
SemEq (D ⊕ E) = SemEq D × SemEq E
SemEq (D ⊛ E) = SemEq D × SemEq E

ExtendEq : ∀ {i β s} {I : Set i} -> Desc I β s -> Set β
ExtendEq (var i) = ⊤
ExtendEq (π b P) = Transform P λ A D -> Eq A × ∀ {x} -> ExtendEq (D x)
ExtendEq (D ⊕ E) = ExtendEq D × ExtendEq E
ExtendEq (D ⊛ E) = SemEq D × ExtendEq E

instance
  {-# TERMINATING #-}
  DescEq : ∀ {i β s} {I : Set i} {D : Desc I β s} {j} {{eqD : ExtendEq D}} -> Eq (μ D j)
  DescEq {ι} {β = β} {I = I} {D = D₀} = record { _≟_ = decMu } where
    mutual
      decSem : ∀ {s} -> (D : Desc I β s) {{eqD : SemEq D}} -> IsSet (⟦ D ⟧ (μ D₀))
      decSem (var i)                d₁        d₂       = decMu d₁ d₂
      decSem (π b P) {{()}}
      decSem (D ⊕ E) {{eqD , eqE}}  s₁        s₂       =
        decSum (decSem D {{eqD}}) (decSem E {{eqE}}) s₁ s₂
      decSem (D ⊛ E) {{eqD , eqE}} (x₁ , y₁) (x₂ , y₂) =
        decSem D {{eqD}} x₁ x₂ <,>ᵈ decSem E {{eqE}} y₁ y₂

      decExtend : ∀ {s j} -> (D : Desc I β s) {{eqD : ExtendEq D}} -> IsSet (Extend D (μ D₀) j)
      decExtend (var i)                      lrefl     lrefl    = yes refl
      decExtend (π {{q}} b P) {{eqP}}        p₁        p₂       =
        split′ eqP λ eqA eqD ->
          splitWith₂ q _#_ p₁ p₂ λ x₁ x₂ e₁ e₂ ->
            _≟_ {{eqA}} x₁ x₂ <,>ᵈᵒ decExtend (unproj₂ P x₁) {{eqD}} e₁
      decExtend (D ⊕ E)       {{eqD , eqE}}  s₁        s₂       =
        decSum (decExtend D {{eqD}}) (decExtend E {{eqE}}) s₁ s₂
      decExtend (D ⊛ E)       {{eqD , eqE}} (x₁ , e₁) (x₂ , e₂) =
        decSem D {{eqD}} x₁ x₂ <,>ᵈ decExtend E {{eqE}} e₁ e₂

      decMu : ∀ {j} -> IsSet (μ D₀ j)
      decMu (node e₁) (node e₂) = dcong node node-inj (decExtend D₀ e₁ e₂)
