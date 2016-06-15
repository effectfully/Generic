module Generic.Property.Eq where

open import Generic.Core

SemEq : ∀ {i β s} {I : Set i} -> Desc I β s -> Set
SemEq (var i) = ⊤
SemEq (π b P) = ⊥
SemEq (D ⊛ E) = SemEq D × SemEq E

ExtendEq : ∀ {i β s} {I : Set i} -> Desc I β s -> Set β
ExtendEq (var i) = ⊤
ExtendEq (π b P) = transform P λ A D -> Eq A × ∀ {x} -> ExtendEq (D x)
ExtendEq (D ⊛ E) = SemEq D × ExtendEq E

instance
  {-# TERMINATING #-}
  DescEq : ∀ {i β} {I : Set i} {Ds : Data I β} {j} {{eqD : All ExtendEq Ds}} -> Eq (μ Ds j)
  DescEq {ι} {β = β} {I} {Ds = Ds₀} = record { _≟_ = decMu } where
    mutual
      decSem : ∀ {s} -> (D : Desc I β s) {{eqD : SemEq D}} -> IsSet (⟦ D ⟧ (μ Ds₀))
      decSem (var i)                d₁        d₂       = decMu d₁ d₂
      decSem (π b P) {{()}}
      decSem (D ⊛ E) {{eqD , eqE}} (x₁ , y₁) (x₂ , y₂) =
        decSem D {{eqD}} x₁ x₂ <,>ᵈ decSem E {{eqE}} y₁ y₂

      decExtend : ∀ {s j} -> (D : Desc I β s) {{eqD : ExtendEq D}} -> IsSet (Extend D (μ Ds₀) j)
      decExtend (var i)                      lrefl     lrefl    = yes refl
      decExtend (π {{q}} b P) {{eqP}}        p₁        p₂       =
        split′ q eqP λ eqA eqD ->
          splitWith₂ q _#_ p₁ p₂ λ x₁ x₂ e₁ e₂ ->
            _≟_ {{eqA}} x₁ x₂ <,>ᵈᵒ decExtend (unproj₂ P x₁) {{eqD}} e₁
      decExtend (D ⊛ E)       {{eqD , eqE}} (x₁ , e₁) (x₂ , e₂) =
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
