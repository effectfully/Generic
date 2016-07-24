module Generic.Property.Reify where

open import Generic.Core

SemReify : ∀ {i β} {I : Set i} -> Cons I β -> Set
SemReify (var i)   = ⊤
SemReify (π q v C) = ⊥
SemReify (D ⊛ E)   = SemReify D × SemReify E

mutual
  ExtendReify : ∀ {i β} {I : Set i} -> Cons I β -> Set β
  ExtendReify (var i)   = ⊤
  ExtendReify (π q v C) = ExtendReifyᵇ C q v
  ExtendReify (D ⊛ E)   = SemReify D × ExtendReify E

  ExtendReifyᵇ : ∀ {α ι β γ q} {I : Set ι}
               -> Binder α β γ q I -> α ≤ℓ β -> Visibility -> Set β
  ExtendReifyᵇ (coerce (A , D)) q expl = Coerce′ q $ Reify A × ∀ {x} -> ExtendReify (D x)
  ExtendReifyᵇ (coerce (A , D)) q v    = Coerce′ q $ ∀ {x} -> ExtendReify (D x)

instance
  {-# TERMINATING #-} -- Why?
  DescReify : ∀ {i β} {I : Set i} {D : Desc I β} {j}
                {{reD : All (ExtendReify ∘ proj₂) D}} -> Reify (μ D j)
  DescReify {ι} {β = β} {I = I} {D = D₀} = record { reify = reifyMu } where
    mutual
      reifySem : ∀ D {{reD : SemReify D}} -> ⟦ D ⟧ (μ D₀) -> Term
      reifySem (var i)                  d      = reifyMu d
      reifySem (π q v C) {{()}}
      reifySem (D ⊛ E)   {{reD , reE}} (x , y) =
        vis₂ con (quote _,_) (reifySem D {{reD}} x) (reifySem E {{reE}} y)

      reifyExtend : ∀ {j} D {{reD : ExtendReify D}} -> Extend D (μ D₀) j -> List Term
      reifyExtend (var i)                  lrefl  = []
      reifyExtend (π q v C)                p      = reifyExtendᵇ C q v p
      reifyExtend (D ⊛ E)   {{reD , reE}} (x , e) =
        reifySem D {{reD}} x ∷ reifyExtend E {{reE}} e

      reifyExtendᵇ : ∀ {α γ q j} (C : Binder α β γ q I) q v {{reC : ExtendReifyᵇ C q v}}
                   -> Extendᵇ C q (μ D₀) j -> List Term
      reifyExtendᵇ (coerce (A , D)) q expl {{reC}} p =
        split q reC λ reA reD -> split q p λ x e ->
          reify {{reA}} x ∷ reifyExtend (D x) {{reD}} e
      reifyExtendᵇ (coerce (A , D)) q impl {{reC}} p =
        split q p λ x e -> reifyExtend (D x) {{uncoerce′ q reC}} e
      reifyExtendᵇ (coerce (A , D)) q inst {{reC}} p =
        split q p λ x e -> reifyExtend (D x) {{uncoerce′ q reC}} e

      reifyCons : ∀ {j} (C : Name × Cons I β) {{reC : ExtendReify (proj₂ C)}}
                -> Extend (proj₂ C) (μ D₀) j -> Term
      reifyCons (n , C) e = vis con n (reifyExtend C e)

      reifyAny : ∀ {j} (D : Desc I β) {{reD : All (ExtendReify ∘ proj₂) D}}
               -> Any (proj₂ >>> λ C -> Extend C (μ D₀) j) D -> Term
      reifyAny  []                         ()
      reifyAny (C ∷ [])     {{reC , _}}    e       = reifyCons C {{reC}} e
      reifyAny (C ∷ C′ ∷ D) {{reC , reD}} (inj₁ e) = reifyCons C {{reC}} e
      reifyAny (C ∷ C′ ∷ D) {{reC , reD}} (inj₂ a) = reifyAny (C′ ∷ D) {{reD}} a

      reifyMu : ∀ {j} -> μ D₀ j -> Term
      reifyMu (node e) = reifyAny D₀ e
