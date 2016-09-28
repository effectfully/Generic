module Generic.Property.Reify where

open import Generic.Core

data ExplView : Visibility -> Set where
  yes-expl : ExplView expl
  no-expl  : ∀ {v} -> ExplView v

explView : ∀ v -> ExplView v
explView expl = yes-expl
explView v    = no-expl

ExplMaybe : ∀ {α} -> Visibility -> Set α -> Set α
ExplMaybe v A with explView v
... | yes-expl = A
... | no-expl  = ⊤

caseExplMaybe : ∀ {α π} {A : Set α} (P : Visibility -> Set π)
              -> (A -> P expl) -> (∀ {v} -> P v) -> ∀ v -> ExplMaybe v A -> P v
caseExplMaybe P f y v x with explView v
... | yes-expl = f x
... | no-expl  = y

Prod : ∀ {α} β -> Visibility -> Set α -> Set (α ⊔ β) -> Set (α ⊔ β)
Prod β v A B with explView v
... | yes-expl = A × B
... | no-expl  = B

uncurryProd : ∀ {α β γ} {A : Set α} {B : Set (α ⊔ β)} {C : Set γ} v
            -> Prod β v A B -> (ExplMaybe v A -> B -> C) -> C
uncurryProd v p g with explView v | p
... | yes-expl | (x , y) = g x  y
... | no-expl  |  y      = g tt y

SemReify : ∀ {i β} {I : Set i} -> Desc I β -> Set
SemReify (var i)   = ⊤
SemReify (π i q C) = ⊥
SemReify (D ⊛ E)   = SemReify D × SemReify E

mutual
  ExtendReify : ∀ {i β} {I : Set i} -> Desc I β -> Set β
  ExtendReify (var i)   = ⊤
  ExtendReify (π i q C) = ExtendReifyᵇ i C q
  ExtendReify (D ⊛ E)   = SemReify D × ExtendReify E

  ExtendReifyᵇ : ∀ {ι α β γ q} {I : Set ι} i -> Binder α β γ i q I -> α ≤ℓ β -> Set β
  ExtendReifyᵇ {β = β} i (coerce (A , D)) q = Coerce′ q $
    Prod β (visibility i) (Reify A) (∀ {x} -> ExtendReify (D x))

-- Can't reify an irrelevant thing into its relevant representation.
postulate
  reifyᵢ : ∀ {α} {A : Set α} {{aReify : Reify A}} -> .A -> Term

instance
  {-# TERMINATING #-}
  DataReify : ∀ {i β} {I : Set i} {D : Data (Desc I β)} {j}
                {{reD : All ExtendReify (consTypes D)}} -> Reify (μ D j)
  DataReify {ι} {β} {I} {D₀} = record { reify = reifyMu } where
    mutual
      reifySem : ∀ D {{reD : SemReify D}} -> ⟦ D ⟧ (μ D₀) -> Term
      reifySem (var i)                  d      = reifyMu d
      reifySem (π i q C) {{()}}
      reifySem (D ⊛ E)   {{reD , reE}} (x , y) =
        sate _,_ (reifySem D {{reD}} x) (reifySem E {{reE}} y)

      reifyExtend : ∀ {j} D {{reD : ExtendReify D}} -> Extend D (μ D₀) j -> List Term
      reifyExtend (var i)                  lrefl  = []
      reifyExtend (π i q C)                p      = reifyExtendᵇ i C q p
      reifyExtend (D ⊛ E)   {{reD , reE}} (x , e) =
        reifySem D {{reD}} x ∷ reifyExtend E {{reE}} e

      reifyExtendᵇ : ∀ {α γ q j} i (C : Binder α β γ i q I) q′ {{reC : ExtendReifyᵇ i C q′}}
                   -> Extendᵇ i C q′ (μ D₀) j -> List Term
      reifyExtendᵇ i (coerce (A , D)) q {{reC}} p =
        uncurryProd (visibility i) (uncoerce′ q reC) λ mreA reD -> split q p λ x e ->
          let es = reifyExtend (D x) {{reD}} e in
            caseExplMaybe _ (λ reA -> elimRelValue _ (reify {{reA}}) (reifyᵢ {{reA}}) x ∷ es)
                             es
                            (visibility i)
                             mreA

      reifyDesc : ∀ {j} D {{reD : ExtendReify D}} -> Name -> Extend D (μ D₀) j -> Term
      reifyDesc D n e = vis appCon n (reifyExtend D e)

      reifyAny : ∀ {j} (Ds : List (Desc I β)) {{reD : All ExtendReify Ds}}
               -> ∀ d a b ns -> Node D₀ (packData d a b Ds ns) j -> Term
      reifyAny  []                         d a b  tt       ()
      reifyAny (D ∷ [])     {{reD , _}}    d a b (n , ns)  e       = reifyDesc D {{reD}} n e
      reifyAny (D ∷ E ∷ Ds) {{reD , reDs}} d a b (n , ns) (inj₁ e) = reifyDesc D {{reD}} n e
      reifyAny (D ∷ E ∷ Ds) {{reD , reDs}} d a b (n , ns) (inj₂ r) =
        reifyAny (E ∷ Ds) {{reDs}} d a b ns r

      reifyMu : ∀ {j} -> μ D₀ j -> Term
      reifyMu (node e) = reifyAny (consTypes D₀)
                                  (dataName  D₀)
                                  (parsTele  D₀)
                                  (indsTele  D₀)
                                  (consNames D₀)
                                   e
