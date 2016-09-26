module Generic.Property.Reify where

open import Generic.Core

data ExplRelView : Arg-info -> Set where
  yes-explRel : ExplRelView (arg-info expl rel)
  no-explRel  : ∀ {i} -> ExplRelView i

explRelView : ∀ i -> ExplRelView i
explRelView (arg-info expl rel) = yes-explRel
explRelView  i                  = no-explRel

Prod : ∀ {α} β -> Arg-info -> Set α -> Set (α ⊔ β) -> Set (α ⊔ β)
Prod β i A B with explRelView i
... | yes-explRel = A × B
... | no-explRel  = B

ExplRelMaybe : ∀ {α} -> Arg-info -> Set α -> Set α
ExplRelMaybe i A with explRelView i
... | yes-explRel = A
... | no-explRel  = ⊤

caseExplRelMaybe : ∀ {α π} {A : Set α}
                 -> (P : Arg-info -> Set π)
                 -> (A -> P (arg-info expl rel))
                 -> (∀ i -> P i)
                 -> ∀ i
                 -> ExplRelMaybe i A
                 -> P i
caseExplRelMaybe P f g i x with explRelView i
... | yes-explRel = f x
... | no-explRel  = g _

uncurryProd : ∀ {α β γ} {A : Set α} {B : Set (α ⊔ β)} {C : Set γ} i
            -> Prod β i A B -> (ExplRelMaybe i A -> B -> C) -> C
uncurryProd i p g with explRelView i | p
... | yes-explRel | (x , y) = g x  y
... | no-explRel  |  y      = g tt y

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
    Prod β i (Reify A) (∀ {x} -> ExtendReify (D x))

instance
  {-# TERMINATING #-}
  DataReify : ∀ {i β} {I : Set i} {D : Data (Desc I β)} {j}
                {{reD : All ExtendReify (consTypes D)}} -> Reify (μ D j)
  DataReify {ι} {β = β} {I = I} {D = D₀} = record { reify = reifyMu } where
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
        uncurryProd i (uncoerce′ q reC) λ mreA reD -> split q p λ x e ->
          let es = reifyExtend (D x) {{reD}} e in
            caseExplRelMaybe (λ i -> < relevance i > A -> _)
                             (λ reA rx -> reify {{reA}} (unrelv rx) ∷ es)
                             (λ _ _ -> es)
                              i
                              mreA
                              x

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
