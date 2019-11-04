module Generic.Function.Elim where

open import Generic.Core

AllAny : ∀ {ι α β γ δ} {I : Set ι} {A : Set α} {C : I -> Set γ}
       -> (B : I -> A -> Set β)
       -> (∀ x -> (∀ {j} -> B j x -> C j) -> Set δ)
       -> (xs : List A)
       -> (∀ {j} -> Any (B j) xs -> C j)
       -> Set δ
AllAny B D  []          k = ⊤
AllAny B D (x ∷ [])     k = D x k
AllAny B D (x ∷ y ∷ xs) k = D x (k ∘ inj₁) × AllAny B D (y ∷ xs) (k ∘ inj₂)

data VarView {ι β} {I : Set ι} : Desc I β -> Set where
  yes-var : ∀ {i} -> VarView (var i)
  no-var  : ∀ {D} -> VarView  D

varView : ∀ {ι β} {I : Set ι} -> (D : Desc I β) -> VarView D
varView (var i) = yes-var
varView  D      = no-var

mutual
  Hyp : ∀ {ι β γ} {I : Set ι} {B}
      -> (∀ {i} -> B i -> Set γ) -> (D : Desc I β) -> ⟦ D ⟧ B -> Set (β ⊔ γ)
  Hyp {β = β} C (var i)    y      = Lift β (C y)
  Hyp         C (π i q D)  f      = Hypᵇ i C D f
  Hyp         C (D ⊛ E)   (x , y) = Hyp C D x × Hyp C E y

  Hypᵇ : ∀ {ι α β γ δ q q′} {I : Set ι} {B} i
       -> (∀ {i} -> B i -> Set γ) -> (D : Binder α β δ i q′ I) -> ⟦ i / D ⟧ᵇ q B -> Set (β ⊔ γ)
  Hypᵇ {γ = γ} {q = q} i C (coerce (A , D)) f =
    Coerce′ (cong (γ ⊔_) q) $ Pi i A λ x -> Hyp C (D x) (appPi i (uncoerce′ q f) x)

mutual
  Elim : ∀ {ι β γ} {I : Set ι} {B}
       -> (∀ {i} -> B i -> Set γ)
       -> (D : Desc I β)
       -> (∀ {j} -> Extend D B j -> B j)
       -> Set (β ⊔ γ)
  Elim {β = β} C (var i)   k = Lift β (C (k lrefl))
  Elim         C (π i q D) k = Elimᵇ i C D k
  Elim         C (D ⊛ E)   k with varView D
  ... | yes-var = ∀ {x} -> C x -> Elim C E (k ∘ _,_ x)
  ... | no-var  = ∀ {x} -> Hyp C D x -> Elim C E (k ∘ _,_ x)

  Elimᵇ : ∀ {ι α β γ δ q q′} {I : Set ι} {B} i
        -> (∀ {i} -> B i -> Set γ)
        -> (D : Binder α β δ i q′ I)
        -> (∀ {j} -> Extendᵇ i D q B j -> B j)
        -> Set (β ⊔ γ)
  Elimᵇ {γ = γ} {q = q} i C (coerce (A , D)) k =
    Coerce′ (cong (γ ⊔_) q) $ Pi i A λ x -> Elim C (D x) (k ∘ coerce′ q ∘ _,_ x)

module _ {ι β γ} {I : Set ι} {D₀ : Data (Desc I β)} (C : ∀ {j} -> μ D₀ j -> Set γ) where
  K : Name -> Type -> Type -> (Ds : List (Desc I β)) -> All (const Name) Ds -> Set (ι ⊔ β)
  K d a b Ds ns = ∀ {j} -> Node D₀ (packData d a b Ds ns) j -> μ D₀ j

  Elims : ∀ d a b (Ds : List (Desc I β)) ns -> K d a b Ds ns -> Set (β ⊔ γ)
  Elims d a b Ds ns = AllAny (λ j D -> Extend D (μ D₀) j) (Elim C) Ds

  module _ (hs : Elims (dataName  D₀)
                       (parsTele  D₀)
                       (indsTele  D₀)
                       (consTypes D₀)
                       (consNames D₀)
                        node) where
    {-# TERMINATING #-}
    mutual
      elimHyp : (D : Desc I β) -> (d : ⟦ D ⟧ (μ D₀)) -> Hyp C D d
      elimHyp (var i)    d      = lift (elim d)
      elimHyp (π i q D)  f      = elimHypᵇ i D f
      elimHyp (D ⊛ E)   (x , y) = elimHyp D x , elimHyp E y

      elimHypᵇ : ∀ {α δ q q′} i
               -> (D : Binder α β δ i q′ I)
               -> (f : ⟦ i / D ⟧ᵇ q (μ D₀))
               -> Hypᵇ i C D f
      elimHypᵇ {q = q} i (coerce (A , D)) f =
        coerce′ (cong (_⊔_ γ) q) (lamPi i λ x -> elimHyp (D x) (appPi i (uncoerce′ q f) x))

      elimExtend : ∀ {j}
                 -> (D : Desc I β) {k : ∀ {j} -> Extend D (μ D₀) j -> μ D₀ j}
                 -> Elim C D k
                 -> (e : Extend D (μ D₀) j)
                 -> C (k e)
      elimExtend (var i)   z  lrefl  = lower z
      elimExtend (π i q D) h  p      = elimExtendᵇ i D h p
      elimExtend (D ⊛ E)   h (d , e) with varView D
      ... | yes-var = elimExtend E (h (elim d))  e
      ... | no-var  = elimExtend E (h (elimHyp D d)) e

      elimExtendᵇ : ∀ {α δ q q′ j} i
                  -> (D : Binder α β δ i q′ I) {k : ∀ {j} -> Extendᵇ i D q (μ D₀) j -> μ D₀ j}
                  -> Elimᵇ i C D k
                  -> (p : Extendᵇ i D q (μ D₀) j)
                  -> C (k p)
      elimExtendᵇ {q = q} i (coerce (A , D)) h p with p | inspectUncoerce′ q p
      ... | _ | (x , e) , refl = elimExtend (D x) (appPi i (uncoerce′ (cong (γ ⊔_) q) h) x) e

      elimAny : ∀ {j} (Ds : List (Desc I β)) d a b ns {k : K d a b Ds ns}
              -> Elims d a b Ds ns k -> (a : Node D₀ (packData d a b Ds ns) j) -> C (k a)
      elimAny  []          d a b  tt       tt       ()
      elimAny (D ∷ [])     d a b (n , ns)  h        e       = elimExtend D h e
      elimAny (D ∷ E ∷ Ds) d a b (n , ns) (h , hs) (inj₁ e) = elimExtend D h e
      elimAny (D ∷ E ∷ Ds) d a b (n , ns) (h , hs) (inj₂ r) = elimAny (E ∷ Ds) d a b ns hs r

      elim : ∀ {j} -> (d : μ D₀ j) -> C d
      elim (node e) = elimAny (consTypes D₀)
                              (dataName  D₀)
                              (parsTele  D₀)
                              (indsTele  D₀)
                              (consNames D₀)
                               hs
                               e
