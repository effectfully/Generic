-- Under reconstruction.

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
  no-var  : ∀ {D} -> VarView D

varView : ∀ {ι β} {I : Set ι} -> (D : Desc I β) -> VarView D
varView (var i) = yes-var
varView  D      = no-var

mutual
  Hyp : ∀ {ι β γ} {I : Set ι} {B}
      -> (∀ {i} -> B i -> Set γ) -> (D : Desc I β) -> ⟦ D ⟧ B -> Set (β ⊔ γ)
  Hyp {β = β} C (var i)    y      = Lift {ℓ = β} (C y)
  Hyp         C (π q v D)  f      = Hypᵇ C D f
  Hyp         C (D ⊛ E)   (x , y) = Hyp C D x × Hyp C E y

  Hypᵇ : ∀ {α ι β γ δ q q′ v} {I : Set ι} {B}
       -> (∀ {i} -> B i -> Set γ) -> (D : Binder α β δ q′ I) -> ⟦ D ⟧ᵇ q v B -> Set (β ⊔ γ)
  Hypᵇ {γ = γ} {q = q} {v = v} C (coerce (A , D)) f =
    Coerce′ (cong (γ ⊔_) q) $ Pi v A λ x -> Hyp C (D x) (app v (uncoerce′ q f) x) 

mutual
  Elim : ∀ {ι β γ} {I : Set ι} {B}
       -> (∀ {i} -> B i -> Set γ)
       -> (D : Desc I β)
       -> (∀ {j} -> Extend D B j -> B j)
       -> Set (β ⊔ γ)
  Elim {β = β} C (var i)   k = Lift {ℓ = β} (C (k lrefl))
  Elim         C (π q v D) k = Elimᵇ C D v k 
  Elim         C (D ⊛ E)   k with varView D
  ... | yes-var = ∀ {x} -> C x -> Elim C E (k ∘ _,_ x)
  ... | no-var  = ∀ {x} -> Hyp C D x -> Elim C E (k ∘ _,_ x)

  Elimᵇ : ∀ {α ι β γ δ q q′} {I : Set ι} {B}
        -> (∀ {i} -> B i -> Set γ)
        -> (D : Binder α β δ q′ I)
        -> Visibility
        -> (∀ {j} -> Extendᵇ D q B j -> B j)
        -> Set (β ⊔ γ)
  Elimᵇ {γ = γ} {q = q} C (coerce (A , D)) v k =
    Coerce′ (cong (γ ⊔_) q) $ Pi v A λ x -> Elim C (D x) (k ∘ coerce′ q ∘ _,_ x)

module _ {ι β γ} {I : Set ι} {D₀ : Data I β} (C : ∀ {j} -> μ D₀ j -> Set γ) where
  K : Data I β -> Set (ι ⊔ β)
  K D = ∀ {j} -> Node D₀ D j -> μ D₀ j

  Elims : (D : Data I β) -> K D -> Set (β ⊔ γ)
  Elims = AllAny (λ j -> proj₂ >>> λ D -> Extend D (μ D₀) j) (Elim C ∘ proj₂)

  module _ (hs : Elims D₀ node) where
    {-# TERMINATING #-}
    mutual
      elimHyp : (D : Desc I β) -> (d : ⟦ D ⟧ (μ D₀)) -> Hyp C D d
      elimHyp (var i)    d      = lift (elim d)
      elimHyp (π q v D)  f      = elimHypᵇ D f
      elimHyp (D ⊛ E)   (x , y) = elimHyp D x , elimHyp E y

      elimHypᵇ : ∀ {α δ q q′ v} -> (D : Binder α β δ q′ I) -> (f : ⟦ D ⟧ᵇ q v (μ D₀)) -> Hypᵇ C D f
      elimHypᵇ {q = q} {v = v} (coerce (A , D)) f =
        coerce′ (cong (_⊔_ γ) q) (lam v λ x -> elimHyp (D x) (app v (uncoerce′ q f) x))

      elimExtend : ∀ {j}
                 -> (D : Desc I β) {k : ∀ {j} -> Extend D (μ D₀) j -> μ D₀ j}
                 -> Elim C D k
                 -> (e : Extend D (μ D₀) j)
                 -> C (k e)
      elimExtend (var i)   z  lrefl  = lower z
      elimExtend (π q v D) h  p      = elimExtendᵇ D h p 
      elimExtend (D ⊛ E)   h (d , e) with varView D
      ... | yes-var = elimExtend E (h (elim d))  e
      ... | no-var  = elimExtend E (h (elimHyp D d)) e

      elimExtendᵇ : ∀ {α δ q q′ v j}
                  -> (D : Binder α β δ q′ I) {k : ∀ {j} -> Extendᵇ D q (μ D₀) j -> μ D₀ j}
                  -> Elimᵇ C D v k
                  -> (p : Extendᵇ D q (μ D₀) j)
                  -> C (k p)
      elimExtendᵇ {q = q} {v = v} (coerce (A , D)) h p with p | inspectUncoerce′ q p
      ... | _ | (x , e) , refl = elimExtend (D x) (app v (uncoerce′ (cong (γ ⊔_) q) h) x) e

      elimAny : ∀ {j} (D : Data I β) {k : K D} -> Elims D k -> (a : Node D₀ D j) -> C (k a)
      elimAny  []           tt       ()
      elimAny (C ∷ [])      h        e       = elimExtend (proj₂ C) h e
      elimAny (C ∷ C′ ∷ D) (h , hs) (inj₁ e) = elimExtend (proj₂ C) h e
      elimAny (C ∷ C′ ∷ D) (h , hs) (inj₂ a) = elimAny (C′ ∷ D) hs a

      elim : ∀ {j} -> (d : μ D₀ j) -> C d
      elim (node e) = elimAny D₀ hs e
