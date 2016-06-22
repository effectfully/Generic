module Generic.Function.Elim where

open import Generic.Core

data VarView {ι β} {I : Set ι} : ∀ {s} -> Desc I β s -> Set where
  yes-var : ∀ {i} -> VarView (var i)
  no-var  : ∀ {s D} -> VarView {s = s} D

varView : ∀ {ι β s} {I : Set ι} -> (D : Desc I β s) -> VarView D
varView (var i) = yes-var
varView  D      = no-var

Hyp : ∀ {ι β γ s} {I : Set ι} {B}
    -> (∀ {i} -> B i -> Set γ) -> (D : Desc I β s) -> ⟦ D ⟧ B -> Set (β ⊔ γ)
Hyp {β = β} C (var i)        y      = Lift {ℓ = β} (C y)
Hyp {γ = γ} C (π {{q}} b P)  f      =
  Coerce′ (cong (γ ⊔_) q) (Pi b _ λ x -> Hyp C (unproj₂ P x) (apply b (uncoerce′ f) x))
Hyp         C (D ⊕ E)        s      = [ Hyp C D , Hyp C E ] s
Hyp         C (D ⊛ E)       (x , y) = Hyp C D x × Hyp C E y

Elim : ∀ {ι β γ s} {I : Set ι} {B}
     -> (∀ {i} -> B i -> Set γ)
     -> (D : Desc I β s)
     -> (∀ {j} -> Extend D B j -> B j)
     -> Set (β ⊔ γ)
Elim {β = β} C (var i)       k = Lift {ℓ = β} (C (k lrefl))
Elim {γ = γ} C (π {{q}} b P) k =
  Coerce′ (cong (γ ⊔_) q) (Pi b _ λ x -> Elim C (unproj₂ P x) (k ∘ coerce′ ∘ _,_ x))
Elim         C (D ⊕ E)       k = Elim C D (k ∘ inj₁) × Elim C E (k ∘ inj₂)
Elim         C (D ⊛ E)       k with varView D
... | yes-var = ∀ {x} -> C x -> Elim C E (k ∘ _,_ x)
... | no-var  = ∀ {x} -> Hyp C D x -> Elim C E (k ∘ _,_ x)

module _ {ι β γ s} {I : Set ι} {D₀ : Desc I β s}
         (C : ∀ {j} -> μ D₀ j -> Set γ) (h : Elim C D₀ node) where
   {-# TERMINATING #-}
   mutual
     elimExtend : ∀ {j s}
                -> (D : Desc I β s) {k : ∀ {j} -> Extend D (μ D₀) j -> μ D₀ j}
                -> Elim C D k
                -> (e : Extend D (μ D₀) j)
                -> C (k e)
     elimExtend (var i)        z       lrefl   = lower z
     elimExtend (π {{q}} b P)  f       p       with p | inspectUncoerce′ p
     ... | _ | (x , e) , refl =
       elimExtend (unproj₂ P x) (apply b (uncoerce′ {{cong (γ ⊔_) q}} f) x) e
     elimExtend (D ⊕ E)       (f , g) (inj₁ e) = elimExtend D f e
     elimExtend (D ⊕ E)       (f , g) (inj₂ e) = elimExtend E g e
     elimExtend (D ⊛ E)        f      (d , e)  with varView D
     ... | yes-var = elimExtend E (f (elim d))  e
     ... | no-var  = elimExtend E (f (hyp D d)) e

     hyp : ∀ {s} -> (D : Desc I β s) -> (d : ⟦ D ⟧ (μ D₀)) -> Hyp C D d
     hyp (var i)        d       = lift (elim d)
     hyp (π {{q}} b P)  f       =
       coerce′ {{cong (_⊔_ γ) q}} (lam b λ x -> hyp (unproj₂ P x) (apply b (uncoerce′ f) x))
     hyp (D ⊕ E)       (inj₁ x) = hyp D x
     hyp (D ⊕ E)       (inj₂ y) = hyp E y
     hyp (D ⊛ E)       (x , y)  = hyp D x , hyp E y

     elim : ∀ {j} -> (d : μ D₀ j) -> C d
     elim (node e) = elimExtend D₀ h e
