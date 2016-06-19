module Generic.Function.Elim where

open import Generic.Core

Hyp : ∀ {ι β γ s} {I : Set ι} {B}
    -> (∀ {i} -> B i -> Set γ) -> (D : Desc I β s) -> ⟦ D ⟧ B -> Set (β ⊔ γ)
Hyp {β = β} C (var i)        y      = Lift {ℓ = β} (C y)
Hyp {γ = γ} C (π {{q}} b P)  f      =
  Coerce′ (cong (γ ⊔_) q) (Pi b _ λ x -> Hyp C (unproj₂ P x) (apply b (uncoerce′ f) x))
Hyp         C (D ⊛ E)       (x , y) = Hyp C D x × Hyp C E y

Elim : ∀ {ι β γ s} {I : Set ι} {B}
     -> (∀ {i} -> B i -> Set γ)
     -> (D : Desc I β s)
     -> (∀ {j} -> Extend D B j -> B j)
     -> Set (β ⊔ γ)
Elim {β = β} C (var i)       k = Lift {ℓ = β} (C (k lrefl))
Elim {γ = γ} C (π {{q}} b P) k =
  Coerce′ (cong (γ ⊔_) q) (Pi b _ λ x -> Elim C (unproj₂ P x) (k ∘ coerce′ ∘ _,_ x))
Elim         C (var i ⊛ E)   k = ∀ {x} -> C x -> Elim C E (k ∘ _,_ x)
Elim         C (D     ⊛ E)   k = ∀ {x} -> Hyp C D x -> Elim C E (k ∘ _,_ x)

-- Dang.
IAllAny : ∀ {ι κ α β γ δ} {I : Set ι} {J : Set κ} {A : I -> Set α} {C : J -> Set γ}
        -> (B : ∀ {i} -> J -> A i -> Set β)
        -> (∀ {i} -> (x : A i) -> (∀ {j} -> B j x -> C j) -> Set δ)
        -> (xs : IList A)
        -> (∀ {j} -> Any (B j) xs -> C j)
        -> Set δ
IAllAny B D  []          k = ⊤
IAllAny B D (x ∷ [])     k = D x k
IAllAny B D (x ∷ y ∷ xs) k = D x (k ∘ inj₁) × IAllAny B D (y ∷ xs) (k ∘ inj₂)

module _ {ι β γ} {I : Set ι} {Ds₀ : Data I β} (C : ∀ {j} -> μ Ds₀ j -> Set γ) where
  KA : Data I β -> Set _
  KA Ds = ∀ {j} -> Any (λ D -> Extend D (μ Ds₀) j) Ds -> μ Ds₀ j

  ElimFuns : (Ds : Data I β) -> KA Ds -> Set _
  ElimFuns = IAllAny (λ j D -> Extend D (μ Ds₀) j) (Elim C)

  module _ (hs : ElimFuns Ds₀ node) where
    {-# TERMINATING #-}
    mutual
      elimExtend : ∀ {j s}
                 -> (D : Desc I β s) {k : ∀ {j} -> Extend D (μ Ds₀) j -> μ Ds₀ j}
                 -> Elim C D k
                 -> (e : Extend D (μ Ds₀) j)
                 -> C (k e)
      elimExtend (var i)       z  lrefl  = lower z
      elimExtend (π {{q}} b P) h  p      with p | inspectUncoerce′ p
      ... | _ | (x , e) , refl =
        elimExtend (unproj₂ P x) (apply b (uncoerce′ {{cong (γ ⊔_) q}} h) x) e
      elimExtend (var i     ⊛ E)       h (d , e) = elimExtend E (h (elim d))  e
      elimExtend (D@(π _ _) ⊛ E)       h (d , e) = elimExtend E (h (hyp D d)) e 
      elimExtend (D@(_ ⊛ _) ⊛ E)       h (d , e) = elimExtend E (h (hyp D d)) e

      elimAny : ∀ {j}
              -> (Ds : Data I β) {k : KA Ds}
              -> ElimFuns Ds k
              -> (a : Any (λ D -> Extend D (μ Ds₀) j) Ds)
              -> C (k a)
      elimAny  []           tt       ()
      elimAny (D ∷ [])      h        e       = elimExtend D h e
      elimAny (D ∷ E ∷ Ds) (h , hs) (inj₁ e) = elimExtend D h e
      elimAny (D ∷ E ∷ Ds) (h , hs) (inj₂ a) = elimAny (E ∷ Ds) hs a

      hyp : ∀ {s} -> (D : Desc I β s) -> (d : ⟦ D ⟧ (μ Ds₀)) -> Hyp C D d
      hyp (var i)        d      = lift (elim d)
      hyp (π {{q}} b P)  f      =
        coerce′ {{cong (_⊔_ γ) q}} (lam b λ x -> hyp (unproj₂ P x) (apply b (uncoerce′ f) x))
      hyp (D ⊛ E)       (x , y) = hyp D x , hyp E y

      elim : ∀ {j} -> (d : μ Ds₀ j) -> C d
      elim (node a) = elimAny Ds₀ hs a
