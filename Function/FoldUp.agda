module Generic.Function.FoldUp where

open import Generic.Core

CurryAll : ∀ {α β} {A : Set α} -> (A -> Set β) -> List A -> Set β -> Set β
CurryAll B  []      C = C
CurryAll B (x ∷ xs) C = B x -> CurryAll B xs C

curryAll : ∀ {α β} {A : Set α} {B : A -> Set β} {C}
         -> ∀ xs -> (All B xs -> C) -> CurryAll B xs C
curryAll  []      g = g tt
curryAll (x ∷ xs) g = curryAll xs ∘ curry g

mutual
  Hyp : ∀ {ι β} {I : Set ι} γ -> (I -> Set (β ⊔ γ)) -> (D : Desc I β) -> Set (β ⊔ γ)
  Hyp γ C (var i)   = C i
  Hyp γ C (π q v D) = Hypᵇ γ C D q v
  Hyp γ C (D ⊛ E)   = Hyp γ C D × Hyp γ C E

  Hypᵇ : ∀ {α ι β δ q} {I : Set ι} γ
       -> (I -> Set (β ⊔ γ)) -> Binder α β δ q I -> α ≤ℓ β -> Visibility -> Set (β ⊔ γ)
  Hypᵇ γ C (coerce (A , D)) q v = Coerce′ (cong (γ ⊔_) q) $ Pi v A λ x -> Hyp γ C (D x)

mutual
  Fold : ∀ {ι β} {I : Set ι} γ
       -> (I -> Set (β ⊔ γ)) -> (D : Desc I β) -> Set (β ⊔ γ)
  Fold γ C (var i)   = C i
  Fold γ C (π q v D) = Foldᵇ γ C D q v 
  Fold γ C (D ⊛ E)   = Hyp γ C D -> Fold γ C E

  Foldᵇ : ∀ {α ι β δ q} {I : Set ι} γ
        -> (I -> Set (β ⊔ γ)) -> Binder α β δ q I -> α ≤ℓ β -> Visibility -> Set (β ⊔ γ)
  Foldᵇ γ C (coerce (A , D)) q v = Coerce′ (cong (γ ⊔_) q) $ Pi v A λ x -> Fold γ C (D x)

module _ {ι β} {I : Set ι} {D₀ : Data I β} γ (C : I -> Set (β ⊔ γ)) where
  Folds : List (Desc I β) -> Set (β ⊔ γ)
  Folds = All (Fold γ C)

  module _ (hs : Folds (constructors D₀)) where
    {-# TERMINATING #-}
    mutual
      foldHyp : (D : Desc I β) -> ⟦ D ⟧ (μ D₀) -> Hyp γ C D
      foldHyp (var i)    d      = foldUp d
      foldHyp (π q v D)  f      = foldHypᵇ D f
      foldHyp (D ⊛ E)   (x , y) = foldHyp D x , foldHyp E y

      foldHypᵇ : ∀ {α δ q q′ v} -> (D : Binder α β δ q′ I) -> ⟦ D ⟧ᵇ q v (μ D₀) -> Hypᵇ γ C D q v
      foldHypᵇ {q = q} {v = v} (coerce (A , D)) f =
        coerce′ (cong (_⊔_ γ) q) (lam v λ x -> foldHyp (D x) (app v (uncoerce′ q f) x))

      foldExtend : ∀ {j} -> (D : Desc I β) -> Fold γ C D -> Extend D (μ D₀) j -> C j
      foldExtend (var i)   z  lrefl  = z
      foldExtend (π q v D) h  p      = foldExtendᵇ D h p 
      foldExtend (D ⊛ E)   h (d , e) = foldExtend E (h (foldHyp D d)) e

      foldExtendᵇ : ∀ {α δ q q′ v j}
                  -> (D : Binder α β δ q′ I) -> Foldᵇ γ C D q v -> Extendᵇ D q (μ D₀) j -> C j
      foldExtendᵇ {q = q} {v = v} (coerce (A , D)) h p with p | inspectUncoerce′ q p
      ... | _ | (x , e) , refl = foldExtend (D x) (app v (uncoerce′ (cong (γ ⊔_) q) h) x) e

      foldAny : ∀ {j} (Ds : List (Desc I β)) n a b ns
              -> Folds Ds -> Node D₀ (packData n a b Ds ns) j -> C j
      foldAny  []          n a b  tt       tt       ()
      foldAny (D ∷ [])     n a b  ns      (h , tt)  e       = foldExtend D h e
      foldAny (D ∷ E ∷ Ds) n a b  ns      (h , hs) (inj₁ e) = foldExtend D h e
      foldAny (D ∷ E ∷ Ds) n a b (_ , ns) (h , hs) (inj₂ r) = foldAny (E ∷ Ds) n a b ns hs r

      foldUp : ∀ {j} -> μ D₀ j -> C j
      foldUp (node e) =
        foldAny (constructors D₀) (dataName D₀) (paramsType D₀) (indicesType D₀)(consNames D₀) hs e

foldMono : ∀ {ι β} {I : Set ι} {D : Data I β} {j}
         -> (C : I -> Set β) -> μ D j -> CurryAll (Fold β C) (constructors D) (C j)
foldMono C d = curryAll _ λ hs -> foldUp _ C hs d
