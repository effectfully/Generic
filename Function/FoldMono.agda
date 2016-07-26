module Generic.Function.FoldMono where

open import Generic.Core

CurryAll : ∀ {α β} {A : Set α} -> (A -> Set β) -> List A -> Set β -> Set β
CurryAll B  []      C = C
CurryAll B (x ∷ xs) C = B x -> CurryAll B xs C

curryAll : ∀ {α β} {A : Set α} {B : A -> Set β} {C xs}
         -> (All B xs -> C) -> CurryAll B xs C
curryAll {xs = []}     g = g tt
curryAll {xs = x ∷ xs} g = curryAll ∘ curry g

mutual
  Hyp : ∀ {ι β} {I : Set ι} -> (I -> Set β) -> (D : Desc I β) -> Set β
  Hyp C (var i)   = C i
  Hyp C (π q v D) = Hypᵇ C D q v
  Hyp C (D ⊛ E)   = Hyp C D × Hyp C E

  Hypᵇ : ∀ {α ι β γ q} {I : Set ι}
       -> (I -> Set β) -> Binder α β γ q I -> α ≤ℓ β -> Visibility -> Set β
  Hypᵇ C (coerce (A , D)) q v = Coerce′ q $ Pi v A λ x -> Hyp C (D x)

mutual
  Fold : ∀ {ι β} {I : Set ι} -> (I -> Set β) -> (D : Desc I β) -> Set β
  Fold C (var i)   = C i
  Fold C (π q v D) = Foldᵇ C D q v 
  Fold C (D ⊛ E)   = Hyp C D -> Fold C E

  Foldᵇ : ∀ {α ι β γ q} {I : Set ι}
        -> (I -> Set β) -> Binder α β γ q I -> α ≤ℓ β -> Visibility -> Set β
  Foldᵇ C (coerce (A , D)) q v = Coerce′ q $ Pi v A λ x -> Fold C (D x)

module _ {ι β} {I : Set ι} {D₀ : Data I β} (C : I -> Set β) where
  module _ (hs : All (Fold C) (constructors D₀)) where
    {-# TERMINATING #-}
    mutual
      foldHyp : (D : Desc I β) -> ⟦ D ⟧ (μ D₀) -> Hyp C D
      foldHyp (var i)    d      = foldMono d
      foldHyp (π q v D)  f      = foldHypᵇ D f
      foldHyp (D ⊛ E)   (x , y) = foldHyp D x , foldHyp E y

      foldHypᵇ : ∀ {α γ q q′ v} -> (D : Binder α β γ q′ I) -> ⟦ D ⟧ᵇ q v (μ D₀) -> Hypᵇ C D q v
      foldHypᵇ {q = q} {v = v} (coerce (A , D)) f =
        coerce′ q $ lam v λ x -> foldHyp (D x) (app v (uncoerce′ q f) x)

      foldExtend : ∀ {j} -> (D : Desc I β) -> Fold C D -> Extend D (μ D₀) j -> C j
      foldExtend (var i)   z  lrefl  = z
      foldExtend (π q v D) h  p      = foldExtendᵇ D h p 
      foldExtend (D ⊛ E)   h (d , e) = foldExtend E (h (foldHyp D d)) e

      foldExtendᵇ : ∀ {α γ q q′ v j}
                  -> (D : Binder α β γ q′ I) -> Foldᵇ C D q v -> Extendᵇ D q (μ D₀) j -> C j
      foldExtendᵇ {q = q} {v = v} (coerce (A , D)) h p with p | inspectUncoerce′ q p
      ... | _ | (x , e) , refl = foldExtend (D x) (app v (uncoerce′ q h) x) e

      foldAny : ∀ {j} (Ds : List (Desc I β)) d a b ns
              -> All (Fold C) Ds -> Node D₀ (packData d a b Ds ns) j -> C j
      foldAny  []          d a b  tt       tt       ()
      foldAny (D ∷ [])     d a b  ns      (h , tt)  e       = foldExtend D h e
      foldAny (D ∷ E ∷ Ds) d a b  ns      (h , hs) (inj₁ e) = foldExtend D h e
      foldAny (D ∷ E ∷ Ds) d a b (_ , ns) (h , hs) (inj₂ r) = foldAny (E ∷ Ds) d a b ns hs r

      foldMono : ∀ {j} -> μ D₀ j -> C j
      foldMono (node e) = foldAny (constructors D₀)
                                  (dataName     D₀)
                                  (paramsType   D₀)
                                  (indicesType  D₀)
                                  (consNames    D₀)
                                   hs
                                   e

  curryFoldMono : ∀ {j} -> μ D₀ j -> CurryAll (Fold C) (constructors D₀) (C j)
  curryFoldMono d = curryAll λ hs -> foldMono hs d
