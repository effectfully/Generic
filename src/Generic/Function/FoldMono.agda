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
  Hyp C (π i q D) = Hypᵇ i C D q
  Hyp C (D ⊛ E)   = Hyp C D × Hyp C E

  Hypᵇ : ∀ {α ι β γ q} {I : Set ι} i
       -> (I -> Set β) -> Binder α β γ i q I -> α ≤ℓ β -> Set β
  Hypᵇ i C (coerce (A , D)) q = Coerce′ q $ Pi i A λ x -> Hyp C (D x)

mutual
  Fold : ∀ {ι β} {I : Set ι} -> (I -> Set β) -> (D : Desc I β) -> Set β
  Fold C (var i)   = C i
  Fold C (π i q D) = Foldᵇ i C D q 
  Fold C (D ⊛ E)   = Hyp C D -> Fold C E

  Foldᵇ : ∀ {α ι β γ q} {I : Set ι} i
        -> (I -> Set β) -> Binder α β γ i q I -> α ≤ℓ β -> Set β
  Foldᵇ i C (coerce (A , D)) q = Coerce′ q $ Pi i A λ x -> Fold C (D x)

module _ {ι β} {I : Set ι} {D₀ : Data (Desc I β)} (C : I -> Set β) where
  module _ (hs : All (Fold C) (consTypes D₀)) where
    {-# TERMINATING #-}
    mutual
      foldHyp : (D : Desc I β) -> ⟦ D ⟧ (μ D₀) -> Hyp C D
      foldHyp (var i)    d      = foldMono d
      foldHyp (π i q D)  f      = foldHypᵇ i D f
      foldHyp (D ⊛ E)   (x , y) = foldHyp D x , foldHyp E y

      foldHypᵇ : ∀ {α γ q q′} i
               -> (D : Binder α β γ i q′ I) -> ⟦ i / D ⟧ᵇ q (μ D₀) -> Hypᵇ i C D q
      foldHypᵇ {q = q} i (coerce (A , D)) f =
        coerce′ q $ lamPi i λ x -> foldHyp (D x) (appPi i (uncoerce′ q f) x)

      foldExtend : ∀ {j} -> (D : Desc I β) -> Fold C D -> Extend D (μ D₀) j -> C j
      foldExtend (var i)   z  lrefl  = z
      foldExtend (π i q D) h  p      = foldExtendᵇ i D h p 
      foldExtend (D ⊛ E)   h (d , e) = foldExtend E (h (foldHyp D d)) e

      foldExtendᵇ : ∀ {α γ q q′ j} i
                  -> (D : Binder α β γ i q′ I) -> Foldᵇ i C D q -> Extendᵇ i D q (μ D₀) j -> C j
      foldExtendᵇ {q = q} i (coerce (A , D)) h p with p | inspectUncoerce′ q p
      ... | _ | (x , e) , refl = foldExtend (D x) (appPi i (uncoerce′ q h) x) e

      foldAny : ∀ {j} (Ds : List (Desc I β)) d a b ns
              -> All (Fold C) Ds -> Node D₀ (packData d a b Ds ns) j -> C j
      foldAny  []          d a b  tt       tt       ()
      foldAny (D ∷ [])     d a b (_ , ns) (h , tt)  e       = foldExtend D h e
      foldAny (D ∷ E ∷ Ds) d a b (_ , ns) (h , hs) (inj₁ e) = foldExtend D h e
      foldAny (D ∷ E ∷ Ds) d a b (_ , ns) (h , hs) (inj₂ r) = foldAny (E ∷ Ds) d a b ns hs r

      foldMono : ∀ {j} -> μ D₀ j -> C j
      foldMono (node e) = foldAny (consTypes D₀)
                                  (dataName  D₀)
                                  (parsTele  D₀)
                                  (indsTele  D₀)
                                  (consNames D₀)
                                   hs
                                   e

  curryFoldMono : ∀ {j} -> μ D₀ j -> CurryAll (Fold C) (consTypes D₀) (C j)
  curryFoldMono d = curryAll λ hs -> foldMono hs d
