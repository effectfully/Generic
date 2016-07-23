-- Under reconstruction.

module Generic.Function.Lookup where

open import Generic.Core

data SumView {ι β} {I : Set ι} : ∀ {s} -> Desc I β s -> Set where
  yes-sum : ∀ {s t} -> (D : Desc I β s) -> (E : Desc I β t) -> SumView (D ⊕ E)
  no-sum  : ∀ {s} {D : Desc I β s} -> SumView D

sumView : ∀ {ι β s} {I : Set ι} -> (D : Desc I β s) -> SumView D
sumView (D ⊕ E) = yes-sum D E
sumView  D      = no-sum

data To {ι β} {I : Set ι} {B j}
        : ∀ {α s} -> Set α -> (D : Desc I β s) -> Extend D B j -> Set β where
  hereπ  : ∀ {α s b} {{q : α ⊔ β ≡ β}} {P p}
         -> To (unproj₁ P) (π {α = α} {s} b P) p
  here⊛  : ∀ {s} {D E : Desc I β s} {x} {e : Extend E B j}
         -> To (⟦ D ⟧ B) (D ⊛ E) (x , e)
  thereπ : ∀ {α s b} {A : Set α} {{q : α ⊔ β ≡ β}} {P p}
         -> let x , e = uncoerce′ {{q}} p in
              To A (unproj₂ P x) e -> To A (π {α = α} {s} b P) p
  there⊛ : ∀ {α s} {A : Set α} {D E : Desc I β s} {x} {e : Extend E B j}
         -> To A E e -> To A (D ⊛ E) (x , e)

Here : ∀ {ι α β} {I : Set ι} {B s j} -> Set α -> (D : Desc I β s) -> Extend D B j -> Set β
Here A D₀ e₀ with sumView D₀ | e₀
... | yes-sum D E | inj₁ e = Here A D e
... | yes-sum D E | inj₂ e = Here A E e
... | no-sum      | _      = To A D₀ e₀

Rec : ∀ {ι β s} {I : Set ι} {B}
    -> (∀ {i} -> B i -> Set β) -> (D : Desc I β s) -> ⟦ D ⟧ B -> Set β
Rec C (var i)        x      = C x
Rec C (π {{q}} b P)  f      = Coerce′ q (∃ λ x -> Rec C (unproj₂ P x) (apply b (uncoerce′ f) x))
Rec C (D ⊕ E)        s      = [ Rec C D , Rec C E ] s
Rec C (D ⊛ E)       (x , y) = Rec C D x ⊎ Rec C E y

There : ∀ {ι β s} {I : Set ι} {B : I -> Set β} {j}
      -> (∀ {i} -> B i -> Set β) -> (D : Desc I β s) -> Extend D B j -> Set β
There C (var i)  e      = ⊥
There C (π b P)  p      = split′ p (There C ∘ unproj₂ P)
There C (D ⊕ E)  s      = [ There C D , There C E ] s
There C (D ⊛ E) (x , e) = Rec C D x ⊎ There C E e

data PathTo {ι α β s} {I : Set ι} {D : Desc I β s} {j} (A : Set α) : μ D j -> Set β where
  phere  : ∀ {e} -> Here   A         D e -> PathTo A (node e)
  pthere : ∀ {e} -> There (PathTo A) D e -> PathTo A (node e)

glookupTo : ∀ {ι α β s} {A : Set α} {I : Set ι} {D : Desc I β s} {B j} {e : Extend D B j}
          -> To A D e -> A
glookupTo (hereπ {p = p}) = unproj₁′ p
glookupTo (here⊛ {x = x}) = x
glookupTo (thereπ t)      = glookupTo t
glookupTo (there⊛ t)      = glookupTo t

glookupHere : ∀ {ι α β s} {A : Set α} {I : Set ι} {B j}
            -> (D : Desc I β s) {e : Extend D B j} -> Here A D e -> A
glookupHere D₀ {e₀} h with sumView D₀ | e₀
... | yes-sum D E | inj₁ e = glookupHere D h
... | yes-sum D E | inj₂ e = glookupHere E h
... | no-sum      | _      = glookupTo h

module _ {ι α β s₀} {I : Set ι} {A : Set α} {D₀ : Desc I β s₀} where
  infixl 8 _!_

  {-# TERMINATING #-}
  mutual
    glookupRec : ∀ {s} -> (D : Desc I β s) {d : ⟦ D ⟧ (μ D₀)} -> Rec (PathTo A) D d -> A
    glookupRec (var i)           p       = glookup p
    glookupRec (π b P)           p       = let x , r = uncoerce′ p in glookupRec (unproj₂ P x) r
    glookupRec (D ⊕ E) {inj₁ _}  r       = glookupRec D r
    glookupRec (D ⊕ E) {inj₂ _}  r       = glookupRec E r
    glookupRec (D ⊛ E)          (inj₁ r) = glookupRec D r
    glookupRec (D ⊛ E)          (inj₂ r) = glookupRec E r

    glookupThere : ∀ {s j}
                 -> (D : Desc I β s) {e : Extend D (μ D₀) j} -> There (PathTo A) D e -> A
    glookupThere (var i)           ()
    glookupThere (π b P)           t       = glookupThere (unproj₂ P _) t
    glookupThere (D ⊕ E) {inj₁ e}  t       = glookupThere D t
    glookupThere (D ⊕ E) {inj₂ e}  t       = glookupThere E t
    glookupThere (D ⊛ E)          (inj₁ r) = glookupRec D r
    glookupThere (D ⊛ E)          (inj₂ t) = glookupThere E t

    glookup : ∀ {j} {d : μ D₀ j} -> PathTo A d -> A
    glookup (phere  h) = glookupHere  D₀ h
    glookup (pthere p) = glookupThere D₀ p

  _!_ : ∀ {j} -> (d : μ D₀ j) -> PathTo A d -> A
  d ! p = glookup p
