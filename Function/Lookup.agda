module Generic.Function.Lookup where

open import Generic.Core

infixl 8 _!_

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

Rec : ∀ {ι β s} {I : Set ι} {B}
    -> (∀ {i} -> B i -> Set β) -> (D : Desc I β s) -> ⟦ D ⟧ B -> Set β
Rec C (var i)        x      = C x
Rec C (π {{q}} b P)  f      = Coerce′ q (∃ λ x -> Rec C (unproj₂ P x) (apply b (uncoerce′ f) x))
Rec C (D ⊛ E)       (x , y) = Rec C D x ⊎ Rec C E y

There : ∀ {ι β s} {I : Set ι} {B : I -> Set β} {j}
      -> (∀ {i} -> B i -> Set β) -> (D : Desc I β s) -> Extend D B j -> Set β
There C (var i)  e      = ⊥
There C (π b P)  p      = split′ p (There C ∘ unproj₂ P)
There C (D ⊛ E) (x , e) = Rec C D x ⊎ There C E e

-- God bless forcing.
data PathTo {ι β} {I : Set ι} {Ds : Data I β} {j}
            : ∀ {α} -> Set α -> μ Ds j -> Set β where
  phere  : ∀ {a α} {A : Set α}
         -> To A (findEl Ds a) (find Ds a) -> PathTo A (node a)
  pthere : ∀ {a α} {A : Set α}
         -> There (PathTo A) (findEl Ds a) (find Ds a) -> PathTo A (node a)

glookupTo : ∀ {ι α β s} {A : Set α} {I : Set ι} {D : Desc I β s} {B j} {e : Extend D B j}
          -> To A D e -> A
glookupTo (hereπ {p = p}) = unproj₁′ p
glookupTo (here⊛ {x = x}) = x
glookupTo (thereπ t)      = glookupTo t
glookupTo (there⊛ t)      = glookupTo t

{-# TERMINATING #-}
mutual
  glookupRec : ∀ {ι α β s} {A : Set α} {I : Set ι} {Ds}
             -> (D : Desc I β s) {d : ⟦ D ⟧ (μ Ds)} -> Rec (PathTo A) D d -> A
  glookupRec (var i)  p       = glookup p
  glookupRec (π b P)  p       = let x , r = uncoerce′ p in glookupRec (unproj₂ P x) r
  glookupRec (D ⊛ E) (inj₁ r) = glookupRec D r
  glookupRec (D ⊛ E) (inj₂ r) = glookupRec E r

  glookupThere : ∀ {ι α β s} {A : Set α} {I : Set ι} {Ds j}
               -> (D : Desc I β s) -> (e : Extend D (μ Ds) j) -> There (PathTo A) D e -> A
  glookupThere (var i)  q       ()
  glookupThere (π b P)  p       t       = let x , e = uncoerce′ p in glookupThere (unproj₂ P x) e t
  glookupThere (D ⊛ E) (d , e) (inj₁ r) = glookupRec D r
  glookupThere (D ⊛ E) (d , e) (inj₂ t) = glookupThere E e t

  glookup : ∀ {ι α β} {A : Set α} {I : Set ι} {Ds : Data I β} {j} {d : μ Ds j}
          -> PathTo A d -> A
  glookup           (phere  t)     = glookupTo t
  glookup {Ds = Ds} (pthere {a} p) = glookupThere (findEl Ds a) (find Ds a) p

_!_ : ∀ {ι α β} {A : Set α} {I : Set ι} {Ds : Data I β} {j}
    -> (d : μ Ds j) -> PathTo A d -> A
d ! p = glookup p
