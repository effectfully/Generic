{-# OPTIONS --type-in-type #-}

module Generic.Examples.Experiment where

open import Generic.Lib.Prelude

data Desc (I : Set) : Set₁ where
  ret : I -> Desc I
  π   : (A : Set) -> (A -> Desc I) -> Desc I
  _⊕_ : Desc I -> Desc I -> Desc I

data RecDesc (I : Set) : Set₁ where
  rec : ((I -> Set) -> Desc I) -> RecDesc I

⟦_⟧ : ∀ {I} -> Desc I -> (I -> Set) -> I -> Set
⟦ ret i ⟧ B j = i ≡ j
⟦ π A D ⟧ B j = ∃ λ x -> ⟦ D x ⟧ B j
⟦ D ⊕ E ⟧ B j = ⟦ D ⟧ B j ⊎ ⟦ E ⟧ B j

⟦_⟧ʳ : ∀ {I} -> RecDesc I -> (I -> Set) -> I -> Set
⟦ rec K ⟧ʳ B j = ⟦ K B ⟧ B j

{-# NO_POSITIVITY_CHECK #-}
data μ {I} (D : RecDesc I) j : Set where
  node : ⟦ D ⟧ʳ (μ D) j -> μ D j

DescEq : ∀ {I} -> Desc I -> Set
DescEq (ret i) = ⊤
DescEq (π A D) = Eq A × ∀ x -> DescEq (D x)
DescEq (D ⊕ E) = DescEq D × DescEq E

RecDescEq : ∀ {I} -> RecDesc I -> Set₁
RecDescEq (rec K) = ∀ {B} {{eqB : ∀ {i} -> Eq (B i)}} -> DescEq (K B)

instance
  {-# TERMINATING #-}
  DataEq : ∀ {I} {D : RecDesc I} {j} {{recDescEq : RecDescEq D}} -> Eq (μ D j)
  DataEq {D = D} {j} = record
    { _≟_ = eqMu
    } where
        node-inj : ∀ {I D j x y} -> node {I} {D} {j} x ≡ node y -> x ≡ y
        node-inj refl = refl

        eqSem : ∀ {j} D₀ D {{descEq : DescEq D}} -> IsSet (⟦ D ⟧ (μ D₀) j)
        eqSem D₀ (ret i)               refl refl = yes refl
        eqSem D₀ (π A D) {{eqA , eqD}} p₁   p₂   =
          decProd (_≟_ {{eqA}}) (eqSem D₀ (D _) {{eqD _}}) p₁ p₂
        eqSem D₀ (D ⊕ E) {{eqD , eqE}} s₁   s₂   =
          decSum (eqSem D₀ D {{eqD}}) (eqSem D₀ E {{eqE}}) s₁ s₂

        eqMu : ∀ {D} {{recDescEq : RecDescEq D}} -> IsSet (μ D j)
        eqMu {D@(rec K)} {{recDescEq}} (node d₁) (node d₂) =
          dcong node node-inj (eqSem D _ {{recDescEq {{DataEq {D = D}}}}} d₁ d₂)

module Example1 where
  open import Generic.Main using (deriveEqTo)

  instance
    ListEq : {A : Set} {{eqA : Eq A}} -> Eq (List A)
    unquoteDef ListEq = deriveEqTo ListEq (quote List)

  data Rose (A : Set) : Set where
    rose : A -> List (Rose A) -> Rose A

  Rose′ : Set -> Set
  Rose′ A = flip μ tt $ rec λ Rose′ -> π A λ _ -> π (List (Rose′ tt)) λ _ -> ret tt

  pattern rose′ x rs = node (x , rs , refl)

  {-# TERMINATING #-}
  Rose→Rose′ : ∀ {A} -> Rose A -> Rose′ A
  Rose→Rose′ (rose x rs) = rose′ x (map Rose→Rose′ rs)

  {-# TERMINATING #-}
  Rose′→Rose : ∀ {A} -> Rose′ A -> Rose A
  Rose′→Rose (rose′ x rs) = rose x (map Rose′→Rose rs)

  arose : Rose′ ℕ
  arose = rose′ 4 (rose′ 1 (rose′ 6 [] ∷ []) ∷ rose′ 2 [] ∷ [])

  find : {A : Set} {{x : A}} -> A
  find {{x}} = x

  -- -- Instance search cannot be used to find elements in an explicit function type
  -- test : _≟_ {{DataEq {{λ {_} -> find}}}} arose arose ≡ yes refl
  -- test = refl

module Example2 where
  -- If `A` is a parameter, then this definition would be strictly positive,
  -- but I intentionally made it an index, because we can't make `A` a parameter
  -- in the described version of `D`.
  {-# NO_POSITIVITY_CHECK #-}
  data D : Set -> Set where
    ret : ∀ {A} -> A -> D A
    rec : ∀ {A} -> D (D A) -> D A

  D′ : Set -> Set
  D′ = μ $ rec λ D′ -> (π Set λ A -> π A λ _ -> ret A)
                     ⊕ (π Set λ A -> π (D′ (D′ A)) λ _ -> ret A)

  pattern ret′ x = node (inj₁ (_ , x , refl))
  pattern rec′ r = node (inj₂ (_ , r , refl))

  Dⁿ : ℕ -> Set -> Set
  Dⁿ  0      A = A
  Dⁿ (suc n) A = D (Dⁿ n A)

  D′ⁿ : ℕ -> Set -> Set
  D′ⁿ  0      A = A
  D′ⁿ (suc n) A = D′ (D′ⁿ n A)

  ⟨D→D′⟩ⁿ : ∀ {A} n -> D (Dⁿ n A) -> D′ (D′ⁿ n A)
  ⟨D→D′⟩ⁿ  0      (ret x) = ret′ x
  ⟨D→D′⟩ⁿ (suc n) (ret r) = ret′ (⟨D→D′⟩ⁿ  n      r)
  ⟨D→D′⟩ⁿ  n      (rec r) = rec′ (⟨D→D′⟩ⁿ (suc n) r)

  ⟨D′→D⟩ⁿ : ∀ {A} n -> D′ (D′ⁿ n A) -> D (Dⁿ n A)
  ⟨D′→D⟩ⁿ  0      (ret′ x) = ret x
  ⟨D′→D⟩ⁿ (suc n) (ret′ r) = ret (⟨D′→D⟩ⁿ  n      r)
  ⟨D′→D⟩ⁿ  n      (rec′ r) = rec (⟨D′→D⟩ⁿ (suc n) r)

  D→D′ : ∀ {A} -> D A -> D′ A
  D→D′ = ⟨D→D′⟩ⁿ 0

  D′→D : ∀ {A} -> D′ A -> D A
  D′→D = ⟨D′→D⟩ⁿ 0
