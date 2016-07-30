# Generic

It's a library for doing generic programming in Agda. Descriptions are defined as follows:

```
mutual
  Binder : ∀ {ι} α β γ -> ι ⊔ lsuc (α ⊔ β) ≡ γ -> Set ι -> Set γ
  Binder α β γ q I = Coerce q (∃ λ (A : Set α) -> A -> Desc I β)

  data Desc {ι} (I : Set ι) β : Set (ι ⊔ lsuc β) where
    var : I -> Desc I β
    π   : ∀ {α}
        -> (q : α ≤ℓ β) -> Visibility -> Binder α β _ (cong (λ αβ -> ι ⊔ lsuc αβ) q) I -> Desc I β
    _⊛_ : Desc I β -> Desc I β -> Desc I β

record Data {ι} (I : Set ι) β : Set (ι ⊔ lsuc β) where
  no-eta-equality
  constructor packData
  field
    dataName     : Name
    paramsType   : Type
    indicesType  : Type
    constructors : List (Desc I β)
    consNames    : All (λ _ -> Name) constructors
open Data public
```

I.e. an encoded data typed is a list of named constructors. It also has a name and is packaged with telescopes of types of parameters and indices. `Name` and `Type` come from the `Reflection` module. That `Coerce` stuff is elaborated in [Emulating cumulativity in Agda](http://effectfully.blogspot.ru/2016/07/cumu.html). Constructors are interpreted in the way described in [Descriptions](http://effectfully.blogspot.ru/2016/04/descriptions.html) (in the `CompProp` module).

There is some reflection machinery that allows to parse regular Agda data types into their described counterparts. An example from the [`Examples/ReadData.agda`](Examples/ReadData.agda) module:

```
data D {α β} (A : Set α) (B : ℕ -> Set β) : ∀ {n} -> B n -> List ℕ -> Set (α ⊔ β) where
  c₁ : ∀ {n} (y : B n) xs -> A -> D A B y xs
  c₂ : ∀ {y : B 0} -> (∀ {n} (y : B n) {{xs}} -> D A B y xs) -> List A -> D A B y []

D′ : ∀ {α β} (A : Set α) (B : ℕ -> Set β) {n} -> B n -> List ℕ -> Set (α ⊔ β)
D′ = readData D

pattern c₁′ {n} y xs x = #₀  (n , y , xs , x , lrefl)
pattern c₂′ {y} r ys   = !#₁ (y , r , ys , lrefl)

inj : ∀ {α β} {A : Set α} {B : ℕ -> Set β} {n xs} {y : B n} -> D A B y xs -> D′ A B y xs
inj (c₁ y xs x) = c₁′ y xs x
inj (c₂ r ys)   = c₂′ (λ y -> inj (r y)) ys

outj : ∀ {α β} {A : Set α} {B : ℕ -> Set β} {n xs} {y : B n} -> D′ A B y xs -> D A B y xs
outj (c₁′ y xs x) = c₁ y xs x
outj (c₂′ r ys)   = c₂ (λ y -> outj (r y)) ys
```

So universe polymorphism is fully supported, as well as implicit and instance arguments, multiple (including single or none) parameters and indices, higher-order inductive occurrences and you can define functions over described data types just like over the actual ones (though, [pattern synonyms are not equal in power to proper constructors](https://github.com/agda/agda/issues/2069)).

There is a generic procedure that allows to coerce elements of described data type to elements of the corresponding regular data types, e.g. `outj` can be defined as

```
outj : ∀ {α β} {A : Set α} {B : ℕ -> Set β} {n xs} {y : B n} -> D′ A B y xs -> D A B y xs
outj d = uncoerce d
```

Internally it's a bit of reflection sugar on top of a generic fold defined on described data types (the [`Function/FoldMono.agda`](Function/FoldMono.agda) module).

`D′` computes to the following term:

```
λ {α} {β} A B {n} z z₁ →
  μ
  ((quote c₁ ,
    ipi ℕ
    (λ n₁ →
       pi (B n₁)
       (λ y → pi (List ℕ) (λ xs → pi A (λ z₂ → var (n₁ , y , xs))))))
   ∷
   (quote c₂ ,
    ipi (B 0)
    (λ y →
       ipi ℕ
       (λ n₁ →
          pi (B n₁) (λ y₁ → iipi (List ℕ) (λ xs → var (n₁ , y₁ , xs))))
       ⊛ pi (List A) (λ z₂ → var (0 , y , []))))
   ∷ [])
  (n , z , z₁)
```

Actual generic programming happens in the [`Property`](Property) subfolder. There is generic decidable equality defined over described data types. It can be used like this:

```
xs : Vec (List (Fin 4)) 3
xs = (fsuc fzero ∷ fzero ∷ [])
   ∷ᵥ (fsuc (fsuc fzero) ∷ [])
   ∷ᵥ (fzero ∷ fsuc (fsuc (fsuc fzero)) ∷ [])
   ∷ᵥ []ᵥ

test : xs ≟ xs ≡ yes refl
test = refl
```

Equality for `Vec`s, `List`s and `Fin`s is derived automatically.

The [`Property/Reify.agda`](Property/Reify.agda) module implements coercion from described data types to `Term`s. Since stored names of described constructors are taken from actual constructors, reified elements of described data types are actually quoted elements of regular data types and hence the former can be converted to the latter (like with `uncoerce`, but deeply and accepts only normal forms):

```
record Reify {α} (A : Set α) : Set α where
  field reify : A -> Term

  macro
    reflect : A -> Term -> TC _
    reflect = unify ∘ reify
open Reify {{...}} public

instance
  DescReify : ∀ {i β} {I : Set i} {D : Desc I β} {j}
                {{reD : All (ExtendReify ∘ proj₂) D}} -> Reify (μ D j)
  DescReify = ...

open import Generic.Data.Fin
open import Generic.Data.Vec

open import Data.Fin renaming (Fin to StdFin)
open import Data.Vec renaming (Vec to StdVec)

xs : Vec (Fin 4) 3
xs = fsuc (fsuc (fsuc fzero)) ∷ᵥ fzero ∷ᵥ fsuc fzero ∷ᵥ []ᵥ

xs′ : StdVec (StdFin 4) 3
xs′ = suc (suc (suc zero)) ∷ zero ∷ (suc zero) ∷ []

test : reflect xs ≡ xs′
test = refl
```

There are also generic `elim` in [`Function/Elim.agda`](Function/Elim.agda) (the idea is described in [Deriving eliminators of described data types](http://effectfully.blogspot.ru/2016/06/deriving-eliminators-of-described-data.html) and `lookup` in [`Function/Lookup.agda`](Function/Lookup.agda) (broken currently).

The plan is to define decidable equality over regular data types using reflection and the current decidable equality over described data types. There is a problem however: it's hard to derive eliminators for regular data types (I can't handle implicits properly, see e.g. [this](https://github.com/agda/agda/issues/2118) issue). Currently, a data type and its constructors can be read automatically as well as coercion from a described data type to its regular counterpart, but automatic coercion in the other direction is missing, because of the mentioned issue with implicits (which also doesn't allow to derive data types via `unquoteDecl`). And we also need a proof that the latter coercion is an injection to get decidable equality. So deriving equality is quite verbose now, see the [`Examples/DeriveEq.agda`](Examples/DeriveEq.agda) module for two examples.

Ornaments may or may not appear later (a model can be found [here](https://github.com/effectfully/random-stuff/blob/master/Desc/ParamOrn.agda)).