# Generic

It's a library for doing generic programming in Agda. Descriptions are defined as follows:

```
mutual
  Binder : ∀ {ι} α β γ -> ι ⊔ lsuc (α ⊔ β) ≡ γ -> Set ι -> Set γ
  Binder α β γ q I = Coerce q (∃ λ (A : Set α) -> A -> Cons I β)

  data Cons {ι} (I : Set ι) β : Set (ι ⊔ lsuc β) where
    var : I -> Cons I β
    π   : ∀ {α}
        -> (q : α ≤ℓ β) -> Visibility -> Binder α β _ (cong (λ αβ -> ι ⊔ lsuc αβ) q) I -> Cons I β
    _⊛_ : Cons I β -> Cons I β -> Cons I β

Desc : ∀ {ι} -> Set ι -> ∀ β -> Set (ι ⊔ lsuc β)
Desc I β = List (Name × Cons I β)
```

I.e. a description is a list of named constructors, where `Name` comes from the `Reflection` module. That `Coerce` stuff is elaborated in [Emulating cumulativity in Agda](http://effectfully.blogspot.ru/2016/07/cumu.html). Constructors are interpreted in the way described in [Descriptions](http://effectfully.blogspot.ru/2016/04/descriptions.html) (in the `CompProp` module).

There is some reflection machinery that allows to parse actual Agda data types into their described counterparts. An example from the `/Generic/Examples/ReadData.agda` module:

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

Actual generic programming happens in the `/Generic/Property` subfolder. There is generic decidable equality defined over described data types. It can be used like this:

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

The `/Generic/Property/Reify.agda` module implements coercion from described data types to `Term`s (from the `Reflection` module). Since stored names of described constructors are taken from actual constructors, reified elements of described data types are actually quoted elements of actual data types and hence the former can be converted to the latter:

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

xs : Vec (Fin 4) 3
xs = fsuc (fsuc (fsuc fzero)) ∷ᵥ fzero ∷ᵥ fsuc fzero ∷ᵥ []ᵥ

test : reflect xs ≡ suc (suc (suc zero)) ∷ zero ∷ (Fin.Fin 4 ∋ suc zero) ∷ []
test = refl
```

There are also generic `elim` and `lookup`, but they are outdated and don't work currently.

The plan is to define decidable equality over actual data types using reflection and the current decidable equality over described data types. Ornaments may or may not appear later.