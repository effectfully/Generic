module Generic.Data.List where

open import Generic.Core

infixr 5 _∷ₗ_ _∷ₗ′_

List : ∀ {α} -> Set α -> Set α
List A = μ′
       $ pos
       ⊕ (A ⇒ pos ⊛ pos)

pattern []ₗ       = #₀ lrefl
pattern _∷ₗ_ x xs = !#₁ (x , xs , lrefl)

_∷ₗ′_ : ∀ {α} {A : Set α} -> A -> List A -> List A
_∷ₗ′_ = _∷ₗ_

elimList : ∀ {α π} {A : Set α}
         -> (P : List A -> Set π)
         -> (∀ {xs} x -> P xs -> P (x ∷ₗ xs))
         -> P []ₗ
         -> ∀ xs
         -> P xs
elimList P f z  []ₗ      = z
elimList P f z (x ∷ₗ xs) = f x (elimList P f z xs)



-- The entire content of `Data.List.Base` (modulo imports and the constructors were renamed):

open import Generic.Data.Maybe

infixr 5 _++_

[_] : ∀ {a} {A : Set a} → A → List A
[ x ] = x ∷ₗ []ₗ

_++_ : ∀ {a} {A : Set a} → List A → List A → List A
[]ₗ       ++ ys = ys
(x ∷ₗ xs) ++ ys = x ∷ₗ (xs ++ ys)

-- Snoc.

infixl 5 _∷ₗʳ_

_∷ₗʳ_ : ∀ {a} {A : Set a} → List A → A → List A
xs ∷ₗʳ x = xs ++ [ x ]

null : ∀ {a} {A : Set a} → List A → Bool
null []ₗ       = true
null (x ∷ₗ xs) = false

-- * List transformations

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
map f []ₗ       = []ₗ
map f (x ∷ₗ xs) = f x ∷ₗ map f xs

replicate : ∀ {a} {A : Set a} → (n : ℕ) → A → List A
replicate zero    x = []ₗ
replicate (suc n) x = x ∷ₗ replicate n x

zipWith : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
          → (A → B → C) → List A → List B → List C
zipWith f (x ∷ₗ xs) (y ∷ₗ ys) = f x y ∷ₗ zipWith f xs ys
zipWith f _        _        = []ₗ

zip : ∀ {a b} {A : Set a} {B : Set b} → List A → List B → List (A × B)
zip = zipWith (_,_)

intersperse : ∀ {a} {A : Set a} → A → List A → List A
intersperse x []ₗ           = []ₗ
intersperse x (y ∷ₗ []ₗ)     = [ y ]
intersperse x (y ∷ₗ z ∷ₗ zs) = y ∷ₗ x ∷ₗ intersperse x (z ∷ₗ zs)

-- * Reducing lists (folds)

foldr : ∀ {a b} {A : Set a} {B : Set b} → (A → B → B) → B → List A → B
foldr c n []ₗ       = n
foldr c n (x ∷ₗ xs) = c x (foldr c n xs)

foldl : ∀ {a b} {A : Set a} {B : Set b} → (A → B → A) → A → List B → A
foldl c n []ₗ       = n
foldl c n (x ∷ₗ xs) = foldl c (c n x) xs

-- ** Special folds

concat : ∀ {a} {A : Set a} → List (List A) → List A
concat = foldr _++_ []ₗ

concatMap : ∀ {a b} {A : Set a} {B : Set b} →
            (A → List B) → List A → List B
concatMap f = concat ∘ map f

and : List Bool → Bool
and = foldr _∧_ true

or : List Bool → Bool
or = foldr _∨_ false

any : ∀ {a} {A : Set a} → (A → Bool) → List A → Bool
any p = or ∘ map p

all : ∀ {a} {A : Set a} → (A → Bool) → List A → Bool
all p = and ∘ map p

sum : List ℕ → ℕ
sum = foldr _+_ 0

product : List ℕ → ℕ
product = foldr _*_ 1

length : ∀ {a} {A : Set a} → List A → ℕ
length = foldr (λ _ → suc) 0

import Data.List.Base

reverse : ∀ {a} {A : Set a} → List A → List A
reverse = foldl (λ rev x → x ∷ₗ′ rev) []ₗ

-- * Building lists

-- ** Scans

scanr : ∀ {a b} {A : Set a} {B : Set b} →
        (A → B → B) → B → List A → List B
scanr f e []ₗ       = e ∷ₗ []ₗ
scanr f e (x ∷ₗ xs) with scanr f e xs
... | []ₗ     = []ₗ                -- dead branch
... | y ∷ₗ ys = f x y ∷ₗ y ∷ₗ ys

scanl : ∀ {a b} {A : Set a} {B : Set b} →
        (A → B → A) → A → List B → List A
scanl f e []ₗ       = e ∷ₗ []ₗ
scanl f e (x ∷ₗ xs) = e ∷ₗ scanl f (f e x) xs

-- ** Unfolding

-- Unfold. Uses a measure (a natural number) to ensure termination.

unfold : ∀ {a b} {A : Set a} (B : ℕ → Set b)
         (f : ∀ {n} → B (suc n) → Maybe (A × B n)) →
         ∀ {n} → B n → List A
unfold B f {n = zero}  s = []ₗ
unfold B f {n = suc n} s with f s
... | nothing       = []ₗ
... | just (x , s') = x ∷ₗ unfold B f s'

-- downFrom 3 = 2 ∷ₗ 1 ∷ₗ 0 ∷ₗ []ₗ.

downFrom : ℕ → List ℕ
downFrom n = unfold Singleton f (wrap n)
  where
  data Singleton : ℕ → Set where
    wrap : (n : ℕ) → Singleton n

  f : ∀ {n} → Singleton (suc n) → Maybe (ℕ × Singleton n)
  f {n} (wrap .(suc n)) = just (n , wrap n)

-- ** Conversions

fromMaybe : ∀ {a} {A : Set a} → Maybe A → List A
fromMaybe (just x) = [ x ]
fromMaybe nothing  = []ₗ

-- * Sublists

-- ** Extracting sublists

take : ∀ {a} {A : Set a} → ℕ → List A → List A
take zero    xs       = []ₗ
take (suc n) []ₗ       = []ₗ
take (suc n) (x ∷ₗ xs) = x ∷ₗ take n xs

drop : ∀ {a} {A : Set a} → ℕ → List A → List A
drop zero    xs       = xs
drop (suc n) []ₗ       = []ₗ
drop (suc n) (x ∷ₗ xs) = drop n xs

splitAt : ∀ {a} {A : Set a} → ℕ → List A → (List A × List A)
splitAt zero    xs       = ([]ₗ , xs)
splitAt (suc n) []ₗ       = ([]ₗ , []ₗ)
splitAt (suc n) (x ∷ₗ xs) with splitAt n xs
... | (ys , zs) = (x ∷ₗ ys , zs)

takeWhile : ∀ {a} {A : Set a} → (A → Bool) → List A → List A
takeWhile p []ₗ       = []ₗ
takeWhile p (x ∷ₗ xs) with p x
... | true  = x ∷ₗ takeWhile p xs
... | false = []ₗ

dropWhile : ∀ {a} {A : Set a} → (A → Bool) → List A → List A
dropWhile p []ₗ       = []ₗ
dropWhile p (x ∷ₗ xs) with p x
... | true  = dropWhile p xs
... | false = x ∷ₗ xs

span : ∀ {a} {A : Set a} → (A → Bool) → List A → (List A × List A)
span p []ₗ       = ([]ₗ , []ₗ)
span p (x ∷ₗ xs) with p x
... | true  = pmap (_∷ₗ′_ x) id (span p xs)
... | false = ([]ₗ , x ∷ₗ xs)

break : ∀ {a} {A : Set a} → (A → Bool) → List A → (List A × List A)
break p = span (not ∘ p)

inits : ∀ {a} {A : Set a} → List A → List (List A)
inits []ₗ       = []ₗ ∷ₗ []ₗ
inits (x ∷ₗ xs) = []ₗ ∷ₗ map (_∷ₗ′_ x) (inits xs)

tails : ∀ {a} {A : Set a} → List A → List (List A)
tails []ₗ       = []ₗ ∷ₗ []ₗ
tails (x ∷ₗ xs) = (x ∷ₗ xs) ∷ₗ tails xs

infixl 5 _∷ₗʳ'_

data InitLast {a} {A : Set a} : List A → Set a where
  []ₗʳ   : InitLast []ₗ
  _∷ₗʳ'_ : (xs : List A) (x : A) → InitLast (xs ∷ₗʳ x)

initLast : ∀ {a} {A : Set a} (xs : List A) → InitLast xs
initLast []ₗ               = []ₗʳ
initLast (x ∷ₗ xs)         with initLast xs
initLast (x ∷ₗ .[]ₗ)        | []ₗʳ      = []ₗ ∷ₗʳ' x
initLast (x ∷ₗ .(ys ∷ₗʳ y)) | ys ∷ₗʳ' y = (x ∷ₗ ys) ∷ₗʳ' y

-- * Searching lists

-- ** Searching with a predicate

-- A generalised variant of filter.

gfilter : ∀ {a b} {A : Set a} {B : Set b} →
          (A → Maybe B) → List A → List B
gfilter p []ₗ       = []ₗ
gfilter p (x ∷ₗ xs) with p x
... | just y  = y ∷ₗ gfilter p xs
... | nothing =     gfilter p xs

filter : ∀ {a} {A : Set a} → (A → Bool) → List A → List A
filter p = gfilter (λ x → if p x then just′ x else nothing)

partition : ∀ {a} {A : Set a} → (A → Bool) → List A → (List A × List A)
partition p []ₗ       = ([]ₗ , []ₗ)
partition p (x ∷ₗ xs) with p x | partition p xs
... | true  | (ys , zs) = (x ∷ₗ ys , zs)
... | false | (ys , zs) = (ys , x ∷ₗ zs)
