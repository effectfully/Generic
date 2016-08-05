module Generic.Lib.Data.Pow where

open import Generic.Lib.Intro
open import Generic.Lib.Data.Nat
-- open import Generic.Lib.Category

infixl 6 _^_

_^_ : ∀ {α} -> Set α -> ℕ -> Set α
A ^ 0     = ⊤
A ^ suc n = A × A ^ n

elimPow : ∀ {n α} {A : Set α} {b : ∀ {n} -> A ^ n -> Level}
        -> (B : ∀ {n} -> (xs : A ^ n) -> Set (b xs))
        -> (∀ {n} {xs : A ^ n} x -> B xs -> B (x , xs))
        -> B tt
        -> (xs : A ^ n)
        -> B xs
elimPow {0}     B f z  tt      = z
elimPow {suc n} B f z (x , xs) = f x (elimPow B f z xs)

foldPow : ∀ {n α β} {A : Set α}
        -> (B : ℕ -> Set β) -> (∀ {n} -> A -> B n -> B (suc n)) -> B 0 -> A ^ n -> B n
foldPow B f z xs = elimPow (λ {n} _ -> B n) (λ x y -> f x y) z xs

foldPow₁ : ∀ {n α} {A : Set α} -> (A -> A -> A) -> A ^ suc n -> A
foldPow₁ {0}     f (x , []) = x
foldPow₁ {suc n} f (x , xs) = f x (foldPow₁ f xs)

mapPow : ∀ {n α β} {A : Set α} {B : Set β} -> (A -> B) -> A ^ n -> B ^ n
mapPow f = foldPow (_ ^_) (_,_ ∘ f) tt

replicatePow : ∀ {α} {A : Set α} n -> A -> A ^ n
replicatePow  0      x = tt
replicatePow (suc n) x = x , replicatePow n x

-- instance
--   PowFunctor : ∀ {n α} -> RawFunctor {α} (_^ n)
--   PowFunctor = record
--     { _<$>_ = mapPow
--     }
