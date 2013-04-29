module trees where

open import Function
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.List
open import Data.Product
open import Data.Maybe
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PEq

module TreeSplit {A : Set} where

  data Evenness : Set where
    even uneven : Evenness

  other : Evenness → Evenness
  other   even = uneven
  other uneven =   even

  data Interleave : Evenness → List A → List A → List A → Set where
    base : Interleave even [] [] []
    step : ∀ {x xs ys zs e} → Interleave (other e) xs ys zs → Interleave e (x ∷ ys) xs (x ∷ zs)

  data Split : ℕ → List A → Set where
    empty : Split zero []
    single : ∀ x → Split zero (x ∷ []) 
    branch : ∀ x y {xs ys zs n} e
      → Interleave e (x ∷ xs) (y ∷ ys) (x ∷ y ∷ zs)
      → Split n (x ∷ xs)
      → Split n (y ∷ ys)
      → Split (suc n) (x ∷ y ∷ zs)

  insert : ∀ {xs} → (x : A) → Split xs → Split (x ∷ xs)
  insert z empty = single z
  insert z (single x) = branch z x even (step (step base)) (single z) (single x)
  insert z (branch x y even il sx sy) = 
    branch z x uneven (step il) (insert z sy) sx
  insert z (branch x y uneven il sx sy) = 
    branch z x   even (step il) (insert z sy) sx

{-
  split : (xs : List A) → Split xs
  split []       = empty
  split (x ∷ zs) = insert x (split zs)

  depth : {xs : List A} → Split xs → ℕ
  depth empty = 0
  depth (single x) = 0
  depth (branch _ _ _ _ sx _) = suc (depth sx)

  data Exp : ℕ → List A → Set where
    single : ∀ x → Exp zero (x ∷ [])
    branch : ∀ xs ys {zs n}
      → Interleave even xs ys zs
      → Exp n xs
      → Exp n ys
      → Exp (suc n) zs

  exp-nonempty : ∀ {n} → ¬(Exp n [])
  exp-nonempty (branch [] [] base ex ey) = exp-nonempty ex

  depth-lemma : ∀ xs ys {zs}
    → Interleave even xs ys zs
    → (sx : Split xs)
    → (sy : Split ys)
    → depth sx ≡ depth sy
  depth-lemma [] [] base empty empty = refl
  depth-lemma (.x ∷ []) (.y ∷ []) (step (step il)) (single x) (single y) = refl
  depth-lemma (.x ∷ []) (.y ∷ .y' ∷ ys) (step (step ())) (single x) (branch y y' e il sx sy)
  depth-lemma (.x ∷ .x' ∷ xs) (.y ∷ []) (step (step (step ()))) (branch x x' e il sx sy) (single y)
  depth-lemma (.x ∷ .x' ∷ xs) (.y ∷ .y' ∷ ys)
    (step (step (step (step il))))
    (branch x x' e₁ il₁ sx₁ sy₁)
    (branch y y' e₂ il₂ sx₂ sy₂)
    = cong suc {!!}

  exp'? : {xs : List A} → (sx : Split xs) → Maybe (Exp (depth sx) xs)
  exp'? empty = nothing
  exp'? (single x) = just (single x)
  exp'? (branch x y uneven il sx sy) = nothing
  exp'? (branch x y {xs} {ys} even il sx sy) with exp'? sx | exp'? sy
  ... | just esx | just esy = just (branch (x ∷ xs) (y ∷ ys) il esx {!!})
  ... | just _  | nothing = nothing
  ... | nothing | just _  = nothing
  ... | nothing | nothing = nothing

  exp? : (xs : List A) → Maybe (Exp (depth (split xs)) xs)
  exp? xs = exp'? (split xs)

  data Tree : ℕ → Set where
    single : A → Tree zero
    branch : ∀ {n} → (l r : Tree n) → Tree (suc n)

  mkTree : ∀ {n} → (xs : List A) → Exp n xs → Tree n
  mkTree xs e = {!!}
-}



