module Shape (A : Set) where
  open import Data.Nat
  open import Data.Vec hiding (split)
  open import Function
  open import Relation.Binary.PropositionalEquality

  import Splits
  open Splits A

  open import Evenness
  open import Logarithm

  shape : {n : ℕ} {xs : Vec A n} (sx : Split xs) → LogTree
  shape (single x) = single
  shape (branch-e pl il l r) = double   even (shape l) (shape r)
  shape (branch-u pl il l r) = double uneven (shape l) (shape r)

  depth : {n : ℕ} {xs : Vec A n} (sx : Split xs) → ℕ
  depth = ldepth ∘ shape

  module ShapeLemmas where
    private
      shape-comm : ∀ {n y} x {xs : Vec A n} (sx : Split (y ∷ xs)) → shape (insert x sx) ≡ inc (shape sx)
      shape-comm x (single y) = refl
      shape-comm x (branch-e pl il l r) rewrite shape-comm x r = refl
      shape-comm x (branch-u pl il l r) rewrite shape-comm x l = refl

      shape-split : ∀ {n} (x : A) (xs : Vec A n) → shape (split x xs) ≡ logtree n
      shape-split x [] = refl
      shape-split x (y ∷ xs) rewrite sym (shape-split y xs) = shape-comm x (split y xs)

      shape-size-ee : ∀ {pl il l r pl' il' l' r'}

      shape-uniq : {n : ℕ} {xs ys : Vec A n} (sx : Split xs) (sy : Split ys) → shape sx ≡ shape sy
      shape-uniq (single x) (single y) = refl
      shape-uniq (branch-e pl il l r) (branch-e pl' il' l' r')
        = cong₂ (double even) {!!} {!!}
      shape-uniq (branch-e pl il l r) (branch-u pl' il' l' r') = {!!}
      shape-uniq (branch-u pl il l r) (branch-e pl' il' l' r') = {!!}
      shape-uniq (branch-u pl il l r) (branch-u pl' il' l' r') = {!!}

    depth-lemma : {n : ℕ} {x : A} {xs : Vec A n} (sx : Split (x ∷ xs)) → depth sx ≡ ⌊log₂-suc n ⌋
    depth-lemma {n} {x} {xs} sx rewrite shape-uniq sx (split x xs) = cong ldepth (shape-split x xs)

  open ShapeLemmas
