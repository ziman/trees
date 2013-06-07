module Exp (A : Set) where
  open import Data.Nat
  open import Data.Vec hiding (split)
  open import Data.Maybe
  open import Relation.Binary.PropositionalEquality

  open import Logarithm
  open import Shape A
  open import Splits A

  -- Complete binary tree of depth n
  data ExpTree : ℕ → Set where
    single : A → ExpTree zero
    branch : ∀ {n} → (l r : ExpTree n) → ExpTree (suc n)

  exp'? : {n : ℕ} {x : A} {xs : Vec A n} (sx : Split (x ∷ xs)) → Maybe (ExpTree (depth sx))
  exp'? (single x) = just (single x)
  exp'? (branch-u pl il l r) = nothing
  exp'? (branch-e pl il l r) with exp'? l | exp'? r
  ... | nothing | nothing = nothing
  ... | just el | nothing = nothing
  ... | nothing | just er = nothing
  exp'? (branch-e pl il l r) | just el | just er
    rewrite depth-lemma l | depth-lemma r
    = just (branch el er)

  exp? : {n : ℕ} {x : A} {xs : Vec A n} (sx : Split (x ∷ xs)) → Maybe (ExpTree ⌊log₂-suc n ⌋)
  exp? sx with exp'? sx
  ... | nothing = nothing
  ... | just e  = just (subst ExpTree (depth-lemma sx) e)

  mkTree : {n : ℕ} (xs : Vec A (suc n)) → Maybe (ExpTree ⌊log₂-suc n ⌋)
  mkTree (x ∷ xs) = exp? (split x xs)
