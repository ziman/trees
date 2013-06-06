module Exp (A : Set) where
  open import Data.Nat
  open import Data.Vec hiding (split)
  open import Data.Maybe

  open import Shape A

  data Exp : ℕ → Set where
    single : A → Exp zero
    branch : ∀ {n} → (l r : Exp n) → Exp (suc n)

  exp'? : {n : ℕ} {x : A} {xs : Vec A n} (sx : Split (x ∷ xs)) → Maybe (Exp (depth sx))
  exp'? (single x) = just (single x)
  exp'? (branch-u pl il l r) = nothing
  exp'? (branch-e pl il l r) with exp'? l | exp'? r
  ... | nothing | nothing = nothing
  ... | just el | nothing = nothing
  ... | nothing | just er = nothing
  exp'? (branch-e {n} {nn} {._} {y} {xs} {ys} {zs} pl (step-e {.n} {.nn} {x} pf (step-u pf' il)) l r) | just el | just er
    rewrite depth-lemma l | depth-lemma r = just (branch el er)

  exp? : {n : ℕ} {x : A} {xs : Vec A n} (sx : Split (x ∷ xs)) → Maybe (Exp ⌊log₂-suc n ⌋)
  exp? sx with exp'? sx
  ... | nothing = nothing
  ... | just e  = just (subst Exp (depth-lemma sx) e)
