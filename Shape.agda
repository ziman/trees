module Shape (A : Set) where
  open import Data.Empty
  open import Data.Nat
  open import Data.Vec hiding (split)
  open import Function
  open import Relation.Nullary
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

  module Balance where
    private
      balance : {n : ℕ} {xs : Vec A n} (sx : Split xs) → Evenness
      balance (single x) = uneven
      balance (branch-e pl il l r) = even
      balance (branch-u pl il l r) = uneven
  
      evenness : ℕ → Evenness
      evenness  zero         = even
      evenness (suc  zero  ) = uneven
      evenness (suc (suc n)) = evenness n
  
      other²=id : ∀ {e} → other (other e) ≡ e
      other²=id {  even} = refl
      other²=id {uneven} = refl
  
      infixl 5 _⊕_
      _⊕_ : Evenness → Evenness → Evenness
      even   ⊕ even   = even
      even   ⊕ uneven = uneven
      uneven ⊕ even   = uneven
      uneven ⊕ uneven = even
  
      even-id-l : ∀ {e} → even ⊕ e ≡ e
      even-id-l {even} = refl
      even-id-l {uneven} = refl
    
      comm-suc-other : ∀ n → evenness (suc n) ≡ other (evenness n)
      comm-suc-other zero = refl
      comm-suc-other (suc n) rewrite comm-suc-other n = sym other²=id
  
      comm-⊕-other-l : ∀ m n → other m ⊕ n ≡ other (m ⊕ n)
      comm-⊕-other-l even even = refl
      comm-⊕-other-l even uneven = refl
      comm-⊕-other-l uneven even = refl
      comm-⊕-other-l uneven uneven = refl
  
      plus-⊕ : ∀ {m} {n} {o} → Plus m n o → evenness m ⊕ evenness n ≡ evenness o
      plus-⊕ +-base = even-id-l
      plus-⊕ {suc m} {n} {suc o} (+-step pl) = begin
        evenness (suc m) ⊕ evenness n
          ≡⟨ cong (λ x → x ⊕ evenness n) (comm-suc-other m)⟩
        other (evenness m) ⊕ evenness n
          ≡⟨ comm-⊕-other-l (evenness m) (evenness n) ⟩
        other (evenness m ⊕ evenness n)
          ≡⟨ cong other (plus-⊕ pl) ⟩
        other (evenness o)
          ≡⟨ sym (comm-suc-other o) ⟩
        evenness (suc o)
          ∎
        where
          open ≡-Reasoning

      ev-double : ∀ e → e ⊕ e ≡ even
      ev-double even = refl
      ev-double uneven = refl
  
      plus-even : ∀ {n nn} → Plus n n nn → evenness nn ≡ even
      plus-even {n} {nn} pl = begin
        evenness nn
          ≡⟨ sym (plus-⊕ pl) ⟩
        evenness n ⊕ evenness n
          ≡⟨ ev-double (evenness n) ⟩
        even
          ∎
        where
          open ≡-Reasoning

    ev-thm : {n : ℕ} {xs : Vec A n} (sx : Split xs) → balance sx ≡ evenness n
    ev-thm (single x) = refl
    ev-thm (branch-e pl il l r) = sym (plus-even pl)
    ev-thm (branch-u {n} {nn} pl il l r) rewrite comm-suc-other nn = cong other (sym (plus-even pl))

  open Balance

  module ShapeLemmas where
    private
      shape-comm : ∀ {n y} x {xs : Vec A n} (sx : Split (y ∷ xs)) → shape (insert x sx) ≡ inc (shape sx)
      shape-comm x (single y) = refl
      shape-comm x (branch-e pl il l r) rewrite shape-comm x r = refl
      shape-comm x (branch-u pl il l r) rewrite shape-comm x l = refl

      shape-split : ∀ {n} (x : A) (xs : Vec A n) → shape (split x xs) ≡ logtree n
      shape-split x [] = refl
      shape-split x (y ∷ xs) rewrite sym (shape-split y xs) = shape-comm x (split y xs)

      even-distinct : ¬ (even ≡ uneven)
      even-distinct ()

      shape-uniq : {n : ℕ} {xs ys : Vec A n} (sx : Split xs) (sy : Split ys) → shape sx ≡ shape sy

      shape-uniq (single x) (single y) = refl

      shape-uniq (branch-e pl il l r) (branch-e pl' il' l' r')
        rewrite half-eq pl pl'
        = cong₂ (double even) (shape-uniq l l') (shape-uniq r r')

      shape-uniq (branch-u pl il l r) (branch-u pl' il' l' r')
        rewrite half-eq pl pl'
        = cong₂ (double uneven) (shape-uniq l l') (shape-uniq r r')

      shape-uniq (branch-e pl il l r) (branch-u pl' il' l' r')
        = ⊥-elim (even-distinct (trans (ev-thm (branch-e pl il l r)) (sym (ev-thm (branch-u pl' il' l' r')))))

      shape-uniq (branch-u pl il l r) (branch-e pl' il' l' r')
        = ⊥-elim (even-distinct (trans (ev-thm (branch-e pl' il' l' r')) (sym (ev-thm (branch-u pl il l r)))))

    depth-lemma : {n : ℕ} {x : A} {xs : Vec A n} (sx : Split (x ∷ xs)) → depth sx ≡ ⌊log₂-suc n ⌋
    depth-lemma {n} {x} {xs} sx rewrite shape-uniq sx (split x xs) = cong ldepth (shape-split x xs)

  open ShapeLemmas public
