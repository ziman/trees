module Splits (A : Set) where

open import Data.Nat
open import Data.Vec hiding (split)
open import Relation.Binary.PropositionalEquality

open import Evenness

data Plus : ℕ → ℕ → ℕ → Set where
  +-base : ∀ {n} → Plus 0 n n
  +-step : ∀ {m n o} → Plus m n o → Plus (suc m) n (suc o)

module PlusProperties where  
  private
    -- note: not really necessary, just for illustration
    +-property : ∀ {p q} → Plus p q (p + q)
    +-property {zero } = +-base
    +-property {suc n} = +-step +-property

  +-suc : ∀ {p q r} → Plus p q r → Plus (suc p) (suc q) (suc (suc r))
  +-suc  +-base     = +-step +-base
  +-suc (+-step pl) = +-step (+-suc pl)
  
  +-unstepr : ∀ {p q r} → Plus p (suc q) (suc r) → Plus p q r
  +-unstepr +-base = +-base
  +-unstepr {r = suc r} (+-step pl) = +-step (+-unstepr pl)
  +-unstepr {r = zero } (+-step ())

  half-lemma : ∀ {n nn} → Plus n n nn → n ≡ ⌊ nn /2⌋
  half-lemma +-base     = refl
  half-lemma {suc n} {suc zero} (+-step ())
  half-lemma {suc n} {suc (suc nn)} (+-step pl) = cong suc (half-lemma (+-unstepr pl))

  half-eq : ∀ {n n' nn} → Plus n n nn → Plus n' n' nn → n ≡ n'
  half-eq pl pl' rewrite half-lemma pl | half-lemma pl' = refl

data Interleave : Evenness → {m n o : ℕ}
    → Vec A m → Vec A n → Vec A o
    → Set
  where
    base : Interleave even [] [] []

    step-e : ∀ {n nn x y} {xs ys : Vec A n} {zs : Vec A nn}
      → Plus n n nn
      → Interleave uneven {    n} {suc n}      xs  (y ∷ ys) (    y ∷ zs)
      → Interleave even   {suc n} {suc n} (x ∷ xs) (y ∷ ys) (x ∷ y ∷ zs)

    step-u : ∀ {n nn y} {xs ys : Vec A n} {zs : Vec A nn}
      → Plus n n nn
      → Interleave even   {n} {    n} xs      ys       zs
      → Interleave uneven {n} {suc n} xs (y ∷ ys) (y ∷ zs)

data Split : {n : ℕ} → Vec A n → Set where
    single : ∀ x → Split (x ∷ [])

    branch-e : ∀ {n nn x y} {xs ys : Vec A n} {zs : Vec A nn}
      → Plus n n nn
      → Interleave even (x ∷ xs) (y ∷ ys) (x ∷ y ∷ zs)
      → Split (x ∷ xs)
      → Split (y ∷ ys)
      → Split (x ∷ y ∷ zs)

    branch-u : ∀ {n nn x y y'} {xs ys : Vec A n} {zs : Vec A nn}
      → Plus n n nn
      → Interleave uneven (x ∷ xs) (y ∷ y' ∷ ys) (y ∷ x ∷ y' ∷ zs)
      → Split (x ∷ xs)
      → Split (y ∷ y' ∷ ys)
      → Split (y ∷ x ∷ y' ∷ zs)

open PlusProperties

insert : {n : ℕ} → {xs : Vec A n} → (z : A) → Split xs → Split (z ∷ xs)
insert z (single x) = branch-e +-base (step-e +-base (step-u +-base base)) (single z) (single x)
insert z (branch-e pl il l r) = branch-u        pl  (step-u (+-suc pl) il)           l  (insert z r)
insert z (branch-u pl il l r) = branch-e (+-suc pl) (step-e (+-suc pl) il) (insert z l)           r

split : {n : ℕ} → (x : A) → (xs : Vec A n) → Split (x ∷ xs)
split x []       = single x
split x (y ∷ ys) = insert x (split y ys)
