module trees where

open import Function
open import Algebra.Structures
open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.List
open import Data.Product
open import Data.Maybe
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PEq

data Evenness : Set where
  even uneven : Evenness

other : Evenness → Evenness
other   even = uneven
other uneven =   even

module Logarithm where

  data LogTree : Set where
    single : LogTree
    double : Evenness → LogTree → LogTree → LogTree

  rdepth : LogTree → ℕ
  rdepth single = 0
  rdepth (double _ l r) = suc (rdepth r)
  
  ldepth : LogTree → ℕ
  ldepth single = 0
  ldepth (double _ l r) = suc (ldepth l)

  inc : LogTree → LogTree
  inc single = double even single single
  inc (double   even lx ly) = double uneven      lx  (inc ly)
  inc (double uneven lx ly) = double   even (inc lx)      ly

  logtree : ℕ → LogTree
  logtree  zero   = single
  logtree (suc n) = inc (logtree n)

  ⌊log₂-suc_⌋ : (n : ℕ) → ℕ
  ⌊log₂-suc n ⌋ = ldepth (logtree n)

  ⌈log₂-suc_⌉ : (n : ℕ) → ℕ
  ⌈log₂-suc n ⌉ = rdepth (logtree n)

module VecSplit (A : Set) where

  open import Data.Vec hiding (split)

  data Plus : ℕ → ℕ → ℕ → Set where
    +-base : ∀ {n} → Plus 0 n n
    +-step : ∀ {m n o} → Plus m n o → Plus (suc m) n (suc o)
  
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

  insert : {n : ℕ} → {xs : Vec A n} → (z : A) → Split xs → Split (z ∷ xs)
  insert z (single x) = branch-e +-base (step-e +-base (step-u +-base base)) (single z) (single x)
  insert z (branch-e pl il l r) = branch-u        pl  (step-u (+-suc pl) il)           l  (insert z r)
  insert z (branch-u pl il l r) = branch-e (+-suc pl) (step-e (+-suc pl) il) (insert z l)           r

  split : {n : ℕ} → (x : A) → (xs : Vec A n) → Split (x ∷ xs)
  split x []       = single x
  split x (y ∷ ys) = insert x (split y ys)

  module Uniqueness where

    private
      foo : ℕ
      foo = 0

    split-irr : {n : ℕ} {xs : Vec A n} (sx sx' : Split xs) → sx ≡ sx'
    split-irr (single x) (single .x) = refl
    split-irr (branch-e pl il l r) (branch-e pl' il' l' r') = {!!}
    split-irr (branch-u pl il l r) (branch-u pl' il' l' r') = {!!}
    split-irr (branch-e pl il l r) (branch-u pl' il' l' r') = {!!}
    split-irr (branch-u pl il l r) (branch-e pl' il' l' r') = {!!}
  
  open Logarithm
  open Uniqueness

  shape : {n : ℕ} {xs : Vec A n} (sx : Split xs) → LogTree
  shape (single x) = single
  shape (branch-e pl il l r) = double   even (shape l) (shape r)
  shape (branch-u pl il l r) = double uneven (shape l) (shape r)

  shape-comm : ∀ {n y} x {xs : Vec A n} (sx : Split (y ∷ xs)) → shape (insert x sx) ≡ inc (shape sx)
  shape-comm x (single y) = refl
  shape-comm x (branch-e pl il l r) rewrite shape-comm x r = refl
  shape-comm x (branch-u pl il l r) rewrite shape-comm x l = refl

  shape-lemma : ∀ {n} (x : A) (xs : Vec A n) → shape (split x xs) ≡ logtree n
  shape-lemma x [] = refl
  shape-lemma x (y ∷ xs) rewrite sym (shape-lemma y xs) = shape-comm x (split y xs)

  depth : {n : ℕ} {xs : Vec A n} (sx : Split xs) → ℕ
  depth = ldepth ∘ shape

  shape-uniq : {n : ℕ} {xs : Vec A n} (sx sx' : Split xs) → shape sx ≡ shape sx'
  shape-uniq sx sx' = cong shape (split-irr sx sx')

  shape-canon : {n : ℕ} {x : A} {xs : Vec A n} (sx : Split (x ∷ xs)) → depth sx ≡ ⌊log₂-suc n ⌋
  shape-canon {n} {x} {xs} sx rewrite shape-uniq sx (split x xs) = cong ldepth (shape-lemma x xs)

  data Exp : ℕ → Set where
    single : A → Exp zero
    branch : ∀ {n} → (l r : Exp n) → Exp (suc n)

  exp? : {n : ℕ} {x : A} {xs : Vec A n} (sx : Split (x ∷ xs)) → Maybe (Exp (depth sx))
  exp? (single x) = just (single x)
  exp? (branch-u pl il l r) = nothing
  exp? (branch-e pl il l r) with exp? l | exp? r
  ... | nothing | nothing = nothing
  ... | just el | nothing = nothing
  ... | nothing | just er = nothing
  exp? (branch-e {n} {nn} {._} {y} {xs} {ys} {zs} pl (step-e {.n} {.nn} {x} pf (step-u pf' il)) l r) | just el | just er
    rewrite shape-canon l | shape-canon r = just (branch el er)
{-
    = subst (Maybe ∘ Exp ∘ ldepth ∘ inc) (shape-lemma y zs)
        (subst (Maybe ∘ Exp ∘ ldepth) (shape-comm x (split y zs)) {!!})
-}
