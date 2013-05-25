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

module Logarithm where

  data LogTree : ℕ → Set where
    single : LogTree (suc zero)
    double : ∀ {x y z}
      → LogTree (suc x)
      → LogTree (suc y)
      → LogTree (suc (suc z))

  rdepth : ∀ {n} → LogTree n → ℕ
  rdepth single = 0
  rdepth (double l r) = suc (rdepth r)
  
  ldepth : ∀ {n} → LogTree n → ℕ
  ldepth single = 0
  ldepth (double l r) = suc (ldepth l)

  inc : ∀ {n} → LogTree n → LogTree (suc n)
  inc single = double single single
  inc (double lx ly) = double (inc ly) lx

  logtree : (n : ℕ) → LogTree (suc n)
  logtree  zero   = single
  logtree (suc n) = inc (logtree n)

  ⌊log₂_⌋ : (n : ℕ) → n ≢ 0 → ℕ
  ⌊log₂ zero  ⌋ 0≢0 = ⊥-elim (0≢0 refl)
  ⌊log₂ suc n ⌋ n≢0 = rdepth (logtree n)

  ⌈log₂_⌉ : (n : ℕ) → n ≢ 0 → ℕ
  ⌈log₂ zero  ⌉ 0≢0 = ⊥-elim (0≢0 refl)
  ⌈log₂ suc n ⌉ n≢0 = ldepth (logtree n)

module VecSplit (A : Set) where

  open import Data.Vec

  data Evenness : Set where
    even uneven : Evenness

  other : Evenness → Evenness
  other   even = uneven
  other uneven =   even

  data Plus : ℕ → ℕ → ℕ → Set where
    +-base : ∀ {n} → Plus 0 n n
    +-step : ∀ {m n o} → Plus m n o → Plus (suc m) n (suc o)

  +-suc : ∀ {p q r} → Plus p q r → Plus (suc p) (suc q) (suc (suc r))
  +-suc  +-base     = +-step +-base
  +-suc (+-step pl) = +-step (+-suc pl)

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
