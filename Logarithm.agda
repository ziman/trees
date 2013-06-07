module Logarithm where
  open import Function
  open import Data.Nat
  open import Relation.Binary.PropositionalEquality

  open import Evenness

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

  ⌊log₂-suc_⌋ : ℕ → ℕ
  ⌊log₂-suc_⌋ = ldepth ∘ logtree

  ⌈log₂-suc_⌉ : ℕ → ℕ
  ⌈log₂-suc_⌉ = rdepth ∘ logtree

  data Complete : LogTree → Set where
    single : Complete single
    double : ∀ {l r} → Complete l → Complete r → Complete (double even l r)

  powerOfTwo : ℕ → Set
  powerOfTwo = Complete ∘ logtree

