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

  +-comm : ∀ p q → p + q ≡ q + p
  +-comm = comm
    where
      open IsCommutativeSemiring isCommutativeSemiring
      open IsCommutativeMonoid +-isCommutativeMonoid

  +-suc : ∀ p q → suc (suc (p + q)) ≡ suc p + suc q
  +-suc zero q = refl
  +-suc (suc p) q = cong suc (+-suc p q)

  +-suc' : ∀ p q → p + suc q ≡ suc (p + q)
  +-suc' zero q = refl
  +-suc' (suc p) q = cong suc (+-suc' p q)

  data Plus : ℕ → ℕ → ℕ → Set where
    +-base : ∀ {n} → Plus 0 n n
    +-step : ∀ {m n o} → Plus m n o → Plus (suc m) n (suc o)

  +-rsuc : ∀ {m n o} → Plus m (suc n) o → Plus (suc m) n o
  +-rsuc +-base = +-step +-base
  +-rsuc (+-step pl) = +-step (+-rsuc pl)

  +-rev : ∀ {m n o} → Plus m (suc n) (suc o) → Plus m n o
  +-rev +-base = +-base
  +-rev (+-step pl) = +-rsuc pl 

  data Interleave : Evenness → {m n o : ℕ}
    → Plus m n o
    → Vec A m → Vec A n → Vec A o
    → Set
   where
    base : Interleave even +-base [] [] []
    step-e : ∀ {n x y pl} {xs ys : Vec A n} {zs : Vec A (n + n)}
      → Interleave uneven {suc n} {n} (+-rev pl) (y ∷ ys) xs (y ∷ zs)
      → Interleave even {suc n} {suc n} pl (x ∷ xs) (y ∷ ys) (x ∷ y ∷ zs)
    step-u : ∀ {n x pl} {xs ys : Vec A n} {zs : Vec A (n + n)}
      → Interleave even {n} {n} pl ys xs zs
      → Interleave uneven {suc n} {n} (+-step pl) (x ∷ xs) ys (x ∷ zs)

{-
  data Split : {n : ℕ} → Vec A n → Set where
    single : ∀ x → Split (x ∷ [])
    branch-e : ∀ {n x y} {xs : Vec A n} {ys : Vec A n} {zs : Vec A (n + n)}
      → Interleave even (x ∷ xs) (y ∷ ys) (subst (Vec A) (+-suc n n) (x ∷ y ∷ zs))
      → Split (x ∷ xs)
      → Split (y ∷ ys)
      → Split (x ∷ y ∷ zs)
    branch-u : ∀ {n x y} {xs : Vec A (suc n)} {ys : Vec A n} {zs : Vec A (suc n + n)}
      → Interleave uneven (x ∷ xs) (y ∷ ys) (subst (Vec A) (cong suc (+-suc n n)) (x ∷ y ∷ zs))
      → Split (x ∷ xs)
      → Split (y ∷ ys)
      → Split (x ∷ y ∷ zs)
  
  insert : {n : ℕ} → {xs : Vec A n} → (z : A) → Split xs → Split (z ∷ xs)
  insert z (single x) = {!!}
  insert z (branch-e il l r) = {!!}
  insert z (branch-u il l r) = {!!}
-}
