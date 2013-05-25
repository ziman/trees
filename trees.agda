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

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {x y z x' y' z'} → x ≡ x' → y ≡ y' → z ≡ z' → f x y z ≡ f x' y' z'
cong₃ f refl refl refl = refl

module Logarithm where

  {-
  data Balance : Set where
    even uneven : Balance

  other : Balance → Balance
  other even = uneven
  other uneven = even

  data Balanced : Balance → (x y z : ℕ) → Set where
    base : Balanced even zero zero zero
    step : ∀ {x y z b} → Balanced (other b) x y z → Balanced b (suc y) x (suc z)

  bal-eq-weak : ∀ {x y x' y' z e} → Balanced e x y z → Balanced e x' y' z → x ≡ x' × y ≡ y'
  bal-eq-weak base base = refl , refl
  bal-eq-weak (step b) (step b') with bal-eq-weak b b'
  ... | eqx , eqy = cong suc eqy , eqx

  bal-even : ∀ {x y z} → Balanced even x y z → x ≡ y
  bal-even base = refl
  bal-even (step (step b)) = cong suc (bal-even b)

  bal-uneven : ∀ {x y z} → Balanced uneven x y z → x ≡ suc y
  bal-uneven (step base) = refl
  bal-uneven (step (step b)) = cong suc (bal-uneven b)

  bal-eq-balance : ∀ {x y x' y' z e e'} → Balanced e x y z → Balanced e' x' y' z → e ≡ e'
  bal-eq-balance {e = even}   {e' = even}    base     base     = refl
  bal-eq-balance {e = even}   {e' = even}   (step b) (step b') = refl
  bal-eq-balance {e = even}   {e' = uneven}  base    ()
  bal-eq-balance {e = even}   {e' = uneven} (step b) (step b') = bal-eq-balance b' b
  bal-eq-balance {e = uneven} {e' = even}   (step b) (step b') = bal-eq-balance b' b
  bal-eq-balance {e = uneven} {e' = uneven} (step b) (step b') = refl

  bal-eq : ∀ {x y x' y' z e e'} → Balanced e x y z → Balanced e' x' y' z → e ≡ e' × x ≡ x' × y ≡ y'
  bal-eq b b' with bal-eq-balance b b'
  bal-eq b b' | refl = refl , bal-eq-weak b b'

  bal-irr : ∀ {x y z e} → (b b' : Balanced e x y z) → b ≡ b'
  bal-irr base base = refl
  bal-irr (step b) (step b') = cong step (bal-irr b b')
  -}

  data LogTree : ℕ → Set where
    single : LogTree (suc zero)
    double : ∀ {x y z {- b -} }
      {- → Balanced b (suc x) (suc y) (suc (suc z)) -}
      → LogTree (suc x)
      → LogTree (suc y)
      → LogTree (suc (suc z))

  depth : ∀ {n} → LogTree n → ℕ
  depth single = 0
  depth (double {- b -} l r) = suc (depth r)

  {-
  logtree-irr : ∀ {n} → (p q : LogTree n) → p ≡ q
  logtree-irr single single = refl
  logtree-irr (double {b = b} b₁ lx₁ ly₁) (double b₂ lx₂ ly₂) with bal-eq b₁ b₂
  ... | refl , refl , refl = cong₃ double (bal-irr b₁ b₂) (logtree-irr lx₁ lx₂) (logtree-irr ly₁ ly₂)
  -}

  inc : ∀ {n} → LogTree n → LogTree (suc n)
  inc single = double {- (step (step base)) -} single single
  inc (double {- b =   even bal -} lx ly) = double {- (step bal) -} (inc ly) lx
  {- inc (double {b = uneven bal} lx ly) = double (step bal) (inc ly) lx -}

  logtree : (n : ℕ) → LogTree (suc n)
  logtree  zero   = single
  logtree (suc n) = inc (logtree n)

  log : (n : ℕ) → n ≢ 0 → ℕ
  log zero    0≢0 = ⊥-elim (0≢0 refl)
  log (suc n) n≢0 = depth (logtree n)

{-
module TreeSplit {A : Set} where

  data Evenness : Set where
    even uneven : Evenness

  other : Evenness → Evenness
  other   even = uneven
  other uneven =   even

  data Interleave : Evenness → List A → List A → List A → Set where
    base : Interleave even [] [] []
    step : ∀ {x xs ys zs e} → Interleave (other e) xs ys zs → Interleave e (x ∷ ys) xs (x ∷ zs)

  il-irr : ∀ {xs ys zs e} → (p q : Interleave e xs ys zs) → p ≡ q
  il-irr base base = refl
  il-irr (step p) (step q) = cong step (il-irr p q)

  il-eq-evenness : ∀ {xs ys xs' ys' zs e e'} → Interleave e xs ys zs → Interleave e' xs' ys' zs → e ≡ e'
  il-eq-evenness {e = even}   {e' = even}    base      base      = refl
  il-eq-evenness {e = even}   {e' = even}   (step il) (step il') = refl
  il-eq-evenness {e = even}   {e' = uneven}  base     ()
  il-eq-evenness {e = even}   {e' = uneven} (step il) (step il') = il-eq-evenness il' il
  il-eq-evenness {e = uneven} {e' = even}   (step il) (step il') = il-eq-evenness il' il
  il-eq-evenness {e = uneven} {e' = uneven} (step il) (step il') = refl

  il-eq-weak : ∀ {xs ys xs' ys' zs e} → Interleave e xs ys zs → Interleave e xs' ys' zs → xs ≡ xs' × ys ≡ ys'
  il-eq-weak base base = refl , refl
  il-eq-weak (step il) (step il') with il-eq-weak il il'
  ... | refl , refl = refl , refl

  il-eq : ∀ {xs ys xs' ys' zs e e'} → Interleave e xs ys zs → Interleave e' xs' ys' zs → e ≡ e' × xs ≡ xs' × ys ≡ ys'
  il-eq il il' with il-eq-evenness il il'
  ... | refl = refl , il-eq-weak il il'

  il-length : ∀ {xs ys zs} → Interleave even xs ys zs → length xs ≡ length ys
  il-length base = refl
  il-length (step (step il)) = cong suc (il-length il)

  data Split : List A → Set where
    single : ∀ x → Split (x ∷ []) 
    branch : ∀ x y {xs ys zs} e
      → Interleave e (x ∷ xs) (y ∷ ys) (x ∷ y ∷ zs)
      → (l : Split (x ∷ xs))
      → (r : Split (y ∷ ys))
      → Split (x ∷ y ∷ zs)

  depth : ∀ {xs} → Split xs → ℕ
  depth (single _) = 0
  depth (branch _ _ _ _ l r) = suc (depth r)

  il-depth : ∀ {xs ys zs} → Interleave even xs ys zs → (sx : Split xs) → (sy : Split xs) → depth sx ≡ depth sy
  il-depth base () ()
  il-depth (step i) (single x) (single .x) = refl
  il-depth (step i) (branch x y e il l r) (branch .x .y e' il' l' r') = cong suc {!!}

  length-depth : ∀ {xs ys} → (sx : Split xs) → (sy : Split ys) → length xs ≡ length ys → depth sx ≡ depth sy
  length-depth (single x) (single x') eq = refl
  length-depth (branch x y even il sx sy) (branch x' y' even il' sx' sy') eq = {!!}
  length-depth (branch x y even il sx sy) (branch x' y' uneven il' sx' sy') eq = {!!}
  length-depth (branch x y uneven il sx sy) (branch x' y' even il' sx' sy') eq = {!!}
  length-depth (branch x y uneven il sx sy) (branch x' y' uneven il' sx' sy') eq = {!!}
  length-depth (single x) (branch x₁ y e x₂ sy sy₁) ()
  length-depth (branch x y e x₁ sx sx₁) (single x₂) ()
  
  split-irr : ∀ {xs} → (p q : Split xs) → p ≡ q
  split-irr (single x) (single .x) = refl
  split-irr (branch x y e il l r) (branch .x .y e' il' l' r') with il-eq il il'
  ... | e=e' , refl , refl rewrite e=e' = cong₃ (branch x y e') (il-irr il il') (split-irr l l') (split-irr r r')

  insert : ∀ z {zs} → Split zs → Split (z ∷ zs)
  insert z (single x) = branch z x even (step (step base)) (single z) (single x)
  insert z (branch x y   even il l r) = branch z x uneven (step il) (insert z r) l
  insert z (branch x y uneven il l r) = branch z x   even (step il) (insert z r) l

  split : ∀ x xs → Split (x ∷ xs)
  split x []       = single x
  split x (y ∷ xs) = insert x (split y xs)

  data Exp : ℕ → List A → Set where
    single : ∀ x → Exp zero (x ∷ [])
    branch : ∀ {xs ys zs n}
      → Interleave even xs ys zs
      → Exp n xs
      → Exp n ys
      → Exp (suc n) zs
  
  exp? : ∀ {xs} → (s : Split xs) → Maybe (Exp (depth s) xs)
  exp? (single x) = just (single x)
  exp? (branch x y uneven il l r) = nothing
  exp? (branch x y even il l r) with exp? l | exp? r
  ... | nothing | nothing = nothing
  ... | just el | nothing = nothing
  ... | nothing | just er = nothing
  ... | just el | just er = just (branch il {!!} er)
-}

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

  data Interleave : Evenness → {n n' : ℕ} → Vec A n → Vec A n' → Vec A (n + n') → Set where
    base : Interleave even [] [] []
    step-e : ∀ {n x xs ys zs}
      → Interleave uneven {suc n} {n} ys xs (subst (Vec A) (+-suc' n n) zs)
      → Interleave even {suc n} {suc n} (x ∷ xs) ys (x ∷ zs)
    step-u : ∀ {n x xs ys zs}
      → Interleave even {n} {n} ys xs zs
      → Interleave uneven {suc n} {n} (x ∷ xs) ys (x ∷ zs)

{-
  data Split : {n : ℕ} → Vec A n → Set where
    single : ∀ x → Split (x ∷ [])
    branch-e : ∀ {n x y} {xs : Vec A n} {ys : Vec A n} {zs : Vec A (n + n)}
      → Interleave even
-}
{-
  data Split : {n : ℕ} (xs : Vec A n) → Set where
    single : ∀ x → Split (x ∷ [])
    branch : ∀ {x y xn yn} {xs : Vec A xn} {ys : Vec A yn} {zs : Vec A (xn + yn)}
      → (e : Evenness)
      → Interleave e (x ∷ xs) (y ∷ ys) (subst (Vec A) (+-suc xn yn) (x ∷ y ∷ zs))
      → Split (x ∷ xs)
      → Split (y ∷ ys)
      → Split (x ∷ y ∷ zs)
-}







































































































{-
  insert : ∀ {xs n} → (x : A) → Split n xs → ∃ λ n' → Split n' (x ∷ xs)
  insert z (single x) = 1 , branch z x even (step (step base)) (single z) (single x)
  insert {n = suc n} z (branch x y even il sx sy) = 
    suc n , branch z x uneven (step il) (insert z sy) sx
  insert z (branch x y uneven il sx sy) = 
    _ , branch z x   even (step il) (insert z sy) sx
-}
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



