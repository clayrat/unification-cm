module NominalN.Cofinite.AU where

open import Prelude
open import Meta.Effect
open import Meta.Effect.Traversable

open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.String
open import Data.Maybe as Maybe
open import Data.List as List
open import Data.List.Correspondences.Unary.All

open import LFSet
open import Unfinite
open import State

open import Id
open import NominalN.Term
open import NominalN.Cofinite.Base
open import NominalN.Cofinite.Sub
open import NominalN.Cofinite.ISub

private variable
  ℓᵃ ℓᵇ ℓᶜ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ

{-
-- TODO upstream

unzip-with : (A → B × C) → List A → List B × List C
unzip-with f [] = [] , []
unzip-with f (a ∷ as) =
  let b , c = f a in
  ((b ∷_) × (c ∷_)) $ unzip-with f as
-}

unzip-with-m : (A → Maybe (B × C)) → List A -> Maybe (List B × List C)
unzip-with-m f as =
  map unzip $ traverse f as

uncouple : Term → List Term → Maybe (Term × List Term × Term × List Term)
uncouple (p ⟶ q) ts =
  map (λ where (ps , qs) → p , ps , q , qs) (unzip-with-m ⟶-split ts)
uncouple _         _ = nothing

-- computational substitution
-- TODO unify with MM

SubT : 𝒰 → 𝒰 → 𝒰
SubT A B = List (A × B)

empST : SubT A B
empST = []

lupST : ⦃ is-discrete A ⦄ → A → SubT A B → Maybe B
lupST a [] = nothing
lupST a ((x , b) ∷ s) = if a =? x then just b else lupST a s

insST : A → B → SubT A B → SubT A B
insST a b s = (a , b) ∷ s

invST : SubT A B → SubT B A
invST = map (λ where (a , b) → (b , a))

-- generator

gen : Unfinite B → A → State (B × SubT A B) B
gen ub a =
  do x , s ← st-get
     st-put (new1 ub x , insST a x s)
     pure x

-- preprocessing

pre-process-loop : Term → State (Sy × SubT Id Sy) Term
pre-process-loop (`` x)    =
  do s ← st-gets snd
     Maybe.rec
       (map con (gen unfin-String x))
       (λ c → pure (con c))
       (lupST x s)
pre-process-loop (p ⟶ q) =
  do p′ ← pre-process-loop p
     q′ ← pre-process-loop q
     pure (p′ ⟶ q′)
pre-process-loop t@(con _) = pure t

pre-process1 : Term → List Term → State (Sy × SubT Id Sy) (Term × List Term)
pre-process1 t ts =
  do t′ ← pre-process-loop t
     ts′ ← traverse pre-process-loop ts
     pure (t′ , ts′)

pre-process : Term → List Term → Term × List Term × SubT Id Sy
pre-process t ts =
  let sys = bindₛ syms (from-list ts)
      ((t′ , ts′) , (_ , s)) = runState (pre-process1 t ts) ((unfin-String .new sys) , empST)
   in
  t′ , ts′ , s

-- postprocessing

post-process : Term → SubT Sy Id → Term
post-process t@(`` _)   _ = t
post-process   (p ⟶ q) s =
  post-process p s ⟶ post-process q s
post-process t@(con c)  s =
  Maybe.rec t ``_ (lupST c s)
