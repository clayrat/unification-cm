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
open import Data.Maybe.Instances.Map.Properties
open import Data.Maybe.Instances.Idiom.Properties
open import Data.List as List
open import Data.List.Correspondences.Unary.All

open import LFSet
open import Unfinite
open import State
open import SubC

open import Id

open import NominalN.Term
open import NominalN.Cofinite.BaseA
open import NominalN.Cofinite.Sub
open import NominalN.Cofinite.ISub

private variable
  ℓᵃ ℓᵇ ℓᶜ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ

-- generator

gen : Unfinite B → A → State (B × SubC A B) B
gen ub a =
  do x , s ← st-get
     st-put (new1 ub x , insS a x s)
     pure x

-- preprocessing

pre-process-loop : Term → State (Sy × SubC Id Sy) Term
pre-process-loop (`` x)    =
  do s ← st-gets snd
     Maybe.rec
       (map con (gen unfin-String x))
       (λ c → pure (con c))
       (lupS x s)
pre-process-loop (p ⟶ q) =
  do p′ ← pre-process-loop p
     q′ ← pre-process-loop q
     pure (p′ ⟶ q′)
pre-process-loop t@(con _) = pure t

pre-process1 : Term → List Term → State (Sy × SubC Id Sy) (Term × List Term)
pre-process1 t ts =
  do t′ ← pre-process-loop t
     ts′ ← traverse pre-process-loop ts
     pure (t′ , ts′)

pre-process : Term → List Term → Term × List Term × SubC Id Sy
pre-process t ts =
  let sys = bindₛ syms (from-list ts)
      ((t′ , ts′) , (_ , s)) = runState (pre-process1 t ts) ((unfin-String .new sys) , empS)
   in
  t′ , ts′ , s

-- postprocessing

post-process : Term → SubC Sy Id → Term
post-process t@(`` _)   _ = t
post-process   (p ⟶ q) s =
  post-process p s ⟶ post-process q s
post-process t@(con c)  s =
  Maybe.rec t ``_ (lupS c s)
