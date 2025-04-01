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
-- open import Data.Maybe.Instances.Map.Properties
-- open import Data.Maybe.Instances.Idiom.Properties
open import Data.Vec.Inductive

open import LFSet
open import Unfinite
open import State
open import SubC

open import Id

open import NominalN.Term
-- open import NominalN.Cofinite.BaseA
-- open import NominalN.Cofinite.Sub
-- open import NominalN.Cofinite.ISub

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

pre-process1 : ∀ {n} → Vec Term n → State (Sy × SubC Id Sy) (Vec Term n)
pre-process1 = traverse pre-process-loop

pre-process : ∀ {n} → Vec Term n → Vec Term n × SubC Id Sy
pre-process ts =
  let sys = bindₛ syms (from-vec ts)
      (ts′ , (_ , s)) = runState (pre-process1 ts) ((unfin-String .new sys) , empS)
    in
  ts′ , s

-- postprocessing

post-process : Term → SubC Sy Id → Term
post-process t@(`` _)   _ = t
post-process   (p ⟶ q) s =
  post-process p s ⟶ post-process q s
post-process t@(con c)  s =
  Maybe.rec t ``_ (lupS c s)
