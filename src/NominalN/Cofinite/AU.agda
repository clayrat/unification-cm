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

uncouple : Term → List Term → Maybe ((Term × List Term) × (Term × List Term))
uncouple (p ⟶ q) ts =
  map ((λ where (ps , qs) → (p , ps) , (q , qs)) ∘ unzip) $
  traverse ⟶-split ts
uncouple _         _ = nothing

tm-sizes : List Term → ℕ
tm-sizes = List.rec 0 λ t → tm-size t +_

-- TODO how to make these less adhoc?
{-
traverse-length : ∀ {ts} {pqs : List (Term × Term)}
               → list-traverse ⟶-split ts ＝ just pqs
               → length ts ＝ length pqs
traverse-length {ts = []} e = ap length (just-inj e)
traverse-length {ts = (`` _) ∷ ts} e = false! e
traverse-length {ts = con _ ∷ ts} e = false! e
traverse-length {ts = (p ⟶ q) ∷ ts} {pqs = []} e =
  let (x , _ , eq) = mapₘ=just e in
  false! eq
traverse-length {ts = (p ⟶ q) ∷ ts} {pqs = (u , v) ∷ pqs} e =
  let (x , meq , eq) = mapₘ=just e in
  ap suc (traverse-length {ts = ts} {pqs = pqs} (meq ∙ ap just (∷-tail-inj eq)))
-}

traverse-sizes : ∀ {ts} {pqs : List (Term × Term)}
               → list-traverse ⟶-split ts ＝ just pqs
               → let (ps , qs) = unzip pqs in
                 (tm-sizes ps ≤ tm-sizes ts)
               × (tm-sizes qs ≤ tm-sizes ts)
traverse-sizes {ts = []}                           e =
  let e′ = just-inj e in
    subst (λ q → tm-sizes (unzip q .fst) ≤ 0) e′ z≤
  , subst (λ q → tm-sizes (unzip q .snd) ≤ 0) e′ z≤
traverse-sizes {ts = t ∷ ts} {pqs = []}            e =
  let ((p′ , q′) , xs , _ , _ , ceq) = map²ₘ=just {f = _∷_} {ma = ⟶-split t} e in
  false! ceq
traverse-sizes {ts = t ∷ ts} {pqs = (p , q) ∷ pqs} e =
  let ((p′ , q′) , xs , steq , treq , ceq) = map²ₘ=just {f = _∷_} {ma = ⟶-split t} e
      teq = ⟶-split=just steq
      (ps≤ , qs≤) = traverse-sizes {ts = ts} {pqs = pqs} (treq ∙ ap just (∷-tail-inj ceq))
      pqeq = ×-path-inv $ ∷-head-inj ceq
   in
    ≤-+ (subst (λ w → tm-size p ≤ tm-size w)
               (teq ⁻¹)
               (≤-ascend ∙ s≤s (=→≤ (ap tm-size (pqeq .fst ⁻¹)) ∙ ≤-+-r)))
        ps≤
  , ≤-+ (subst (λ w → tm-size q ≤ tm-size w)
               (teq ⁻¹)
               (≤-ascend ∙ s≤s (=→≤ (ap tm-size (pqeq .snd ⁻¹)) ∙ ≤-+-l)))
        qs≤

uncouple-sizes : ∀ {t ts p ps q qs}
               → uncouple t ts ＝ just ((p , ps) , (q , qs))
               → (tm-sizes (p ∷ ps) < tm-sizes (t ∷ ts))
               × (tm-sizes (q ∷ qs) < tm-sizes (t ∷ ts))
uncouple-sizes {t = `` _}           e = false! e
uncouple-sizes {t = p′ ⟶ q′} {ts} {p} {q} e =
  let (pqs , meq , eq) = mapₘ=just e
      treq = traverse-sizes {ts = ts} meq
      (ppseq , qqseq) = ×-path-inv eq
      (peq , pseq) = ×-path-inv ppseq
      (qeq , qseq) = ×-path-inv qqseq
    in
    <-≤-+ (<-+-r (subst (λ w → tm-size p < 1 + tm-size w) (peq ⁻¹) <-ascend))
          (=→≤ (ap tm-sizes (pseq ⁻¹)) ∙ treq .fst)
  , <-≤-+ (≤-<-trans (=→≤ (ap tm-size (qeq ⁻¹))) (<-+-0lr z<s))
          (=→≤ (ap tm-sizes (qseq ⁻¹)) ∙ treq .snd)
uncouple-sizes {t = con _}    e = false! e

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
