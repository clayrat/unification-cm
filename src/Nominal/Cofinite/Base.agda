{-# OPTIONS --safe #-}
module Nominal.Cofinite.Base where

open import Prelude
open import Meta.Effect

open import Data.Empty hiding (_≠_)
open import Data.Unit
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.List as List
open import Data.List.Correspondences.Unary.All
open import Data.List.Operations.Properties
open import Data.Sum

open import LFSet as LFSet
open import LFSet.Mem

open import Nominal.Ty

-- occurs check

occurs : Id → Ty → 𝒰
occurs v (`` x)    = v ＝ x
occurs v (p ⟶ q) = occurs v p ⊎ occurs v q
occurs v con       = ⊥

occurs? : Id → Ty → Bool
occurs? v (`` x)    = v == x
occurs? v (p ⟶ q) = occurs? v p or occurs? v q
occurs? v con       = false

occurs-reflects : ∀ {v} {t}
                → Reflects (occurs v t) (occurs? v t)
occurs-reflects {t = `` x}    = Reflects-ℕ-Path
occurs-reflects {t = p ⟶ q} =
  Reflects-⊎ ⦃ rp = occurs-reflects {t = p} ⦄ ⦃ rq = occurs-reflects {t = q} ⦄
occurs-reflects {t = con}     = ofⁿ id

occurs-dec : ∀ {v t} → Dec (occurs v t)
occurs-dec {v} {t} .does  = occurs? v t
occurs-dec {v} {t} .proof = occurs-reflects {v} {t}

-- constraints

Constr : 𝒰
Constr = Ty × Ty

constr-size : Constr → ℕ
constr-size (p , q) = ty-size p + ty-size q

list-measure : List Constr → ℕ
list-measure = List.rec 0 λ c → constr-size c +_

-- context of type vars

Varctx : 𝒰
Varctx = LFSet Id

-- well-formedness

-- all variables in the type occur in the context

-- TODO this should probably be data?
wf-ty : Varctx → Ty → 𝒰
wf-ty c (`` x)    = x ∈ c
wf-ty c (p ⟶ q) = wf-ty c p × wf-ty c q
wf-ty c con       = ⊤

wf-ty-prop : ∀ {v t} → is-prop (wf-ty v t)
wf-ty-prop {t = `` x} = hlevel!
wf-ty-prop {t = p ⟶ q} =
  ×-is-of-hlevel 1 (wf-ty-prop {t = p}) (wf-ty-prop {t = q})
wf-ty-prop {t = con} = hlevel!

{-
instance opaque
  H-Level-wf-ty : ∀ {n v t} → ⦃ n ≥ʰ 1 ⦄ → H-Level n (wf-ty v t)
  H-Level-wf-ty {t} ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance (wf-ty-prop {t = t})
  {-# OVERLAPPING H-Level-wf-ty #-}
-}

wf-ty-recomp : ∀ {v t} → Recomputable (wf-ty v t)
wf-ty-recomp {t = `` x} = Recomputable-∈ₛ
wf-ty-recomp {t = p ⟶ q} =
  Recomputable-× (wf-ty-recomp {t = p}) (wf-ty-recomp {t = q})
wf-ty-recomp {t = con} = Recomputable-⊤

wf-constr-list : Varctx → List Constr → 𝒰
wf-constr-list c l = All (λ x → wf-ty c (x .fst) × wf-ty c (x .snd)) l

opaque
  unfolding rem
  wf-ty-remove-weak : ∀ {x c} t → wf-ty (rem x c) t → wf-ty c t
  wf-ty-remove-weak {x} {c} (`` y)    w         = filter-⊆ {p = not ∘ x =?_} {s = c} w
  wf-ty-remove-weak {x}     (p ⟶ q) (wp , wq) = wf-ty-remove-weak {x = x} p wp , wf-ty-remove-weak {x = x} q wq
  wf-ty-remove-weak          con      w         = tt

wf-ty-minus-weaken : ∀ {v s t} → wf-ty (minus v s) t → wf-ty v t
wf-ty-minus-weaken {v} {s} {t} = elim-prop go s
  where
  go : Elim-prop λ q → wf-ty (minus v q) t → wf-ty v t
  go .[]ʳ = subst (λ q → wf-ty q t) minus-[]-r
  go .∷ʳ x {xs} ih = ih ∘ wf-ty-remove-weak {x = x} t ∘ subst (λ q → wf-ty q t) (minus-∷-r {s = v} {r = xs})
  go .truncʳ _ = fun-is-of-hlevel 1 (wf-ty-prop {v} {t})

opaque
  unfolding rem
  occurs-wf-ty : ∀ {v c} t → wf-ty c t → ¬ occurs v t → wf-ty (rem v c) t
  occurs-wf-ty (`` x)    w         noc =
    LFSet.Mem.∈-filter (not-so (contra so→true! noc)) w
  occurs-wf-ty (p ⟶ q) (wp , wq) noc =
    occurs-wf-ty p wp (contra inl noc) , occurs-wf-ty q wq (contra inr noc)
  occurs-wf-ty  con      w         noc = tt

  wf-ty-occurs : ∀ {v c} t → wf-ty (rem v c) t → (¬ occurs v t) × wf-ty c t
  wf-ty-occurs {c} (`` x)    w =
    first (contra true→so! ∘ so-not) (LFSet.Mem.filter-∈ {s = c} w)
  wf-ty-occurs (p ⟶ q) (wp , wq) =
    let (np , wp′) = wf-ty-occurs p wp
        (nq , wq′) = wf-ty-occurs q wq
      in
    ([ np , nq ]ᵤ) , wp′ , wq′
  wf-ty-occurs  con      w = id , tt

-- set of constraints

Constrs : 𝒰
Constrs = Varctx × List Constr

