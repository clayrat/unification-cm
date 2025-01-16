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

-- TODO make into a datatype?
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

-- one-hole context

Ctx1 : 𝒰
Ctx1 = List (Ty ⊎ Ty)

-- plugging the hole
_+:_ : Ctx1 → Ty → Ty
[]           +: t = t
(inl r ∷ ps) +: t = (ps +: t) ⟶ r
(inr l ∷ ps) +: t = l ⟶ (ps +: t)

occ→ctx : ∀ {v t} → occurs v t → Σ[ c ꞉ Ctx1 ] (t ＝ c +: (`` v))
occ→ctx {t = `` x}   oc        = [] , (ap ``_ (oc ⁻¹))
occ→ctx {t = p ⟶ q} (inl oc) =
  let (s , e) = occ→ctx {t = p} oc in
  (inl q ∷ s) , ap (_⟶ q) e
occ→ctx {t = p ⟶ q} (inr oc) =
  let (s , e) = occ→ctx {t = q} oc in
  (inr p ∷ s) , ap (p ⟶_) e

+:-++ : ∀ {ps qs : Ctx1} {t} → (ps ++ qs) +: t ＝ ps +: (qs +: t)
+:-++ {ps = []}         = refl
+:-++ {ps = inl r ∷ ps} = ap (_⟶ r) (+:-++ {ps = ps})
+:-++ {ps = inr l ∷ ps} = ap (l ⟶_) (+:-++ {ps = ps})

no-cycle-lemma : ∀ {ps : Ctx1} {t} → ps +: t ＝ t → ps ＝ []
no-cycle-lemma {ps = []}                       e = refl
no-cycle-lemma {ps = inl r ∷ ps} {t = `` x}    e = ⊥.absurd (``≠⟶ (e ⁻¹))
no-cycle-lemma {ps = inr l ∷ ps} {t = `` x}    e = ⊥.absurd (``≠⟶ (e ⁻¹))
no-cycle-lemma {ps = inl r ∷ ps} {t = p ⟶ q} e =
  let (ep , _) = ⟶-inj e in
  false! (no-cycle-lemma {ps = ps ∷r inl q} {t = p}
          (ap (_+: p) (snoc-append ps) ∙ +:-++ {ps = ps}  ∙ ep))
no-cycle-lemma {ps = inr l ∷ ps} {t = p ⟶ q} e =
  let (_ , eq) = ⟶-inj e in
  false! (no-cycle-lemma {ps = ps ∷r inr p} {t = q}
          (ap (_+: q) (snoc-append ps) ∙ +:-++ {ps = ps}  ∙ eq))
no-cycle-lemma {ps = inl r ∷ ps} {t = con}     e = ⊥.absurd (⟶≠con e)
no-cycle-lemma {ps = inr l ∷ ps} {t = con}     e = ⊥.absurd (⟶≠con e)

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

data wf-ty : Varctx → Ty → 𝒰 where
  wf-var : ∀ {c x}   → x ∈ c                → wf-ty c (`` x)
  wf-arr : ∀ {c p q} → wf-ty c p → wf-ty c q → wf-ty c (p ⟶ q)
  wf-con : ∀ {c}                             → wf-ty c con

wf-ty-var : ∀ {c x} → wf-ty c (`` x) → x ∈ c
wf-ty-var (wf-var x∈) = x∈

wf-ty-arr : ∀ {c p q} → wf-ty c (p ⟶ q) → wf-ty c p × wf-ty c q
wf-ty-arr (wf-arr wp wq) = wp , wq

wf-ty-prop : ∀ {v t} → is-prop (wf-ty v t)
wf-ty-prop (wf-var x∈)     (wf-var y∈)      = ap wf-var (hlevel 1 x∈ y∈)
wf-ty-prop (wf-arr wp₁ wq₁) (wf-arr wp₂ wq₂) = ap² wf-arr (wf-ty-prop wp₁ wp₂) (wf-ty-prop wq₁ wq₂)
wf-ty-prop  wf-con           wf-con          = refl

instance opaque
  H-Level-wf-ty : ∀ {n v t} → ⦃ n ≥ʰ 1 ⦄ → H-Level n (wf-ty v t)
  H-Level-wf-ty {t} ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance (wf-ty-prop {t = t})
  {-# OVERLAPPING H-Level-wf-ty #-}

wf-ty-dec : ∀ {v t} → Dec (wf-ty v t)
wf-ty-dec {v} {t = `` x} =
  Dec.dmap wf-var
          (contra (λ where
                       (wf-var x∈) → x∈))
           (Dec-∈ₛ {a = x} {xs = v})
wf-ty-dec {v} {t = p ⟶ q} =
  Dec.dmap (λ (wp , wq) → wf-arr wp wq)
           (contra λ where
                      (wf-arr wp wq) → wp , wq)
             (Dec-× ⦃ da = wf-ty-dec {v} {t = p} ⦄ ⦃ db = wf-ty-dec {v} {t = q} ⦄)
wf-ty-dec {t = con} = yes wf-con

wf-ty-recomp : ∀ {v t} → Recomputable (wf-ty v t)
wf-ty-recomp = Recomputable-Dec ⦃ d = wf-ty-dec ⦄

wf-constr-list : Varctx → List Constr → 𝒰
wf-constr-list c l = All (λ x → wf-ty c (x .fst) × wf-ty c (x .snd)) l

opaque
  unfolding rem
  wf-ty-remove-weak : ∀ {x c t} → wf-ty (rem x c) t → wf-ty c t
  wf-ty-remove-weak {x} {c} (wf-var x∈)   = wf-var (filter-⊆ {p = not ∘ x =?_} {s = c} x∈)
  wf-ty-remove-weak {x}     (wf-arr wp wq) = wf-arr (wf-ty-remove-weak {x} wp) (wf-ty-remove-weak {x} wq)
  wf-ty-remove-weak          wf-con        = wf-con

wf-ty-minus-weaken : ∀ {v s t} → wf-ty (minus v s) t → wf-ty v t
wf-ty-minus-weaken {v} {s} {t} = elim-prop go s
  where
  go : Elim-prop λ q → wf-ty (minus v q) t → wf-ty v t
  go .[]ʳ = subst (λ q → wf-ty q t) minus-[]-r
  go .∷ʳ x {xs} ih = ih ∘ wf-ty-remove-weak {x = x} ∘ subst (λ q → wf-ty q t) (minus-∷-r {s = v} {r = xs})
  go .truncʳ _ = fun-is-of-hlevel 1 (wf-ty-prop {v} {t})

opaque
  unfolding rem
  occurs-wf-ty : ∀ {v c t} → wf-ty c t → ¬ occurs v t → wf-ty (rem v c) t
  occurs-wf-ty (wf-var x∈) noc = wf-var (LFSet.Mem.∈-filter (not-so (contra so→true! noc)) x∈)
  occurs-wf-ty (wf-arr p q) noc = wf-arr (occurs-wf-ty p (contra inl noc)) (occurs-wf-ty q (contra inr noc))
  occurs-wf-ty  wf-con      noc = wf-con

  wf-ty-occurs : ∀ {v c t} → wf-ty (rem v c) t → (¬ occurs v t) × wf-ty c t
  wf-ty-occurs {c} (wf-var x∈)   =
    let (ne , x∈′) = LFSet.Mem.filter-∈ {s = c} x∈ in
    contra true→so! (so-not ne) , wf-var x∈′
  wf-ty-occurs (wf-arr wp wq) =
    let (np , wp′) = wf-ty-occurs wp
        (nq , wq′) = wf-ty-occurs wq
      in
    ([ np , nq ]ᵤ) , wf-arr wp′ wq′
  wf-ty-occurs  wf-con        = id , wf-con

-- set of constraints

Constrs : 𝒰
Constrs = Varctx × List Constr

