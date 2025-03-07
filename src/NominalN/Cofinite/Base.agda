{-# OPTIONS --safe #-}
module NominalN.Cofinite.Base where

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
open import LFSet.Membership
open import LFSet.Discrete

open import Id
open import NominalN.Term

-- occurs check

-- TODO make into a datatype?
occurs : Id → Term → 𝒰
occurs v (`` x)    = v ＝ x
occurs v (p ⟶ q) = occurs v p ⊎ occurs v q
occurs v (con _)   = ⊥

occurs? : Id → Term → Bool
occurs? v (`` x)    = v == x
occurs? v (p ⟶ q) = occurs? v p or occurs? v q
occurs? v (con _)   = false

occurs-reflects : ∀ {v} {t}
                → Reflects (occurs v t) (occurs? v t)
occurs-reflects {t = `` x}    = Reflects-ℕ-Path
occurs-reflects {t = p ⟶ q} =
  Reflects-⊎ ⦃ rp = occurs-reflects {t = p} ⦄ ⦃ rq = occurs-reflects {t = q} ⦄
occurs-reflects {t = con s}   = ofⁿ id

occurs-dec : ∀ {v t} → Dec (occurs v t)
occurs-dec {v} {t} .does  = occurs? v t
occurs-dec {v} {t} .proof = occurs-reflects {v} {t}

-- one-hole context

Ctx1 : 𝒰
Ctx1 = List (Term ⊎ Term)

-- plugging the hole
_+:_ : Ctx1 → Term → Term
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
          (ap (_+: p) (snoc-append ps) ∙ +:-++ {ps = ps} ∙ ep))
no-cycle-lemma {ps = inr l ∷ ps} {t = p ⟶ q} e =
  let (_ , eq) = ⟶-inj e in
  false! (no-cycle-lemma {ps = ps ∷r inr p} {t = q}
          (ap (_+: q) (snoc-append ps) ∙ +:-++ {ps = ps} ∙ eq))
no-cycle-lemma {ps = inl r ∷ ps} {t = con s}   e = ⊥.absurd (⟶≠con e)
no-cycle-lemma {ps = inr l ∷ ps} {t = con s}   e = ⊥.absurd (⟶≠con e)

-- constraints

Constr : 𝒰
Constr = Term × Term

constr-size : Constr → ℕ
constr-size (p , q) = tm-size p + tm-size q

list-measure : List Constr → ℕ
list-measure = List.rec 0 λ c → constr-size c +_

-- context of type vars

Varctx : 𝒰
Varctx = LFSet Id

-- well-formedness

-- all variables in the type occur in the context

data wf-tm : Varctx → Term → 𝒰 where
  wf-var : ∀ {c x}   → x ∈ c                → wf-tm c (`` x)
  wf-arr : ∀ {c p q} → wf-tm c p → wf-tm c q → wf-tm c (p ⟶ q)
  wf-con : ∀ {c s}                           → wf-tm c (con s)

wf-tm-var : ∀ {c x} → wf-tm c (`` x) → x ∈ c
wf-tm-var (wf-var x∈) = x∈

wf-tm-arr : ∀ {c p q} → wf-tm c (p ⟶ q) → wf-tm c p × wf-tm c q
wf-tm-arr (wf-arr wp wq) = wp , wq

-- TODO drop wf-tm entirely?
wf-tm-vars : ∀ {c t} → vars t ⊆ c → wf-tm c t
wf-tm-vars {t = `` x} vs = wf-var (vs (hereₛ refl))
wf-tm-vars {t = p ⟶ q} vs = wf-arr (wf-tm-vars (vs ∘ ∈ₛ-∪∷←l)) (wf-tm-vars (vs ∘ ∈ₛ-∪∷←r {s₁ = vars p}))
wf-tm-vars {t = con x} vs = wf-con

{-
vars-wf-tm : ∀ {c t} → wf-tm c t → vars t ⊆ c
vars-wf-tm (wf-var x∈) = {!!}
vars-wf-tm (wf-arr wp wq) = {!!}
vars-wf-tm wf-con = false! ⦃ Refl-x∉ₛ[] ⦄
-}

wf-tm-prop : ∀ {v t} → is-prop (wf-tm v t)
wf-tm-prop (wf-var x∈)     (wf-var y∈)      = ap wf-var (hlevel 1 x∈ y∈)
wf-tm-prop (wf-arr wp₁ wq₁) (wf-arr wp₂ wq₂) = ap² wf-arr (wf-tm-prop wp₁ wp₂) (wf-tm-prop wq₁ wq₂)
wf-tm-prop  wf-con           wf-con          = refl

instance opaque
  H-Level-wf-tm : ∀ {n v t} → ⦃ n ≥ʰ 1 ⦄ → H-Level n (wf-tm v t)
  H-Level-wf-tm {t} ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance (wf-tm-prop {t = t})
  {-# OVERLAPPING H-Level-wf-tm #-}

wf-tm-dec : ∀ {v t} → Dec (wf-tm v t)
wf-tm-dec {v} {t = `` x} =
  Dec.dmap wf-var
          (contra (λ where
                       (wf-var x∈) → x∈))
           (Dec-∈ₛ {a = x} {xs = v})
wf-tm-dec {v} {t = p ⟶ q} =
  Dec.dmap (λ (wp , wq) → wf-arr wp wq)
           (contra λ where
                      (wf-arr wp wq) → wp , wq)
             (Dec-× ⦃ da = wf-tm-dec {v} {t = p} ⦄ ⦃ db = wf-tm-dec {v} {t = q} ⦄)
wf-tm-dec {t = con s} = yes wf-con

wf-tm-recomp : ∀ {v t} → Recomputable (wf-tm v t)
wf-tm-recomp = Recomputable-Dec ⦃ d = wf-tm-dec ⦄

occurs-wf-tm : ∀ {v c t} → wf-tm c t → ¬ occurs v t → wf-tm (rem v c) t
occurs-wf-tm (wf-var x∈) noc = wf-var (rem-∈-≠ (noc ∘ _⁻¹) x∈)
occurs-wf-tm (wf-arr p q) noc = wf-arr (occurs-wf-tm p (contra inl noc)) (occurs-wf-tm q (contra inr noc))
occurs-wf-tm  wf-con      noc = wf-con

wf-tm-occurs : ∀ {v c t} → wf-tm (rem v c) t → (¬ occurs v t) × wf-tm c t
wf-tm-occurs {v} {c} (wf-var {x} x∈)   =
  let (ne , x∈′) = rem-∈ x∈ in
  ne ∘ _⁻¹ , wf-var x∈′
wf-tm-occurs (wf-arr wp wq) =
  let (np , wp′) = wf-tm-occurs wp
      (nq , wq′) = wf-tm-occurs wq
    in
  ([ np , nq ]ᵤ) , wf-arr wp′ wq′
wf-tm-occurs  wf-con        = id , wf-con

-- TODO All on LFSet ?
wf-tm-minus-occurs : ∀ {v s t} → wf-tm (minus v s) t → (∀ x → x ∈ s → ¬ occurs x t) × wf-tm v t
wf-tm-minus-occurs {v} {s} {t} = elim-prop go s
  where
  go : Elim-prop λ q → wf-tm (minus v q) t → (∀ x → x ∈ q → ¬ occurs x t) × wf-tm v t
  go .[]ʳ wm =
      (λ x x∈ → false! ⦃ Refl-x∉ₛ[] ⦄ x∈)
    , subst (λ q → wf-tm q t) minus-[]-r wm
  go .∷ʳ x {xs} ih wm =
    let nihw1 = wf-tm-occurs $ subst (λ q → wf-tm q t) (minus-∷-r {s = v} {r = xs}) wm
        nihw2 = ih (nihw1 .snd)
      in
      (λ z z∈ oc →
           Recomputable-⊥ .recompute $ erase $
           rec! [ (λ e → nihw1 .fst (subst (λ q → occurs q t) e oc))
                , (λ z∈′ → nihw2 .fst z z∈′ oc) ]ᵤ
             (∈ₛ-∷→ᴱ z∈ .erased))
    , nihw2 .snd
  go .truncʳ _ = hlevel!

wf-tm-occurs-minus : ∀ {v s t} → wf-tm v t → (∀ x → x ∈ s → ¬ occurs x t) → wf-tm (minus v s) t
wf-tm-occurs-minus {v} {s} {t} wt = elim-prop go s
  where
  go : Elim-prop λ q → (∀ x → x ∈ q → ¬ occurs x t) → wf-tm (minus v q) t
  go .[]ʳ wm =
    subst (λ q → wf-tm q t) (minus-[]-r ⁻¹) wt
  go .∷ʳ x {xs} ih wm =
    subst (λ q → wf-tm q t) (minus-∷-r {s = v} {r = xs} ⁻¹) $
    (occurs-wf-tm (ih (λ z z∈ → wm z (thereₛ z∈))) (wm x (hereₛ refl)))
  go .truncʳ _ = hlevel!

-- well-formed constraint list

wf-constr-list : Varctx → List Constr → 𝒰
wf-constr-list c l = All (λ x → wf-tm c (x .fst) × wf-tm c (x .snd)) l

-- set of constraints

Constrs : 𝒰
Constrs = Varctx × List Constr

