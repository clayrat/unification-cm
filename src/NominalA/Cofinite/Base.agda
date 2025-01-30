{-# OPTIONS --safe #-}
module NominalA.Cofinite.Base where

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
open import Data.List.Correspondences.Unary.Any

open import Data.List.Operations.Properties
open import Data.Sum

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

open import NominalA.Term

-- occurs check

-- TODO make into a datatype?
mutual
  occurs : Id → Term → 𝒰
  occurs v (`` x)     = v ＝ x
  occurs v (con s ts) = occurs-list v ts

  occurs-list : Id → List Term → 𝒰
  occurs-list v [] = ⊥
  occurs-list v (t ∷ ts) = occurs v t ⊎ occurs-list v ts

mutual
  occurs? : Id → Term → Bool
  occurs? v (`` x)     = v == x
  occurs? v (con s ts) = occurs-list? v ts

  occurs-list? : Id → List Term → Bool
  occurs-list? v []       = false
  occurs-list? v (s ∷ ts) = occurs? v s or occurs-list? v ts

mutual
  occurs-reflects : ∀ {v t}
                  → Reflects (occurs v t) (occurs? v t)
  occurs-reflects {t = `` x}     = Reflects-ℕ-Path
  occurs-reflects {t = con s ts} = occurs-list-reflects {ts = ts}

  occurs-list-reflects : ∀ {v ts}
                       → Reflects (occurs-list v ts) (occurs-list? v ts)
  occurs-list-reflects {ts = []}     = ofⁿ id
  occurs-list-reflects {ts = t ∷ ts} =
    Reflects-⊎ ⦃ rp = occurs-reflects {t = t} ⦄ ⦃ rq = occurs-list-reflects {ts = ts} ⦄

occurs-dec : ∀ {v t} → Dec (occurs v t)
occurs-dec {v} {t} .does  = occurs? v t
occurs-dec {v} {t} .proof = occurs-reflects {v} {t}

-- one-hole context

Ctx1 : 𝒰
Ctx1 = List (Sy × List Term × List Term)

-- plugging the hole
_+:_ : Ctx1 → Term → Term
[]                 +: t = t
((s , l , r) ∷ ts) +: t = con s (l ++ (ts +: t) ∷ r)

mutual
  occ→ctx : ∀ {v t} → occurs v t → Σ[ c ꞉ Ctx1 ] (t ＝ c +: (`` v))
  occ→ctx {t = `` x}     oc = [] , ap ``_ (oc ⁻¹)
  occ→ctx {t = con s ts} oc =
    let (c , l , r , e) = occs→ctx {ts = ts} oc in
    (s , l , r) ∷ c , ap (con s) e

  occs→ctx : ∀ {v ts} → occurs-list v ts → Σ[ c ꞉ Ctx1 ] Σ[ l ꞉ List Term ] Σ[ r ꞉ List Term ] (ts ＝ l ++ (c +: (`` v) ∷ r))
  occs→ctx {ts = t ∷ ts} (inl ot) =
    let (c , e) = occ→ctx {t = t} ot in
    c , [] , ts , ap (_∷ ts) e
  occs→ctx {ts = t ∷ ts} (inr os) =
    let (c , l , r , e) = occs→ctx {ts = ts} os in
    c , t ∷ l , r , ap (t ∷_) e

+:-++ : ∀ {ps qs : Ctx1} {t} → (ps ++ qs) +: t ＝ ps +: (qs +: t)
+:-++ {ps = []} = refl
+:-++ {ps = (s , l , r) ∷ ps} = ap (λ q → con s (l ++ q ∷ r)) (+:-++ {ps = ps})

mutual
  no-cycle-lemma : ∀ {ps : Ctx1} {t} → ps +: t ＝ t → ps ＝ []
  no-cycle-lemma {ps = []}                               _ = refl
  no-cycle-lemma {ps = (s , l , r) ∷ ps} {t = `` x}      e = ⊥.absurd (``≠con (e ⁻¹))
  no-cycle-lemma {ps = (s , l , r) ∷ ps} {t = con sy ts} e =
    let (_ , tse) = con-inj e in
    absurd (no-cycles {ps = ps} {s = sy} {ts = ts} {zs = []} refl
              (subst ((ps +: con sy ts) ∈_) tse
                 (any-++-r (here refl))))

  no-cycles : ∀ {ps : Ctx1} {s} {ts qs zs} → qs ＝ zs ++ ts → (ps +: con s qs) ∉ ts
  no-cycles {ps} {s} {ts = t ∷ ts} {zs} qe (here px) =
   false! (no-cycle-lemma {ps = ps ∷r (s , zs , ts)}
            (  ap (_+: t) (snoc-append ps)
             ∙ +:-++ {ps = ps}
             ∙ ap (λ q → ps +: con s q) (qe ⁻¹)
             ∙ px))
  no-cycles          {ts = t ∷ ts} {zs} qe (there m) =
    no-cycles {zs = zs ∷r t} (qe ∙ ++-assoc zs (t ∷ []) ts ⁻¹ ∙ ap (_++ ts) (snoc-append zs ⁻¹)) m

-- constraints

Constr : 𝒰
Constr = Term × Term

constr-size : Constr → ℕ
constr-size (p , q) = term-size p + term-size q

list-measure : List Constr → ℕ
list-measure = List.rec 0 λ c → constr-size c +_

list-measure-++ : ∀ {xs ys} → list-measure (xs ++ ys) ＝ list-measure xs + list-measure ys
list-measure-++ {xs} {ys} =
    rec-++ 0 (λ c → constr-size c +_) xs ys
  ∙ rec-fusion xs (λ x y → +-assoc (constr-size x) y (list-measure ys) ⁻¹) ⁻¹

-- TODO adhoc
list-measure-zip : ∀ {ts ts′}
                 → length ts ＝ length ts′
                 → list-measure (zip ts ts′) ＝ terms-size ts + terms-size ts′
list-measure-zip {ts = []}     {ts′ = []}       e = refl
list-measure-zip {ts = []}     {ts′ = t ∷ ts′}  e = false! e
list-measure-zip {ts = t ∷ ts} {ts′ = []}       e = false! e
list-measure-zip {ts = t ∷ ts} {ts′ = t′ ∷ ts′} e =
  ap (term-size t + term-size t′ +_) (list-measure-zip (suc-inj e))
  ∙ +-interchange (term-size t) (term-size t′) (terms-size ts) (terms-size ts′)

-- context of type vars

Varctx : 𝒰
Varctx = LFSet Id

-- well-formedness

-- all variables in the type occur in the context

data wf-tm : Varctx → Term → 𝒰 where
  wf-var : ∀ {c x}    → x ∈ c           → wf-tm c (`` x)
  wf-con : ∀ {c s ts} → All (wf-tm c) ts → wf-tm c (con s ts)

wf-tm-var : ∀ {c x} → wf-tm c (`` x) → x ∈ c
wf-tm-var (wf-var x∈) = x∈

wf-tm-con : ∀ {c s ts} → wf-tm c (con s ts) → All (wf-tm c) ts
wf-tm-con (wf-con wa) = wa

mutual
  wf-tm-prop : ∀ {v t} → is-prop (wf-tm v t)
  wf-tm-prop (wf-var x∈) (wf-var y∈)  = ap wf-var (hlevel 1 x∈ y∈)
  wf-tm-prop (wf-con wa₁) (wf-con wa₂) = ap wf-con (wf-tms-prop wa₁ wa₂)

  -- inlining all-is-of-hlevel :(
  wf-tms-prop : ∀ {v ts} → is-prop (All (wf-tm v) ts)
  wf-tms-prop     {ts = []}     []         []         = refl
  wf-tms-prop {v} {ts = t ∷ ts} (w₁ ∷ ws₁) (w₂ ∷ ws₂) =
    ap² {C = λ x xa → All (wf-tm v) (t ∷ ts)} _∷_ (wf-tm-prop w₁ w₂) (wf-tms-prop ws₁ ws₂)

instance opaque
  H-Level-wf-tm : ∀ {n v t} → ⦃ n ≥ʰ 1 ⦄ → H-Level n (wf-tm v t)
  H-Level-wf-tm {t} ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance (wf-tm-prop {t = t})
  {-# OVERLAPPING H-Level-wf-tm #-}

mutual
  wf-tm-dec : ∀ {v t} → Dec (wf-tm v t)
  wf-tm-dec {v} {t = `` x} =
    Dec.dmap wf-var
             (contra wf-tm-var)
             (Dec-∈ₛ {a = x} {xs = v})
  wf-tm-dec {v} {t = con s ts} =
    Dec.dmap wf-con
             (contra wf-tm-con)
             wf-tms-dec

  -- more inlining
  wf-tms-dec : ∀ {v ts} → Dec (All (wf-tm v) ts)
  wf-tms-dec {ts = []}     = yes []
  wf-tms-dec {ts = t ∷ ts} =
    Dec.dmap (λ where (d , ds) → d ∷ ds)
             (contra all-uncons)
             (Dec-× ⦃ da = wf-tm-dec  {t = t} ⦄ ⦃ db = wf-tms-dec {ts = ts} ⦄)

wf-tm-recomp : ∀ {v t} → Recomputable (wf-tm v t)
wf-tm-recomp = Recomputable-Dec ⦃ d = wf-tm-dec ⦄

mutual
  occurs-wf-tm : ∀ {v c t} → wf-tm c t → ¬ occurs v t → wf-tm (rem v c) t
  occurs-wf-tm (wf-var x∈) noc = wf-var (rem-∈-≠ (noc ∘ _⁻¹) x∈)
  occurs-wf-tm (wf-con wa) noc  = wf-con (occurs-wf-tms wa noc)

  occurs-wf-tms : ∀ {v c ts}
                → All (wf-tm c) ts
                → ¬ occurs-list v ts
                → All (wf-tm (rem v c)) ts
  occurs-wf-tms {ts = []}     []       noc = []
  occurs-wf-tms {ts = t ∷ ts} (w ∷ wa) noc =
    occurs-wf-tm w (contra inl noc) ∷ occurs-wf-tms wa (contra inr noc)

mutual
  wf-tm-occurs : ∀ {v c t} → wf-tm (rem v c) t → (¬ occurs v t) × wf-tm c t
  wf-tm-occurs     {c} (wf-var x∈) =
    let (ne , x∈′) = rem-∈ x∈ in
    ne ∘ _⁻¹ , wf-var x∈′
  wf-tm-occurs {v} {c} (wf-con wa)  =
    let (nts , wts) = wf-tms-occurs {v = v} {c = c} wa in
    nts , wf-con wts

  wf-tms-occurs : ∀ {v c ts} → All (wf-tm (rem v c)) ts → (¬ occurs-list v ts) × All (wf-tm c) ts
  wf-tms-occurs         {ts = []}     []       = id , []
  wf-tms-occurs {v} {c} {ts = t ∷ ts} (w ∷ wa) =
    let (nt , wt) = wf-tm-occurs {v = v} {c = c} w
        (nts , wts) = wf-tms-occurs {v = v} {c = c} wa
      in
    [ nt , nts ]ᵤ , wt ∷ wts

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

-- all arities are correct in the term
data wa-tm : Arity → Term → 𝒰 where
  wa-var : ∀ {a x} → wa-tm a (`` x)
  wa-con : ∀ {a s ts} → a s ＝ length ts → All (wa-tm a) ts → wa-tm a (con s ts)

wa-tm-con : ∀ {a s ts} → wa-tm a (con s ts) → (a s ＝ length ts) × All (wa-tm a) ts
wa-tm-con (wa-con e wa) = e , wa

-- well-foundedness on constraint lists

wf-constr-list : Varctx → List Constr → 𝒰
wf-constr-list c l = All (λ x → wf-tm c (x .fst) × wf-tm c (x .snd)) l

wa-constr-list : Arity → List Constr → 𝒰
wa-constr-list a l = All (λ x → wa-tm a (x .fst) × wa-tm a (x .snd)) l

-- set of constraints

Constrs : 𝒰
Constrs = Varctx × Arity × List Constr

