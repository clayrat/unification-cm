{-# OPTIONS --guarded #-}
module NominalN.Cofinite.MM.Part where

open import Prelude
open import Meta.Effect

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.List as List
open import Data.List.Correspondences.Unary.Any
open import Data.List.Correspondences.Unary.All
open import Data.List.Membership
open import Data.List.Operations.Properties
open import Data.List.Operations.Discrete
open import Data.Sum as ⊎
open import Data.Plus
open import Data.AF
open import Data.Acc

open import Order.Constructions.Lex

open import Later
open import Clocked.Partial
open import Clocked.Partial.Converges
open import Clocked.Partial.All

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

open import Id
open import NominalN.Term
open import NominalN.Cofinite.Base
open import NominalN.Cofinite.Sub
open import NominalN.Cofinite.Unifier
open import NominalN.Cofinite.MM

private variable
  κ : Cl

mutual
  unifyᵏ-body : ▹ κ ((lc : List Constr) → gPart κ (SubT ⊎ UnifyFailure lc))
              → (lc : List Constr) → gPart κ (SubT ⊎ UnifyFailure lc)
  unifyᵏ-body u▹ []               = now (inl [])
  unifyᵏ-body u▹ ((tl , tr) ∷ lc) =
    Dec.rec
      (λ e → let ih▹ = u▹ ⊛ next lc in
             later (mapᵏ (map-r (eq-rec e)) ⍉ ih▹))
      (λ ne → unifyᵏ-body-head u▹ tl tr ne lc)
      (tl ≟ tr)

  unifyᵏ-body-head : ▹ κ ((lc : List Constr) → gPart κ (SubT ⊎ UnifyFailure lc))
                   → (tl tr : Term) → tl ≠ tr
                   → (lc : List Constr) → gPart κ (SubT ⊎ UnifyFailure ((tl , tr) ∷ lc))
  unifyᵏ-body-head u▹ (`` v)       tr        ne lc =
    Dec.rec
      (λ oc → now (inr (occ-fail-l (ne ∘ _⁻¹) oc)))
      (λ _ → let ih▹ = u▹ ⊛ next (app-sngL v tr lc) in
             later (mapᵏ (⊎.dmap ((v , tr) ∷_) subs-rec-l) ⍉ ih▹))
      (occurs-dec {v} {t = tr})
  unifyᵏ-body-head u▹  tl         (`` v)     ne lc =
    Dec.rec
      (λ oc → now (inr (occ-fail-r ne oc)))
      (λ _ → let ih▹ = u▹ ⊛ next (app-sngL v tl lc) in
             later (mapᵏ (⊎.dmap ((v , tl) ∷_) subs-rec-r) ⍉ ih▹))
      (occurs-dec {v} {t = tl})
  unifyᵏ-body-head u▹ (pl ⟶ ql) (pr ⟶ qr) ne lc =
    let ih▹ = u▹ ⊛ next ((pl , pr) ∷ (ql , qr) ∷ lc) in
    later (mapᵏ (map-r arrarr-rec) ⍉ ih▹)
  unifyᵏ-body-head u▹ (con sl)    (pr ⟶ qr) ne lc = now (inr con-app)
  unifyᵏ-body-head u▹ (pl ⟶ ql) (con sr)    ne lc = now (inr app-con)
  unifyᵏ-body-head u▹ (con sl)    (con sr)   ne lc = now (inr (con-con-sym (contra (ap con) ne)))

unifyᵏ : (lc : List Constr) → gPart κ (SubT ⊎ UnifyFailure lc)
unifyᵏ = fix unifyᵏ-body

unify : (lc : List Constr) → Part (SubT ⊎ UnifyFailure lc)
unify lc κ = unifyᵏ lc

-- properties

constr-vars : List Constr → Varctx
constr-vars = List.rec [] (λ where (l , r) ctx → vars l ∪∷ vars r ∪∷ ctx)

constr-vars-∈ : ∀ {l r} cs
               → (l , r) ∈ cs
               → (vars l ⊆ constr-vars cs) × (vars r ⊆ constr-vars cs)
constr-vars-∈ ((a , b) ∷ cs) (here e)    =
  let (le , re) = ×-path-inv e in
    (λ {x} x∈l →
        ∈ₛ-∪∷←l {s₁ = vars a} $
        subst (λ q → x ∈ vars q) le x∈l )
  , (λ {x} x∈r →
        ∈ₛ-∪∷←r {s₁ = vars a} $
        ∈ₛ-∪∷←l {s₁ = vars b} $
        subst (λ q → x ∈ vars q) re x∈r)
constr-vars-∈ ((a , b) ∷ cs) (there lrm) =
  let (ihl , ihr) = constr-vars-∈ cs lrm
      ss : constr-vars cs ⊆ constr-vars ((a , b) ∷ cs)
      ss = λ {x} → ∈ₛ-∪∷←r {s₁ = vars a} ∘ ∈ₛ-∪∷←r {s₁ = vars b}
    in
    (ss ∘ ihl) , (ss ∘ ihr)

wcl-constr-vars : {cs : List Constr} → wf-constr-list (constr-vars cs) cs
wcl-constr-vars {cs} =
  ∀∈→All λ where
              (l , r) lr∈ →
                 let (vl , vr) = constr-vars-∈ cs lr∈ in
                    wf-tm-vars vl
                  , wf-tm-vars vr

-- termination

unify⇓-body : ∀ (l : Constrs)
            → ((l' : Constrs) → l' <C l → wf-constr-list (l' .fst) (l' .snd) → (unify (l' .snd)) ⇓)
            → wf-constr-list (l .fst) (l .snd) → (unify (l .snd)) ⇓
unify⇓-body (ctx , []) ih wcl = (inl []) , ∣ 0 , refl ∣₁
unify⇓-body (ctx , (tl , tr) ∷ lc) ih wcl with tl ≟ tr
unify⇓-body (ctx , (tl , tr) ∷ lc) ih wcl | yes e =
  let (res , cnv) = ih (ctx , lc)
                       (lt-list-constr-lt-constraints {t = tl} {t′ = tr} {l = lc})
                       (all-tail wcl)
    in
    map-r (eq-rec e) res
  , map (λ where
             (k , eq) →
                 suc k
               , fun-ext λ κ →
                     ap (mapᵏ (map-r (eq-rec e)) ∘ later)
                        (▹-ext λ α → happly (▹-ap (pfix {k = κ} unifyᵏ-body) α) lc)
                   ∙ ap (mapᵏ (map-r (eq-rec e)) ∘ δᵏ) (happly eq κ)
                   ∙ delay-by-mapᵏ res (suc k))
        cnv
unify⇓-body (ctx , ((`` v)      , tr)         ∷ lc) ih wcl | no ne with occurs-dec {v} {t = tr}
unify⇓-body (ctx , ((`` v)      , tr)         ∷ lc) ih wcl | no ne | yes oc =
  inr (occ-fail-l (ne ∘ _⁻¹) oc) , ∣ 0 , refl ∣₁
unify⇓-body (ctx , ((`` v)      , tr)         ∷ lc) ih wcl | no ne | no noc =
  let (res , cnv) = ih (rem v ctx , app-sngL v tr lc)
                       (rem<C {xs = app-sngL v tr lc} {ys = (`` v , tr) ∷ lc}
                              (wf-tm-var (all-head wcl .fst)))
                       (subst (wf-constr-list (rem v ctx))
                              (app-sngL-$↦L ⁻¹) $
                        wf-constr-list-remove (wf-tm-var (all-head wcl .fst))
                                              noc (all-head wcl .snd) (all-tail wcl))
    in
    ⊎.dmap ((v , tr) ∷_) subs-rec-l res
  , map (λ where
             (k , eq) →
                 suc k
               , fun-ext λ κ →
                     ap (mapᵏ (⊎.dmap ((v , tr) ∷_) subs-rec-l) ∘ later)
                        (▹-ext λ α → happly (▹-ap (pfix {k = κ} unifyᵏ-body) α) ((app-sngL v tr lc)))
                   ∙ ap (mapᵏ (⊎.dmap ((v , tr) ∷_) subs-rec-l) ∘ δᵏ) (happly eq κ)
                   ∙ delay-by-mapᵏ res (suc k))
        cnv
-- ugh
unify⇓-body (ctx , ((pl ⟶ ql) , (`` v))     ∷ lc) ih wcl | no ne with occurs-dec {v} {t = pl ⟶ ql}
unify⇓-body (ctx , ((pl ⟶ ql) , (`` v))     ∷ lc) ih wcl | no ne | yes oc =
  inr (occ-fail-r ne oc) , ∣ 0 , refl ∣₁
unify⇓-body (ctx , ((pl ⟶ ql) , (`` v))     ∷ lc) ih wcl | no ne | no noc =
  let (res , cnv) = ih (rem v ctx , app-sngL v (pl ⟶ ql) lc)
                       (rem<C {xs = app-sngL v (pl ⟶ ql) lc} {ys = (pl ⟶ ql , `` v) ∷ lc}
                          (wf-tm-var (all-head wcl .snd)))
                       (subst (wf-constr-list (rem v ctx))
                              (app-sngL-$↦L ⁻¹) $
                        wf-constr-list-remove (wf-tm-var (all-head wcl .snd))
                                              noc (all-head wcl .fst) (all-tail wcl))
    in
    ⊎.dmap ((v , pl ⟶ ql) ∷_) subs-rec-r res
  , map (λ where
             (k , eq) →
                 suc k
               , fun-ext λ κ →
                     ap (mapᵏ (⊎.dmap ((v , pl ⟶ ql) ∷_) subs-rec-r) ∘ later)
                        (▹-ext λ α → happly (▹-ap (pfix {k = κ} unifyᵏ-body) α) ((app-sngL v (pl ⟶ ql) lc)))
                   ∙ ap (mapᵏ (⊎.dmap ((v , pl ⟶ ql) ∷_) subs-rec-r) ∘ δᵏ) (happly eq κ)
                   ∙ delay-by-mapᵏ res (suc k))
        cnv
unify⇓-body (ctx , ((pl ⟶ ql) , (pr ⟶ qr)) ∷ lc) ih wcl | no ne =
  let (res , cnv) = ih (ctx , (pl , pr) ∷ (ql , qr) ∷ lc)
                       (app-lt-constraints {l = pl} {l′ = pr} {r = ql} {r′ = qr} {lc = lc})
                       (  (wf-tm-arr (all-head wcl .fst) .fst , wf-tm-arr (all-head wcl .snd) .fst)
                        ∷ (wf-tm-arr (all-head wcl .fst) .snd , wf-tm-arr (all-head wcl .snd) .snd)
                        ∷ all-tail wcl)
    in
    map-r arrarr-rec res
  , map (λ where
             (k , eq) →
                 suc k
               , fun-ext λ κ →
                     ap (mapᵏ (map-r arrarr-rec) ∘ later)
                        (▹-ext λ α → happly (▹-ap (pfix {k = κ} unifyᵏ-body) α) ((pl , pr) ∷ (ql , qr) ∷ lc))
                   ∙ ap (mapᵏ (map-r arrarr-rec) ∘ δᵏ) (happly eq κ)
                   ∙ delay-by-mapᵏ res (suc k))
        cnv
unify⇓-body (ctx , ((pl ⟶ ql) , con x)       ∷ lc) ih wcl | no ne =
  inr app-con , ∣ 0 , refl ∣₁
-- ugh
unify⇓-body (ctx , (con sl      , (`` v))     ∷ lc) ih wcl | no ne with occurs-dec {v} {t = con sl}
unify⇓-body (ctx , (con sl      , (`` v))     ∷ lc) ih wcl | no ne | yes oc = absurd oc
unify⇓-body (ctx , (con sl      , (`` v))     ∷ lc) ih wcl | no ne | no noc =
  let (res , cnv) = ih (rem v ctx , app-sngL v (con sl) lc)
                       (rem<C {xs = app-sngL v (con sl) lc} {ys = (con sl , `` v) ∷ lc}
                          (wf-tm-var (all-head wcl .snd)))
                       (subst (wf-constr-list (rem v ctx))
                              (app-sngL-$↦L ⁻¹) $
                        wf-constr-list-remove (wf-tm-var (all-head wcl .snd))
                                              noc (all-head wcl .fst) (all-tail wcl))
    in
    ⊎.dmap ((v , con sl) ∷_) subs-rec-r res
  , map (λ where
             (k , eq) →
                 suc k
               , fun-ext λ κ →
                     ap (mapᵏ (⊎.dmap ((v , con sl) ∷_) subs-rec-r) ∘ later)
                        (▹-ext λ α → happly (▹-ap (pfix {k = κ} unifyᵏ-body) α) ((app-sngL v (con sl) lc)))
                   ∙ ap (mapᵏ (⊎.dmap ((v , con sl) ∷_) subs-rec-r) ∘ δᵏ) (happly eq κ)
                   ∙ delay-by-mapᵏ res (suc k))
        cnv
unify⇓-body (ctx , (con sl      , (pr ⟶ qr)) ∷ lc) ih wcl | no ne =
  inr con-app , ∣ 0 , refl ∣₁
unify⇓-body (ctx , (con sl      , con sr)      ∷ lc) ih wcl | no ne =
  inr (con-con-sym (contra (ap con) ne)) , ∣ 0 , refl ∣₁

unify⇓ : {cs : List Constr} → unify cs ⇓
unify⇓ {cs} =
  to-induction
    <C-wf
    (λ q → wf-constr-list (q .fst) (q .snd) → unify (q .snd) ⇓)
    unify⇓-body
    (constr-vars cs , cs)
    (wcl-constr-vars {cs = cs})

-- correctness
