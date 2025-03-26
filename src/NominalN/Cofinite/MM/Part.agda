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
open import SubC

open import Id
open import NominalN.Term
open import NominalN.Cofinite.Base
open import NominalN.Cofinite.Sub
open import NominalN.Cofinite.Unifier
open import NominalN.Cofinite.MM

private variable
  κ : Cl

mutual
  unifyᵏ-body : ▹ κ ((lc : List Constr) → gPart κ (SubC Id Term ⊎ UnifyFailure lc))
              → (lc : List Constr) → gPart κ (SubC Id Term ⊎ UnifyFailure lc)
  unifyᵏ-body u▹ []               = now (inl empS)
  unifyᵏ-body u▹ ((tl , tr) ∷ lc) =
    Dec.rec
      (λ e → let ih▹ = u▹ ⊛ next lc in
             later (mapᵏ (map-r (eq-rec e)) ⍉ ih▹))
      (λ ne → unifyᵏ-body-head u▹ tl tr ne lc)
      (tl ≟ tr)

  unifyᵏ-body-head : ▹ κ ((lc : List Constr) → gPart κ (SubC Id Term ⊎ UnifyFailure lc))
                   → (tl tr : Term) → tl ≠ tr
                   → (lc : List Constr) → gPart κ (SubC Id Term ⊎ UnifyFailure ((tl , tr) ∷ lc))
  unifyᵏ-body-head u▹ (`` v)       tr        ne lc =
    Dec.rec
      (λ oc → now (inr (occ-fail-l (ne ∘ _⁻¹) oc)))
      (λ _ → let ih▹ = u▹ ⊛ next (subs1 v tr lc) in
             later (mapᵏ (⊎.dmap (insS v tr) subs-rec-l) ⍉ ih▹))
      (occurs-dec {v} {t = tr})
  unifyᵏ-body-head u▹  tl         (`` v)     ne lc =
    Dec.rec
      (λ oc → now (inr (occ-fail-r ne oc)))
      (λ _ → let ih▹ = u▹ ⊛ next (subs1 v tl lc) in
             later (mapᵏ (⊎.dmap (insS v tl) subs-rec-r) ⍉ ih▹))
      (occurs-dec {v} {t = tl})
  unifyᵏ-body-head u▹ (pl ⟶ ql) (pr ⟶ qr) ne lc =
    let ih▹ = u▹ ⊛ next ((pl , pr) ∷ (ql , qr) ∷ lc) in
    later (mapᵏ (map-r arrarr-rec) ⍉ ih▹)
  unifyᵏ-body-head u▹ (con sl)    (pr ⟶ qr) ne lc = now (inr con-app)
  unifyᵏ-body-head u▹ (pl ⟶ ql) (con sr)    ne lc = now (inr app-con)
  unifyᵏ-body-head u▹ (con sl)    (con sr)   ne lc = now (inr (con-con-sym (contra (ap con) ne)))

unifyᵏ : (lc : List Constr) → gPart κ (SubC Id Term ⊎ UnifyFailure lc)
unifyᵏ = fix unifyᵏ-body

unify : (lc : List Constr) → Part (SubC Id Term ⊎ UnifyFailure lc)
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
unify⇓-body (ctx , []) ih wcl = (inl empS) , ∣ 0 , refl ∣₁
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
  let (res , cnv) = ih (rem v ctx , subs1 v tr lc)
                       (rem<C {xs = subs1 v tr lc} {ys = (`` v , tr) ∷ lc}
                              (wf-tm-var (all-head wcl .fst)))
                       (subst (wf-constr-list (rem v ctx))
                              (subs1-$↦L ⁻¹) $
                        wf-constr-list-remove (wf-tm-var (all-head wcl .fst))
                                              noc (all-head wcl .snd) (all-tail wcl))
    in
    ⊎.dmap (insS v tr) subs-rec-l res
  , map (λ where
             (k , eq) →
                 suc k
               , fun-ext λ κ →
                     ap (mapᵏ (⊎.dmap (insS v tr) subs-rec-l) ∘ later)
                        (▹-ext λ α → happly (▹-ap (pfix {k = κ} unifyᵏ-body) α) ((subs1 v tr lc)))
                   ∙ ap (mapᵏ (⊎.dmap (insS v tr) subs-rec-l) ∘ δᵏ) (happly eq κ)
                   ∙ delay-by-mapᵏ res (suc k))
        cnv
-- ugh
unify⇓-body (ctx , ((pl ⟶ ql) , (`` v))     ∷ lc) ih wcl | no ne with occurs-dec {v} {t = pl ⟶ ql}
unify⇓-body (ctx , ((pl ⟶ ql) , (`` v))     ∷ lc) ih wcl | no ne | yes oc =
  inr (occ-fail-r ne oc) , ∣ 0 , refl ∣₁
unify⇓-body (ctx , ((pl ⟶ ql) , (`` v))     ∷ lc) ih wcl | no ne | no noc =
  let (res , cnv) = ih (rem v ctx , subs1 v (pl ⟶ ql) lc)
                       (rem<C {xs = subs1 v (pl ⟶ ql) lc} {ys = (pl ⟶ ql , `` v) ∷ lc}
                          (wf-tm-var (all-head wcl .snd)))
                       (subst (wf-constr-list (rem v ctx))
                              (subs1-$↦L ⁻¹) $
                        wf-constr-list-remove (wf-tm-var (all-head wcl .snd))
                                              noc (all-head wcl .fst) (all-tail wcl))
    in
    ⊎.dmap (insS v (pl ⟶ ql)) subs-rec-r res
  , map (λ where
             (k , eq) →
                 suc k
               , fun-ext λ κ →
                     ap (mapᵏ (⊎.dmap (insS v (pl ⟶ ql)) subs-rec-r) ∘ later)
                        (▹-ext λ α → happly (▹-ap (pfix {k = κ} unifyᵏ-body) α) (subs1 v (pl ⟶ ql) lc))
                   ∙ ap (mapᵏ (⊎.dmap (insS v (pl ⟶ ql)) subs-rec-r) ∘ δᵏ) (happly eq κ)
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
  let (res , cnv) = ih (rem v ctx , subs1 v (con sl) lc)
                       (rem<C {xs = subs1 v (con sl) lc} {ys = (con sl , `` v) ∷ lc}
                          (wf-tm-var (all-head wcl .snd)))
                       (subst (wf-constr-list (rem v ctx))
                              (subs1-$↦L ⁻¹) $
                        wf-constr-list-remove (wf-tm-var (all-head wcl .snd))
                                              noc (all-head wcl .fst) (all-tail wcl))
    in
    ⊎.dmap (insS v (con sl)) subs-rec-r res
  , map (λ where
             (k , eq) →
                 suc k
               , fun-ext λ κ →
                     ap (mapᵏ (⊎.dmap (insS v (con sl)) subs-rec-r) ∘ later)
                        (▹-ext λ α → happly (▹-ap (pfix {k = κ} unifyᵏ-body) α) ((subs1 v (con sl) lc)))
                   ∙ ap (mapᵏ (⊎.dmap (insS v (con sl)) subs-rec-r) ∘ δᵏ) (happly eq κ)
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

SubT-correct : Varctx → List Constr → SubC Id Term → 𝒰
SubT-correct ctx cs s = Wf-subst ctx (to-sub s) × Max↦ (unifier cs) (to-sub s)

Unify-correct : Varctx → (cs : List Constr) → SubC Id Term ⊎ UnifyFailure cs → 𝒰
Unify-correct ctx cs = [ SubT-correct ctx cs , (λ _ → ⊤) ]ᵤ

unify-correct-body : ▹ κ (   (cs : List Constr)
                           → (ctx : Varctx)
                           → wf-constr-list ctx cs
                           → gAllᵖ κ (Unify-correct ctx cs) (unifyᵏ cs))
                   → (cs : List Constr)
                   → (ctx : Varctx)
                   → wf-constr-list ctx cs
                   → gAllᵖ κ (Unify-correct ctx cs) (unifyᵏ cs)
unify-correct-body     ih▹ []               ctx w =
  gAll-now (  subst (Wf-subst ctx) (to-sub-emp ⁻¹) wf-idsub
            , []
            , (λ f′ _ → subst (f′ ≤↦_) (to-sub-emp ⁻¹) (≤↦-id {f = f′})))
unify-correct-body     ih▹ ((tl , tr) ∷ cs) ctx w with tl ≟ tr
unify-correct-body {κ} ih▹ ((tl , tr) ∷ cs) ctx w | yes e =
  gAll-later λ α →
    all-mapᵏ (λ where
                 {x = inl su} (wsu , mx) →
                   wsu , (Max↦≃ (unifier-eq e) (to-sub su) $ mx)
                 {x = inr _} _ → tt)
             (subst (gAllᵖ κ (Unify-correct ctx cs))
                    (happly (▹-ap (pfix unifyᵏ-body ⁻¹) α) cs)
                    ((ih▹ ⊛ next cs ⊛ next ctx ⊛ next (all-tail w)) α))
unify-correct-body     ih▹ (((`` v)      , tr)         ∷ cs) ctx w | no ne with occurs-dec {v} {t = tr}
unify-correct-body     ih▹ (((`` v)      , tr)         ∷ cs) ctx w | no ne | yes oc = gAll-now tt
unify-correct-body {κ} ih▹ (((`` v)      , tr)         ∷ cs) ctx w | no ne | no noc =
  let w′ = subst (wf-constr-list (rem v ctx))
                 (subs1-$↦L ⁻¹)
                 (wf-constr-list-remove (wf-tm-var (all-head w .fst))
                                 noc (all-head w .snd) (all-tail w))
    in
  gAll-later λ α →
    all-mapᵏ (λ where
                 {x = inl su} (wsu , mx) →
                     (subst (Wf-subst ctx) (to-sub-ins ⁻¹) $
                      wf-sub-◇ {s1 = v ≔ tr}
                         (wf-sub-≔
                           (wf-tm-var (all-head w .fst))
                           (occurs-wf-tm (all-head w .snd) noc))
                         (subst (λ q → Wf-subst q (to-sub su))
                                (  ap (rem v) (minus-[]-r ⁻¹)
                                 ∙ minus-∷-r ⁻¹)
                                wsu))
                   , (subst (Max↦ (unifier (((`` v) , tr) ∷ cs))) (to-sub-ins ⁻¹) $
                      Max↦≃ (λ f →   ↦𝒫◇-id≃ {p = ↦𝒫× (unifies (`` v) tr) (unifier cs) } f
                                    ∙ all-×≃ {P = λ where (x , y) → unifies x y f} ⁻¹)
                             (to-sub su ◇ (v ≔ tr)) $
                             optimist-lemma {p = unifies (`` v) tr} {q = unifier cs} {a = id↦}
                                            {f = v ≔ tr} {g = to-sub su}
                                (DCl-unifies {t = tr})
                                (Max↦≃ (_⁻¹ ∘ ↦𝒫◇-id≃ {p = unifies (`` v) tr}) (v ≔ tr) $
                                 max-flex-rigid noc)
                                (↦thin-unifier {xs = cs})
                                (subst (λ q → Max↦ (↦𝒫◇ (unifier cs) q) (to-sub su))
                                       (◇-id-r {s = v ≔ tr} ⁻¹) $
                                 Max↦≃ (λ s → unifier-append≃) (to-sub su) $
                                 subst (λ q → Max↦ (unifier q) (to-sub su))
                                       subs1-$↦L $
                                 mx))
                 {x = inr _} _ → tt)
             (subst (gAllᵖ κ (Unify-correct (rem v ctx) (subs1 v tr cs)))
                    (happly (▹-ap (pfix unifyᵏ-body ⁻¹) α) (subs1 v tr cs))
                    ((ih▹ ⊛ next (subs1 v tr cs) ⊛ next (rem v ctx) ⊛ next w′) α))
-- ugh
unify-correct-body     ih▹ (((pl ⟶ ql) , (`` v))     ∷ cs) ctx w | no ne with occurs-dec {v} {t = pl ⟶ ql}
unify-correct-body     ih▹ (((pl ⟶ ql) , (`` v))     ∷ cs) ctx w | no ne | yes oc = gAll-now tt
unify-correct-body {κ} ih▹ (((pl ⟶ ql) , (`` v))     ∷ cs) ctx w | no ne | no noc =
  let w′ = subst (wf-constr-list (rem v ctx))
                 (subs1-$↦L ⁻¹)
                 (wf-constr-list-remove (wf-tm-var (all-head w .snd))
                                 noc (all-head w .fst) (all-tail w))
    in
  gAll-later λ α →
    all-mapᵏ (λ where
                 {x = inl su} (wsu , mx) →
                     (subst (Wf-subst ctx) (to-sub-ins ⁻¹) $
                      wf-sub-◇ {s1 = v ≔ (pl ⟶ ql)}
                         (wf-sub-≔
                           (wf-tm-var (all-head w .snd))
                           (occurs-wf-tm (all-head w .fst) noc))
                         (subst (λ q → Wf-subst q (to-sub su))
                                (  ap (rem v) (minus-[]-r ⁻¹)
                                 ∙ minus-∷-r ⁻¹)
                                wsu))
                   , (subst (Max↦ (unifier (((pl ⟶ ql) , (`` v)) ∷ cs))) (to-sub-ins ⁻¹) $
                      Max↦≃ (λ f →   ↦𝒫◇-id≃ {p = ↦𝒫× (unifies (pl ⟶ ql) (`` v)) (unifier cs) } f
                                    ∙ all-×≃ {P = λ where (x , y) → unifies x y f} ⁻¹)
                             (to-sub su ◇ (v ≔ (pl ⟶ ql))) $
                             optimist-lemma {p = unifies (pl ⟶ ql) (`` v)} {q = unifier cs} {a = id↦}
                                             {f = v ≔ (pl ⟶ ql)} {g = to-sub su}
                                 (DCl-unifies {s = (pl ⟶ ql)})
                                 (Max↦≃ (λ s →   unifies-swap {t = (pl ⟶ ql)} s
                                                ∙ (↦𝒫◇-id≃ {p = unifies (pl ⟶ ql) (`` v)} s) ⁻¹)
                                        (v ≔ (pl ⟶ ql)) $
                                  max-flex-rigid noc)
                                 (↦thin-unifier {xs = cs})
                                 (subst (λ q → Max↦ (↦𝒫◇ (unifier cs) q) (to-sub su))
                                        (◇-id-r {s = v ≔ (pl ⟶ ql)} ⁻¹) $
                                  Max↦≃ (λ s → unifier-append≃) (to-sub su) $
                                  subst (λ q → Max↦ (unifier q) (to-sub su))
                                        subs1-$↦L $
                                  mx))
                 {x = inr _} _ → tt)
             (subst (gAllᵖ κ (Unify-correct (rem v ctx) (subs1 v (pl ⟶ ql) cs)))
                    (happly (▹-ap (pfix unifyᵏ-body ⁻¹) α) (subs1 v (pl ⟶ ql) cs))
                    ((ih▹ ⊛ next (subs1 v (pl ⟶ ql) cs) ⊛ next (rem v ctx) ⊛ next w′) α))
unify-correct-body {κ} ih▹ (((pl ⟶ ql) , (pr ⟶ qr)) ∷ cs) ctx w | no ne =
  let w′ = (  (wf-tm-arr (all-head w .fst) .fst , wf-tm-arr (all-head w .snd) .fst)
            ∷ (wf-tm-arr (all-head w .fst) .snd , wf-tm-arr (all-head w .snd) .snd)
            ∷ all-tail w)
    in
  gAll-later λ α →
    all-mapᵏ (λ where
                 {x = inl su} (wsu , mx) →
                     wsu
                   , (Max↦≃ (λ s → (unifier-⟶≃ s) ⁻¹)
                            (to-sub su) $
                             mx)
                 {x = inr _} _ → tt)
             (subst (gAllᵖ κ (Unify-correct ctx ((pl , pr) ∷ (ql , qr) ∷ cs)))
                    (happly (▹-ap (pfix unifyᵏ-body ⁻¹) α) ((pl , pr) ∷ (ql , qr) ∷ cs))
                    ((ih▹ ⊛ next ((pl , pr) ∷ (ql , qr) ∷ cs) ⊛ next ctx ⊛ next w′) α))
unify-correct-body     ih▹ (((pl ⟶ ql) , con sr)     ∷ cs) ctx w | no ne = gAll-now tt
-- ugh
unify-correct-body     ih▹ ((con sl      , (`` v))     ∷ cs) ctx w | no ne with occurs-dec {v} {t = con sl}
unify-correct-body     ih▹ ((con sl      , (`` v))     ∷ cs) ctx w | no ne | yes oc = absurd oc
unify-correct-body {κ} ih▹ ((con sl      , (`` v))     ∷ cs) ctx w | no ne | no noc =
  let w′ = subst (wf-constr-list (rem v ctx))
                 (subs1-$↦L ⁻¹)
                 (wf-constr-list-remove (wf-tm-var (all-head w .snd))
                                 noc (all-head w .fst) (all-tail w))
    in
  gAll-later λ α →
    all-mapᵏ (λ where
                 {x = inl su} (wsu , mx) →
                     (subst (Wf-subst ctx) (to-sub-ins ⁻¹) $
                      wf-sub-◇ {s1 = v ≔ con sl}
                         (wf-sub-≔
                           (wf-tm-var (all-head w .snd))
                           (occurs-wf-tm (all-head w .fst) noc))
                         (subst (λ q → Wf-subst q (to-sub su))
                                (  ap (rem v) (minus-[]-r ⁻¹)
                                 ∙ minus-∷-r ⁻¹)
                                wsu))
                   , (subst (Max↦ (unifier ((con sl , (`` v)) ∷ cs))) (to-sub-ins ⁻¹) $
                      Max↦≃ (λ f →   ↦𝒫◇-id≃ {p = ↦𝒫× (unifies (con sl) (`` v)) (unifier cs) } f
                                    ∙ all-×≃ {P = λ where (x , y) → unifies x y f} ⁻¹)
                             (to-sub su ◇ (v ≔ (con sl))) $
                             optimist-lemma {p = unifies (con sl) (`` v)} {q = unifier cs} {a = id↦}
                                             {f = v ≔ (con sl)} {g = to-sub su}
                                 (DCl-unifies {s = (con sl)})
                                 (Max↦≃ (λ s →   unifies-swap {t = (con sl)} s
                                                ∙ (↦𝒫◇-id≃ {p = unifies (con sl) (`` v)} s) ⁻¹)
                                        (v ≔ (con sl)) $
                                  max-flex-rigid noc)
                                 (↦thin-unifier {xs = cs})
                                 (subst (λ q → Max↦ (↦𝒫◇ (unifier cs) q) (to-sub su))
                                        (◇-id-r {s = v ≔ (con sl)} ⁻¹) $
                                  Max↦≃ (λ s → unifier-append≃) (to-sub su) $
                                  subst (λ q → Max↦ (unifier q) (to-sub su))
                                        subs1-$↦L $
                                  mx))
                 {x = inr _} _ → tt)
             (subst (gAllᵖ κ (Unify-correct (rem v ctx) (subs1 v (con sl) cs)))
                    (happly (▹-ap (pfix unifyᵏ-body ⁻¹) α) (subs1 v (con sl) cs))
                    ((ih▹ ⊛ next (subs1 v (con sl) cs) ⊛ next (rem v ctx) ⊛ next w′) α))
unify-correct-body     ih▹ ((con sl      , (pr ⟶ qr)) ∷ cs) ctx w | no ne = gAll-now tt
unify-correct-body     ih▹ ((con sl      , con sr)     ∷ cs) ctx w | no ne = gAll-now tt

unify-correct : (cs : List Constr) → Allᵖ (Unify-correct (constr-vars cs) cs) (unify cs)
unify-correct cs κ = fix {k = κ} unify-correct-body cs (constr-vars cs) (wcl-constr-vars {cs = cs})
