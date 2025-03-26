{-# OPTIONS --safe #-}
module NominalN.Cofinite.MM.Naive where

open import Prelude
open import Meta.Effect

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.List as List
open import Data.List.Correspondences.Unary.All
open import Data.List.Operations.Properties
open import Data.List.Operations.Discrete
open import Data.Sum as ⊎
open import Data.Plus
open import Data.AF
open import Data.Acc

open import Order.Constructions.Lex

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

-- main algorithm

unify-type : Constrs → 𝒰
unify-type (ctx , lc) =
  wf-constr-list ctx lc →
  (Σ[ s ꞉ SubC Id Term ]
     (Wf-subst ctx (to-sub s) × Max↦ (unifier lc) (to-sub s)))
  ⊎ UnifyFailure lc

unify-body : (l : Constrs)
           → (ih : (l' : Constrs) → l' <C l → unify-type l')
           → unify-type l
unify-body (ctx , [])                           ih _   =
  inl ( empS
      , subst (Wf-subst ctx) (to-sub-emp ⁻¹) wf-idsub
      , []
      , λ f′ _ → subst (f′ ≤↦_) (to-sub-emp ⁻¹) (≤↦-id {f = f′}))
unify-body (ctx , (tl , tr) ∷ lc)               ih wcl with tl ≟ tr
unify-body (ctx , (tl , tr) ∷ lc) ih wcl | yes e with ih (ctx , lc)
                                                         (lt-list-constr-lt-constraints {t = tl} {t′ = tr} {l = lc})
                                                         (all-tail wcl)
unify-body (ctx , (tl , tr) ∷ lc) ih wcl | yes e | inl (su , wsu , mx) =
  inl (su , wsu , (Max↦≃ (unifier-eq e) (to-sub su) $ mx))
unify-body (ctx , (tl , tr) ∷ lc) ih wcl | yes e | inr uf = inr (eq-rec e uf)
unify-body (ctx , (`` v      , tr)        ∷ lc) ih wcl | no ne with occurs-dec {v} {t = tr}
unify-body (ctx , (`` v      , tr)        ∷ lc) ih wcl | no ne | yes oc = inr (occ-fail-l (ne ∘ _⁻¹) oc)
unify-body (ctx , (`` v      , tr)        ∷ lc) ih wcl | no ne | no noc with ih (rem v ctx , subs1 v tr lc)
                                                                                (rem<C
                                                                                   {xs = subs1 v tr lc} {ys = (`` v , tr) ∷ lc}
                                                                                   (wf-tm-var (all-head wcl .fst)))
                                                                                (subst (wf-constr-list (rem v ctx))
                                                                                       (subs1-$↦L ⁻¹)
                                                                                       (wf-constr-list-remove (wf-tm-var (all-head wcl .fst))
                                                                                                       noc (all-head wcl .snd) (all-tail wcl)))
unify-body (ctx , (`` v      , tr)        ∷ lc) ih wcl | no ne | no noc | inl (su , wsu , mx) =
  inl ( insS v tr su
      , (subst (Wf-subst ctx) (to-sub-ins ⁻¹) $
         wf-sub-◇ {s1 = v ≔ tr}
            (wf-sub-≔
              (wf-tm-var (all-head wcl .fst))
              (occurs-wf-tm (all-head wcl .snd) noc))
            (subst (λ q → Wf-subst q (to-sub su))
                   (  ap (rem v) (minus-[]-r ⁻¹)
                    ∙ minus-∷-r ⁻¹)
                   wsu))
      , (subst (Max↦ (unifier (((`` v) , tr) ∷ lc))) (to-sub-ins ⁻¹) $
         Max↦≃
           (λ f →   ↦𝒫◇-id≃ {p = ↦𝒫× (unifies (`` v) tr) (unifier lc) } f
                  ∙ all-×≃ {P = λ where (x , y) → unifies x y f} ⁻¹)
           (to-sub su ◇ (v ≔ tr)) $
           optimist-lemma {p = unifies (`` v) tr} {q = unifier lc} {a = id↦}
                          {f = v ≔ tr} {g = to-sub su}
              (DCl-unifies {t = tr})
              (Max↦≃ (_⁻¹ ∘ ↦𝒫◇-id≃ {p = unifies (`` v) tr}) (v ≔ tr) $
               max-flex-rigid noc)
              (↦thin-unifier {xs = lc})
              (subst (λ q → Max↦ (↦𝒫◇ (unifier lc) q) (to-sub su))
                     (◇-id-r {s = v ≔ tr} ⁻¹) $
               Max↦≃ (λ s → unifier-append≃) (to-sub su) $
               subst (λ q → Max↦ (unifier q) (to-sub su))
                     subs1-$↦L $
               mx))
       )
unify-body (ctx , (`` v      , tr)        ∷ lc) ih wcl | no ne | no noc | inr uf = inr (subs-rec-l uf)
unify-body (ctx , (pl ⟶ ql , pr ⟶ qr)  ∷ lc) ih wcl | no ne with ih (ctx , (pl , pr) ∷ (ql , qr) ∷ lc)
                                                                       (app-lt-constraints {l = pl} {l′ = pr} {r = ql} {r′ = qr} {lc = lc})
                                                                       (  (wf-tm-arr (all-head wcl .fst) .fst , wf-tm-arr (all-head wcl .snd) .fst)
                                                                        ∷ (wf-tm-arr (all-head wcl .fst) .snd , wf-tm-arr (all-head wcl .snd) .snd)
                                                                        ∷ all-tail wcl)
unify-body (ctx , (pl ⟶ ql , pr ⟶ qr)  ∷ lc) ih wcl | no ne | inl (su , wsu , mx) =
  inl ( su
      , wsu
      , (Max↦≃
           (λ s → (unifier-⟶≃ s) ⁻¹)
           (to-sub su) $
           mx)
      )
unify-body (ctx , (pl ⟶ ql , pr ⟶ qr)  ∷ lc) ih wcl | no ne | inr uf = inr (arrarr-rec uf)
unify-body (ctx , (pl ⟶ ql , con s₂)    ∷ lc) ih wcl | no ne = inr app-con
unify-body (ctx , (con s₁    , pr ⟶ qr) ∷ lc) ih wcl | no ne = inr con-app
unify-body (ctx , (con s₁    , con s₂)    ∷ lc) ih wcl | no ne = inr (con-con-sym (contra (ap con) ne))
unify-body (ctx , (tl        , `` v)      ∷ lc) ih wcl | no ne with occurs-dec {v} {t = tl}
unify-body (ctx , (tl        , `` v)      ∷ lc) ih wcl | no ne | yes oc = inr (occ-fail-r ne oc)
unify-body (ctx , (tl        , `` v)      ∷ lc) ih wcl | no ne | no noc with ih (rem v ctx , subs1 v tl lc)
                                                                                (rem<C
                                                                                   {xs = subs1 v tl lc} {ys = (tl , `` v) ∷ lc}
                                                                                   (wf-tm-var (all-head wcl .snd)))
                                                                                (subst (wf-constr-list (rem v ctx))
                                                                                       (subs1-$↦L ⁻¹)
                                                                                       (wf-constr-list-remove (wf-tm-var (all-head wcl .snd)) noc (all-head wcl .fst) (all-tail wcl)))
unify-body (ctx , (tl        , `` v)      ∷ lc) ih wcl | no ne | no noc | inl (su , wsu , mx) =
  inl ( insS v tl su
      , (subst (Wf-subst ctx) (to-sub-ins ⁻¹) $
         wf-sub-◇ {s1 = v ≔ tl}
            (wf-sub-≔
              (wf-tm-var (all-head wcl .snd))
              (occurs-wf-tm (all-head wcl .fst) noc))
            (subst (λ q → Wf-subst q (to-sub su))
                   (  ap (rem v) (minus-[]-r ⁻¹)
                    ∙ minus-∷-r ⁻¹)
                   wsu))
      , (subst (Max↦ (unifier ((tl , (`` v)) ∷ lc))) (to-sub-ins ⁻¹) $
         Max↦≃
           (λ f →   ↦𝒫◇-id≃ {p = ↦𝒫× (unifies tl (`` v)) (unifier lc) } f
                  ∙ all-×≃ {P = λ where (x , y) → unifies x y f} ⁻¹)
           (to-sub su ◇ (v ≔ tl)) $
           optimist-lemma {p = unifies tl (`` v)} {q = unifier lc} {a = id↦}
                           {f = v ≔ tl} {g = to-sub su}
               (DCl-unifies {s = tl})
               (Max↦≃ (λ s → unifies-swap {t = tl} s ∙ (↦𝒫◇-id≃ {p = unifies tl (`` v)} s) ⁻¹)
                      (v ≔ tl) $
                max-flex-rigid noc)
               (↦thin-unifier {xs = lc})
               (subst (λ q → Max↦ (↦𝒫◇ (unifier lc) q) (to-sub su))
                      (◇-id-r {s = v ≔ tl} ⁻¹) $
                Max↦≃ (λ s → unifier-append≃) (to-sub su) $
                subst (λ q → Max↦ (unifier q) (to-sub su))
                      subs1-$↦L $
                mx))
      )
unify-body (ctx , (tl        , `` v)      ∷ lc) ih wcl | no ne | no noc | inr uf = inr (subs-rec-r uf)

unify : (l : Constrs) → unify-type l
unify = to-induction <C-wf unify-type unify-body

