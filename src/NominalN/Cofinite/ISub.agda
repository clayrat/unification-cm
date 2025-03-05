{-# OPTIONS --safe #-}
module NominalN.Cofinite.ISub where

open import Prelude
open import Foundations.Sigma
open import Meta.Effect

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Maybe as Maybe

open import Data.List as List
open import Data.List.Correspondences.Unary.All
open import Data.List.Operations.Properties
open import Data.Sum as ⊎

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

open import Id
open import NominalN.Term
open import NominalN.Cofinite.Base
open import NominalN.Cofinite.Sub

-- inverse substitution as a cofinitely quantified map
-- (dom overapproximates the actual domain)

record ISub : 𝒰 where
  constructor is-isub
  field
    ifun : Term → Maybe Id
    idom : LFSet Term
    icof : ∀ {x} → x ∉ idom → ifun x ＝ nothing

open ISub public

unquoteDecl ISub-Iso = declare-record-iso ISub-Iso (quote ISub)
unquoteDecl H-Level-ISub = declare-record-hlevel 2 H-Level-ISub (quote ISub)

instance
  Funlike-ISub : Funlike ur ISub Term (λ _ → Maybe Id)
  Funlike-ISub ._#_ = ifun

isub-ext : {s₁ s₂ : ISub} → s₁ .ifun ＝ s₂ .ifun → s₁ .idom ＝ s₂ .idom → s₁ ＝ s₂
isub-ext {s₁ = is-isub f₁ d₁ c₁} {s₂ = is-isub f₂ d₂ c₂} ef ed =
  ap² (is-isub $²_)
      (×-path ef ed)
      (to-pathᴾ ((∀-is-of-hlevel 1 λ x → Π-is-of-hlevel 1 λ x∉ → hlevel 1) _ c₂))

-- applying
mutual
  _$←_ : ISub → Term → Term
  is $← t = Maybe.rec (is $←r t) ``_ (is .ifun t)

  _$←r_ : ISub → Term → Term
  is $←r (p ⟶ q) = (is $← p) ⟶ (is $← q)
  is $←r t = t

-- empty
empi : ISub
empi .ifun _ = nothing
empi .idom = []
empi .icof _ = refl

inv-sub : Sub → ISub
inv-sub s .ifun t =
  -- build the whole graph and look up the term
  -- TODO pull out filter+graph ?
  map fst (extract1 (filterₛ (λ q → t ==tm q .snd) (graph s)))
inv-sub s .idom = codom s
inv-sub s .icof {x} x∉ =
  ap (mapₘ fst) $
    ap extract1
       (filter-none
          λ where {x = v , t} vx∈ →
                    false→so! ⦃ tm-eq-reflects {x = x} ⦄
                       (contra
                         (λ e → subst (_∈ₛ codom s) (e ⁻¹)
                                      (∈-graph {x = v} {s = s} vx∈ .snd))
                         x∉))
  ∙ extract1-[]

mutual
  empi-$← : ∀ {t} → empi $← t ＝ t
  empi-$← = empi-$←r

  empi-$←r : ∀ {t} → empi $←r t ＝ t
  empi-$←r {t = `` x}    = refl
  empi-$←r {t = p ⟶ q} = ap² _⟶_ (empi-$← {t = p}) (empi-$← {t = q})
  empi-$←r {t = con s}   = refl

inv-empi : inv-sub id↦ ＝ empi
inv-empi =
  isub-ext
    (fun-ext λ t → ap (map fst) (ap extract1 (ap (filterₛ _) mapₛ-[] ∙ filter-[]) ∙ extract1-[]))
    mapₛ-[]

mutual
  inv-$↦-$← : ∀ {t s}
             → Injective (s .fun)
             → (∀ x → x ∈ vars t → x ∈ s .dom → ⊥)
             → s $↦ (inv-sub s $← t) ＝ t
  inv-$↦-$← {t} {s} si vd with t ∈? codom s
  ... | yes t∈ =
     rec!
       (λ z z∈ →
           (ap (λ q → s $↦ Maybe.rec (inv-sub s $←r t) ``_ (map fst q)) $
            ap extract1
               (set-ext λ where
                            (y , w) →
                              prop-extₑ!
                                (λ yw∈ →
                                    let t=w , yw∈′ = filter-∈ₛ yw∈
                                        w=t′ = so→true! t=w ⁻¹
                                      in
                                    hereₛ (×-path
                                             (si (  ∈-graph-= {s = s} yw∈′ ⁻¹
                                                  ∙ w=t′
                                                  ∙ ∈-graph-= {s = s} z∈))
                                             w=t′))
                                (λ yw∈ →
                                    let yw=zt = ∈ₛ∷-∉ yw∈ ∉ₛ[] in
                                    ∈-filterₛ
                                      (true→so! (×-path-inv yw=zt .snd ⁻¹))
                                      (subst (_∈ graph s) (yw=zt ⁻¹) z∈)))
                 ∙ extract1-x∷)
              ∙ ∈-graph-= {s = s} z∈ ⁻¹)
          (∈-codom-graph {s = s} t∈)
  ... | no  t∉ =
      ap (λ q → s $↦ Maybe.rec (inv-sub s $←r t) ``_ (map fst q))
         (ap extract1
             (filter-none (λ where
                               {x = y , w} yw∈ →
                                        false→so! ⦃ tm-eq-reflects {x = t} ⦄
                                           (contra (λ e → ∈-graph {s = s}
                                                              (subst (λ q → (y , q) ∈ graph s)
                                                                     (e ⁻¹) yw∈) .snd) t∉)))
          ∙ extract1-[])
    ∙ inv-$↦-$←r {t = t} {s = s} si vd t∉

  inv-$↦-$←r : ∀ {t s}
              → Injective (s .fun)
              → ((x : Id) → x ∈ vars t → x ∈ s .dom → ⊥)
              → t ∉ codom s
              → s $↦ (inv-sub s $←r t) ＝ t
  inv-$↦-$←r {t = `` x}   {s} si vd t∉ =
    s .cof (vd x (hereₛ refl))
  inv-$↦-$←r {t = p ⟶ q}     si vd t∉ =
    ap² _⟶_
       (inv-$↦-$← {t = p} si λ x → vd x ∘ ∈ₛ-∪∷←l)
       (inv-$↦-$← {t = q} si λ x → vd x ∘ ∈ₛ-∪∷←r {s₁ = vars p})
  inv-$↦-$←r {t = con sy}     si vd t∉ = refl
