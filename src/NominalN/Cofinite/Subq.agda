{-# OPTIONS --safe #-}
module NominalN.Cofinite.Subq where

open import Prelude
open import Foundations.Sigma
open import Meta.Effect

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat

open import Data.Maybe
open import Data.List as List
open import Data.List.Correspondences.Unary.All
open import Data.List.Operations.Properties
open import Data.Sum as ⊎

open import Order.Constructions.Minmax
open import Order.Constructions.Nat
open import Order.Diagram.Meet
import Order.Diagram.Meet.Reasoning as MR

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

open import Id
open import Ren
open import Ren.Quasi
open import NominalN.Term
open import NominalN.Cofinite.BaseA

-- (idempotent) substitution on sequences

record Subq : 𝒰 where
  constructor is-subq
  field
    funq : Id → List Term
    sizq : ℕ
    domq : LFSet Id
    cohq : ∀ {x} → x ∈ domq → length (funq x) ＝ sizq
    cofq : ∀ {x} → x ∉ domq → funq x ＝ replicate sizq (`` x)

open Subq public

unquoteDecl Subq-Iso = declare-record-iso Subq-Iso (quote Subq)
unquoteDecl H-Level-Subq = declare-record-hlevel 2 H-Level-Subq (quote Subq)

instance
  Funlike-Subq : Funlike ur Subq Id (λ _ → List Term)
  Funlike-Subq ._#_ = funq

-- TODO subq-ext

coh-len : ∀ {s x} → length (s .funq x) ＝ s .sizq
coh-len {s} {x} with x ∈? s .domq
... | yes xi = s .cohq xi
... | no nxi = ap length (s .cofq nxi) ∙ length-replicate

-- a relational definition since the rules
-- aren't structural and are only defined on lists of specific size
data _$q↦_⇒_ : Subq → List Term → List Term → 𝒰 where
  $q-``∈ : ∀ {x s ts}
          → ts ＝ replicate (s .sizq) (`` x)
          → x ∈ s .domq
          → s $q↦ ts ⇒ (s # x)
  $q-``∉ : ∀ {x s ts}
          → ts ＝ replicate (s .sizq) (`` x)
          → x ∉ s .domq
          → s $q↦ ts ⇒ ts
  $q-⟶  : ∀ {s ts ps qs xs ys}
          → length ts ＝ s .sizq         -- TODO redundant?
          → uncouple ts ＝ just (ps , qs)
          → s $q↦ ps ⇒ xs
          → s $q↦ qs ⇒ ys
          → s $q↦ ts ⇒ couple xs ys
  $q-def  : ∀ {s ts}
          → length ts ＝ s .sizq
          → (∀ x → ts ≠ replicate (s .sizq) (`` x))
          → uncouple ts ＝ nothing
          → s $q↦ ts ⇒ ts

open decminmax ℕ-dec-total
open decminmaxprops ℕ-dec-total ℕ-dec-total

$q↦-length : ∀ {sq ts zs}
            → sq $q↦ ts ⇒ zs
            → (length ts ＝ sq .sizq) × (length zs ＝ sq .sizq)
$q↦-length {sq} ($q-``∈ tse x∈) =
  ap length tse ∙ length-replicate , sq .cohq x∈
$q↦-length      ($q-``∉ tse x∉) =
  let e = ap length tse ∙ length-replicate in
  e , e
$q↦-length {ts} ($q-⟶ {xs} le ue pev qev) =
  let (ihp , ihx) = $q↦-length pev
      (ihq , ihy) = $q↦-length qev
    in
  le , zip-with-length ∙ ap² min ihx ihy ∙ MR.∩-idem ℕₚ min-meets -- TODO syntax
$q↦-length      ($q-def le nr un) = le , le

graphq : Subq → LFSet (Id × List Term)
graphq sq = mapₛ (λ x → x , sq .funq x) (sq .domq)

∈-graphq : ∀ {x : Id} {ts : List Term} {sq : Subq}
         → (x , ts) ∈ graphq sq
         → x ∈ sq .domq × (sq # x ＝ ts)
∈-graphq {x} {ts} {sq} xt∈ =
  rec!
    (λ z z∈ xte →
        let (xe , te) = ×-path-inv xte in
          subst (_∈ sq .domq) (xe ⁻¹) z∈
        , ap (sq .funq) xe ∙ te ⁻¹)
    (mapₛ-∈ xt∈)

graphq-∈ : ∀ {x : Id} {ts : List Term} {sq : Subq}
         → x ∈ sq .domq
         → sq # x ＝ ts
         → (x , ts) ∈ graphq sq
graphq-∈ {x} {sq} x∈ sqx =
  subst (λ q → (x , q) ∈ graphq sq) sqx (∈-mapₛ x∈)

codomq : Subq → LFSet (List Term)
codomq sq = mapₛ (sq .funq) (sq .domq)

∈-codom-graph : {sq : Subq} {ts : List Term}
               → ts ∈ codomq sq → ∃[ x ꞉ Id ] (x , ts) ∈ graphq sq
∈-codom-graph {sq} ts∈ =
  rec!  -- why not map
    (λ x x∈ tse → ∣ x , graphq-∈ {sq = sq} x∈ (tse ⁻¹) ∣₁)
    (mapₛ-∈ ts∈)

codom-∈ : {sq : Subq} {x : Id} {ts : List Term}
        → sq # x ＝ ts
        → x ∈ sq .domq
        → ts ∈ codomq sq
codom-∈ {sq} e x∈ = subst (_∈ₛ codomq sq) e (∈-mapₛ x∈)
