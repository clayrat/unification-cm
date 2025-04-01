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
open import Data.Vec.Inductive as Vec
open import Data.Vec.Inductive.Correspondences.Unary.All
open import Data.Vec.Inductive.Operations.Properties
open import Data.Sum as ⊎

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

open import Id
open import Ren
open import Ren.Quasi
open import NominalN.Term
open import NominalN.Cofinite.BaseA

-- (idempotent) substitution on sequences

record Subq (n : ℕ) : 𝒰 where
  constructor is-subq
  field
    funq : Id → Vec Term n
    domq : LFSet Id
    cofq : ∀ {x} → x ∉ domq → funq x ＝ replicate n (`` x)

open Subq public

unquoteDecl Subq-Iso = declare-record-iso Subq-Iso (quote Subq)
unquoteDecl H-Level-Subq = declare-record-hlevel 2 H-Level-Subq (quote Subq)

instance
  Funlike-Subq : ∀ {n} → Funlike ur (Subq n) Id (λ _ → Vec Term n)
  Funlike-Subq ._#_ = funq

-- TODO subq-ext

-- a relational definition since the rules aren't structural
data _$q↦_⇒_ : ∀ {n} → Subq n → Vec Term n → Vec Term n → 𝒰 where
  $q-``∈ : ∀ {n x s} {ts : Vec Term n}
          → ts ＝ replicate n (`` x)                 -- TODO unreplicate
          → x ∈ s .domq
          → s $q↦ ts ⇒ (s # x)
  $q-``∉ : ∀ {n x s} {ts : Vec Term n}
          → ts ＝ replicate n (`` x)
          → x ∉ s .domq
          → s $q↦ ts ⇒ ts
  $q-⟶  : ∀ {n s ps qs xs ys} {ts : Vec Term n}
          → uncouple ts ＝ just (ps , qs)
          → s $q↦ ps ⇒ xs
          → s $q↦ qs ⇒ ys
          → s $q↦ ts ⇒ couple xs ys
  $q-def  : ∀ {n s} {ts : Vec Term n}
          → (∀ x → ts ≠ replicate n (`` x))         -- TODO unreplicate
          → uncouple ts ＝ nothing
          → s $q↦ ts ⇒ ts

graphq : ∀ {n} → Subq n → LFSet (Id × Vec Term n)
graphq sq = mapₛ (λ x → x , sq .funq x) (sq .domq)

∈-graphq : ∀ {n} {x : Id} {ts : Vec Term n} {sq : Subq n}
         → (x , ts) ∈ graphq sq
         → x ∈ sq .domq × (sq # x ＝ ts)
∈-graphq {x} {ts} {sq} xt∈ =
  rec!
    (λ z z∈ xte →
        let (xe , te) = ×-path-inv xte in
          subst (_∈ sq .domq) (xe ⁻¹) z∈
        , ap (sq .funq) xe ∙ te ⁻¹)
    (mapₛ-∈ xt∈)

graphq-∈ : ∀ {n} {x : Id} {ts : Vec Term n} {sq : Subq n}
         → x ∈ sq .domq
         → sq # x ＝ ts
         → (x , ts) ∈ graphq sq
graphq-∈ {x} {sq} x∈ sqx =
  subst (λ q → (x , q) ∈ graphq sq) sqx (∈-mapₛ x∈)

codomq : ∀ {n} → Subq n → LFSet (Vec Term n)
codomq sq = mapₛ (sq .funq) (sq .domq)

∈-codom-graph : ∀ {n} {sq : Subq n} {ts : Vec Term n}
               → ts ∈ codomq sq → ∃[ x ꞉ Id ] (x , ts) ∈ graphq sq
∈-codom-graph {sq} ts∈ =
  rec!  -- why not map
    (λ x x∈ tse → ∣ x , graphq-∈ {sq = sq} x∈ (tse ⁻¹) ∣₁)
    (mapₛ-∈ ts∈)

codom-∈ : ∀ {n} {sq : Subq n} {x : Id} {ts : Vec Term n}
        → sq # x ＝ ts
        → x ∈ sq .domq
        → ts ∈ codomq sq
codom-∈ {sq} e x∈ = subst (_∈ₛ codomq sq) e (∈-mapₛ x∈)

