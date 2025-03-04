{-# OPTIONS --safe #-}
module Unfinite where

open import Prelude
open import Meta.Effect

open import Data.Empty hiding (_≠_ ; elim ; rec)
open import Data.Acc.Properties
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Sum as Sum

open import Order.Constructions.Nat

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

private variable
  ℓ : Level
  A : 𝒰 ℓ

record Unfinite {ℓ : Level} (A : 𝒰 ℓ) : 𝒰 ℓ where
  field
    new   : LFSet A → A
    unfin : ∀ {xs} → new xs ∉ xs

open Unfinite public

-- nats are unfinite

unfin-ℕ : Unfinite ℕ
unfin-ℕ .new = suc ∘ joinₛ {js = ℕ-join-slat}
unfin-ℕ .unfin {xs} s∈ =
  <-irr $ <≃suc≤ $
  joinₛ-∈-≤ {js = ℕ-join-slat} s∈

-- sums are unfinite if one side is

unlefts : {B : 𝒰 (level-of-type A)} → LFSet (A ⊎ B) → LFSet B
unlefts = bindₛ [ (λ _ → []) , sng ]ᵤ

unfin-⊎-r : {B : 𝒰 (level-of-type A)} → Unfinite B → Unfinite (A ⊎ B)
unfin-⊎-r ub .new abs = inr (ub .new (unlefts abs))
unfin-⊎-r ub .unfin {xs} r∈ =
  ub .unfin {xs = unlefts xs} $
  ∈-bind r∈ (hereₛ refl)
