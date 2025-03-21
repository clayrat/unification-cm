module Unfinite where

open import Prelude
open import Meta.Effect

open import Data.Empty hiding (_≠_ ; elim ; rec)
open import Data.Acc.Properties
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.String
open import Data.String.Properties.Unsafe
open import Data.Sum as Sum

open import Order.Strict
open import Order.Constructions.Nat
open import Order.Constructions.Lex
open import Order.Constructions.String

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

private variable
  ℓ : Level
  A : 𝒰 ℓ

-- TODO instance record

record Unfinite {ℓ : Level} (A : 𝒰 ℓ) : 𝒰 ℓ where
  field
    new   : LFSet A → A
    unfin : ∀ {xs} → new xs ∉ xs

open Unfinite public

new1 : Unfinite A → A → A
new1 uf = uf .new ∘ sng

-- nats are unfinite

unfin-ℕ : Unfinite ℕ
unfin-ℕ .new = suc ∘ joinₛ {js = ℕ-join-slat}
unfin-ℕ .unfin {xs} s∈ =
  <-irr $ <≃suc≤ $
  joinₛ-∈-≤ {js = ℕ-join-slat} s∈

-- strings are unfinite

unfin-String : Unfinite String
unfin-String .new  xs  =
  joinₛ {js = Str-join-slat} xs ++ₛ "'"  -- arbitrary
unfin-String .unfin {xs} xs∈ =
  Str-≤→≯ {x = joinₛ {js = Str-join-slat} xs ++ₛ "'"} {y = joinₛ {js = Str-join-slat} xs}
    (joinₛ-∈-≤ {js = Str-join-slat} xs∈) $
    subst (ListCharₛ .Order.Strict.StrictPoset._<_ (string→list (joinₛ {js = Str-join-slat} xs)))
          (string→list-++ₛ {s₁ = joinₛ {js = Str-join-slat} xs} ⁻¹) $
    List-lex<-++-r {xs = string→list (joinₛ {js = Str-join-slat} xs)} z<s

-- sums are unfinite if one side is

unlefts : {B : 𝒰 (level-of-type A)} → LFSet (A ⊎ B) → LFSet B
unlefts = bindₛ [ (λ _ → []) , sng ]ᵤ

unfin-⊎-r : {B : 𝒰 (level-of-type A)} → Unfinite B → Unfinite (A ⊎ B)
unfin-⊎-r ub .new abs = inr (ub .new (unlefts abs))
unfin-⊎-r ub .unfin {xs} r∈ =
  ub .unfin {xs = unlefts xs} $
  ∈-bind r∈ (hereₛ refl)
