{-# OPTIONS --safe #-}
module Id where

open import Prelude

open import Data.Nat
open import Data.Nat.Order.Base

open import Order.Strict
open import Order.Constructions.Nat

-- ids

Id : 𝒰
Id = ℕ

Idₛ : StrictPoset 0ℓ 0ℓ
Idₛ = ℕₛ
