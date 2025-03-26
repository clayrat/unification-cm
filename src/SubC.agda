{-# OPTIONS --safe #-}
module SubC where

open import Prelude
open import Meta.Effect

open import Data.Bool
open import Data.Maybe
open import Data.List as List

private variable
  ℓᵃ ℓᵇ ℓᶜ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ

-- computational (aka triangular) substitution

opaque
  SubC : 𝒰 → 𝒰 → 𝒰
  SubC A B = List (A × B)

  empS : SubC A B
  empS = []

  lupS : ⦃ is-discrete A ⦄ → A → SubC A B → Maybe B
  lupS a [] = nothing
  lupS a ((x , b) ∷ s) = if a =? x then just b else lupS a s

  insS : A → B → SubC A B → SubC A B
  insS a b = (a , b) ∷_

  invS : SubC A B → SubC B A
  invS = map (λ where (a , b) → (b , a))
