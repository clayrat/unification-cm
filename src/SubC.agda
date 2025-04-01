{-# OPTIONS --safe #-}
module SubC where

open import Prelude
open import Meta.Effect

open import Data.Empty
open import Data.Bool
open import Data.Reflects
open import Data.Dec
open import Data.Maybe
open import Data.List as List
open import Data.List.Correspondences.Unary.Any

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

  -- properties

  keyS : SubC A B → List A
  keyS = map fst

  lup∉ : ⦃ d : is-discrete A ⦄
        → {x : A} {s : SubC A B}
        → x ∉ keyS s → lupS x s ＝ nothing
  lup∉          {s = []}          _   = refl
  lup∉ ⦃ d ⦄ {x} {s = (k , v) ∷ s} x∉ =
    let (x≠k , x∉′) = ¬any-uncons x∉ in
    if-false {b = x =? k} (false→so! ⦃ d .proof ⦄ x≠k) ∙ lup∉ x∉′
