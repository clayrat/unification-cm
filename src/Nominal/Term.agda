{-# OPTIONS --safe #-}
module Nominal.Term where

open import Prelude

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base

open import Order.Strict
open import Order.Constructions.Nat

-- ids

Id : 𝒰
Id = ℕ

Idₛ : StrictPoset 0ℓ 0ℓ
Idₛ = ℕₛ

-- types

data Term : 𝒰 where
  ``_  : Id → Term
  _⟶_ : Term → Term → Term
  con  : Term

module Term-code where

  Code : Term → Term → 𝒰
  Code (`` x)      (`` y)     = x ＝ y
  Code (p₁ ⟶ q₁) (p₂ ⟶ q₂) = Code p₁ p₂ × Code q₁ q₂
  Code con         con        = ⊤
  Code _           _          = ⊥

  code-refl : (t : Term) → Code t t
  code-refl (`` x)   = refl
  code-refl (p ⟶ q) = code-refl p , code-refl q
  code-refl con      = tt

  encode : ∀ {t₁ t₂} → t₁ ＝ t₂ → Code t₁ t₂
  encode {t₁} e = subst (Code t₁) e (code-refl t₁)

  decode : ∀ {t₁ t₂} → Code t₁ t₂ → t₁ ＝ t₂
  decode {t₁ = `` x}      {t₂ = `` y}      c        = ap ``_ c
  decode {t₁ = p₁ ⟶ q₁} {t₂ = p₂ ⟶ q₂} (c₁ , c₂) = ap² _⟶_ (decode c₁) (decode c₂)
  decode {t₁ = con}       {t₂ = con}       c        = refl

``-inj : {x y : ℕ} → `` x ＝ `` y → x ＝ y
``-inj = Term-code.encode

⟶-inj : ∀ {p₁ q₁ p₂ q₂} → p₁ ⟶ q₁ ＝ p₂ ⟶ q₂ → (p₁ ＝ p₂) × (q₁ ＝ q₂)
⟶-inj e =
  let (c₁ , c₂) = Term-code.encode e in
  Term-code.decode c₁ , Term-code.decode c₂

``≠⟶ : ∀ {x p q} → `` x ≠ p ⟶ q
``≠⟶ = Term-code.encode

``≠con : ∀ {x} → `` x ≠ con
``≠con = Term-code.encode

⟶≠con : ∀ {p q} → p ⟶ q ≠ con
⟶≠con = Term-code.encode

_==tm_ : Term → Term → Bool
(`` x)      ==tm (`` y)     = x == y
(p₁ ⟶ q₁) ==tm (p₂ ⟶ q₂) = p₁ ==tm p₂ and q₁ ==tm q₂
con         ==tm con        = true
_           ==tm _          = false

instance
  tm-eq-reflects : ∀ {x y} → Reflects (x ＝ y) (x ==tm y)
  tm-eq-reflects {x = `` x}      {y = `` y}     =
    Reflects.dmap (ap ``_) (contra ``-inj) Reflects-ℕ-Path
  tm-eq-reflects {x = `` _}      {y = _ ⟶ _}  = ofⁿ ``≠⟶
  tm-eq-reflects {x = `` _}      {y = con}      = ofⁿ ``≠con
  tm-eq-reflects {x = _ ⟶ _}   {y = `` _}     = ofⁿ (``≠⟶ ∘ _⁻¹)
  tm-eq-reflects {x = p₁ ⟶ q₁} {y = p₂ ⟶ q₂} =
    Reflects.dmap
      (λ where (e₁ , e₂) → ap² _⟶_ e₁ e₂)
      (contra ⟶-inj)
      (Reflects-× ⦃ rp = tm-eq-reflects ⦄ ⦃ rq = tm-eq-reflects ⦄)
  tm-eq-reflects {x = _ ⟶ _}   {y = con}      = ofⁿ ⟶≠con
  tm-eq-reflects {x = con}       {y = `` _}     = ofⁿ (``≠con ∘ _⁻¹)
  tm-eq-reflects {x = con}       {y = _ ⟶ _}  = ofⁿ (⟶≠con ∘ _⁻¹)
  tm-eq-reflects {x = con}       {y = con}      = ofʸ refl

  Term-is-discrete : is-discrete Term
  Term-is-discrete {x} {y} .does = x ==tm y
  Term-is-discrete .proof = tm-eq-reflects

  H-Level-Term : ∀ {n} → H-Level (2 + n) Term
  H-Level-Term = hlevel-basic-instance 2 (is-discrete→is-set auto)
  {-# OVERLAPPING H-Level-Term #-}

tm-size : Term → ℕ
tm-size (p ⟶ q) = suc (tm-size p + tm-size q)
tm-size _        = 1

0<tm-size : ∀ {t} → 0 < tm-size t
0<tm-size {t = `` _}    = z<s
0<tm-size {t = _ ⟶ _} = z<s
0<tm-size {t = con}     = z<s
