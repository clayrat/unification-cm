{-# OPTIONS --safe #-}
module Ribeiro.Ty where

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

data Ty : 𝒰 where
  ``_  : Id → Ty
  _⟶_ : Ty → Ty → Ty
  con  : Ty

module Ty-code where

  Code : Ty → Ty → 𝒰
  Code (`` x)      (`` y)     = x ＝ y
  Code (p₁ ⟶ q₁) (p₂ ⟶ q₂) = Code p₁ p₂ × Code q₁ q₂
  Code con         con        = ⊤
  Code _           _          = ⊥

  code-refl : (t : Ty) → Code t t
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
``-inj = Ty-code.encode

⟶-inj : ∀ {p₁ q₁ p₂ q₂} → p₁ ⟶ q₁ ＝ p₂ ⟶ q₂ → (p₁ ＝ p₂) × (q₁ ＝ q₂)
⟶-inj e =
  let (c₁ , c₂) = Ty-code.encode e in
  Ty-code.decode c₁ , Ty-code.decode c₂

``≠⟶ : ∀ {x p q} → `` x ≠ p ⟶ q
``≠⟶ = Ty-code.encode

``≠con : ∀ {x} → `` x ≠ con
``≠con = Ty-code.encode

⟶≠con : ∀ {p q} → p ⟶ q ≠ con
⟶≠con = Ty-code.encode

_==ty_ : Ty → Ty → Bool
(`` x)      ==ty (`` y)     = x == y
(p₁ ⟶ q₁) ==ty (p₂ ⟶ q₂) = p₁ ==ty p₂ and q₁ ==ty q₂
con         ==ty con        = true
_           ==ty _          = false

ty-eq-reflects : ∀ {x} {y} → Reflects (x ＝ y) (x ==ty y)
ty-eq-reflects {x = `` x}      {y = `` y}     =
  Reflects.dmap (ap ``_) (contra ``-inj) Reflects-ℕ-Path
ty-eq-reflects {x = `` _}      {y = _ ⟶ _}  = ofⁿ ``≠⟶
ty-eq-reflects {x = `` _}      {y = con}      = ofⁿ ``≠con
ty-eq-reflects {x = _ ⟶ _}   {y = `` _}     = ofⁿ (``≠⟶ ∘ _⁻¹)
ty-eq-reflects {x = p₁ ⟶ q₁} {y = p₂ ⟶ q₂} =
  Reflects.dmap
    (λ where (e₁ , e₂) → ap² _⟶_ e₁ e₂)
    (contra ⟶-inj)
    (Reflects-× ⦃ rp = ty-eq-reflects ⦄ ⦃ rq = ty-eq-reflects ⦄)
ty-eq-reflects {x = _ ⟶ _}   {y = con}      = ofⁿ ⟶≠con
ty-eq-reflects {x = con}       {y = `` _}     = ofⁿ (``≠con ∘ _⁻¹)
ty-eq-reflects {x = con}       {y = _ ⟶ _}  = ofⁿ (⟶≠con ∘ _⁻¹)
ty-eq-reflects {x = con}       {y = con}      = ofʸ refl

instance
  Ty-is-discrete : is-discrete Ty
  Ty-is-discrete {x} {y} .does = x ==ty y
  Ty-is-discrete .proof = ty-eq-reflects

  H-Level-Ty : ∀ {n} → H-Level (2 + n) Ty
  H-Level-Ty = hlevel-basic-instance 2 (is-discrete→is-set auto)
  {-# OVERLAPPING H-Level-Ty #-}

ty-size : Ty → ℕ
ty-size (p ⟶ q) = suc (ty-size p + ty-size q)
ty-size _        = 1

0<ty-size : ∀ {t} → 0 < ty-size t
0<ty-size {t = `` _}    = z<s
0<ty-size {t = _ ⟶ _} = z<s
0<ty-size {t = con}     = z<s
