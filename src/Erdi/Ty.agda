{-# OPTIONS --safe #-}
module Erdi.Ty where

open import Prelude

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Fin.Inductive

-- vars

-- TODO erasure?
Var : ℕ → 𝒰
Var n = Fin n

-- types

data Ty (n : ℕ) : 𝒰 where
  ``_  : Var n → Ty n
  _⟶_ : Ty n → Ty n → Ty n
  con  : Ty n

module Ty-code where

  Code : ∀ {n} → Ty n → Ty n → 𝒰
  Code (`` x)      (`` y)     = x ＝ y
  Code (p₁ ⟶ q₁) (p₂ ⟶ q₂) = Code p₁ p₂ × Code q₁ q₂
  Code con         con        = ⊤
  Code _           _          = ⊥

  code-refl : ∀ {n} → (t : Ty n) → Code t t
  code-refl (`` x)   = refl
  code-refl (p ⟶ q) = code-refl p , code-refl q
  code-refl con      = tt

  encode : ∀ {n} {t₁ t₂ : Ty n} → t₁ ＝ t₂ → Code t₁ t₂
  encode {t₁} e = subst (Code t₁) e (code-refl t₁)

  decode : ∀ {n} {t₁ t₂ : Ty n} → Code t₁ t₂ → t₁ ＝ t₂
  decode {t₁ = `` x}      {t₂ = `` y}      c        = ap ``_ c
  decode {t₁ = p₁ ⟶ q₁} {t₂ = p₂ ⟶ q₂} (c₁ , c₂) = ap² _⟶_ (decode c₁) (decode c₂)
  decode {t₁ = con}       {t₂ = con}       c        = refl

-- constructor properties

``-inj : ∀ {n} {x y : Fin n}
       → `` x ＝ `` y → x ＝ y
``-inj = Ty-code.encode

⟶-inj : ∀ {n} {p₁ q₁ p₂ q₂ : Ty n}
       → p₁ ⟶ q₁ ＝ p₂ ⟶ q₂ → (p₁ ＝ p₂) × (q₁ ＝ q₂)
⟶-inj e =
  let (c₁ , c₂) = Ty-code.encode e in
  Ty-code.decode c₁ , Ty-code.decode c₂

``≠⟶ : ∀ {n} {x : Fin n} {p q} → `` x ≠ p ⟶ q
``≠⟶ = Ty-code.encode

``≠con : ∀ {n} {x : Fin n} → `` x ≠ con
``≠con = Ty-code.encode

⟶≠con : ∀ {n} {p q : Ty n} → p ⟶ q ≠ con
⟶≠con = Ty-code.encode

-- discreteness

_==ty_ : ∀ {n} → Ty n → Ty n → Bool
(`` x)      ==ty (`` y)     = fin→ℕ x == fin→ℕ y
(p₁ ⟶ q₁) ==ty (p₂ ⟶ q₂) = p₁ ==ty p₂ and q₁ ==ty q₂
con         ==ty con        = true
_           ==ty _          = false

ty-eq-reflects : ∀ {n} {x y : Ty n} → Reflects (x ＝ y) (x ==ty y)
ty-eq-reflects {x = `` x}      {y = `` y}     =
  Reflects.dmap (ap ``_) (contra ``-inj) Reflects-Fin-Path
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
  Ty-is-discrete : ∀ {n} → is-discrete (Ty n)
  Ty-is-discrete {x} {y} .does = x ==ty y
  Ty-is-discrete .proof = ty-eq-reflects

  H-Level-Ty : ∀ {n m} → H-Level (2 + n) (Ty m)
  H-Level-Ty = hlevel-basic-instance 2 (is-discrete→is-set auto)
  {-# OVERLAPPING H-Level-Ty #-}

