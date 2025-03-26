{-# OPTIONS --safe #-}
module NominalN.Term where

open import Prelude

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Char
open import Data.List
open import Data.Maybe
open import Data.String

open import Order.Strict
open import Order.Constructions.Nat

open import LFSet

open import Id

-- symbols

_==s_ : String → String → Bool
s₁ ==s s₂ = string→list s₁ =? string→list s₂

Sy : 𝒰
Sy = String

-- types

data Term : 𝒰 where
  ``_  : Id → Term
  _⟶_ : Term → Term → Term
  con  : Sy → Term

module Term-code where

  Code : Term → Term → 𝒰
  Code (`` x)      (`` y)     = x ＝ y
  Code (p₁ ⟶ q₁) (p₂ ⟶ q₂) = Code p₁ p₂ × Code q₁ q₂
  Code (con s₁)    (con s₂)   = s₁ ＝ s₂
  Code _           _          = ⊥

  code-refl : (t : Term) → Code t t
  code-refl (`` x)   = refl
  code-refl (p ⟶ q) = code-refl p , code-refl q
  code-refl (con s)   = refl

  encode : ∀ {t₁ t₂} → t₁ ＝ t₂ → Code t₁ t₂
  encode {t₁} e = subst (Code t₁) e (code-refl t₁)

  decode : ∀ {t₁ t₂} → Code t₁ t₂ → t₁ ＝ t₂
  decode {t₁ = `` x}      {t₂ = `` y}      c        = ap ``_ c
  decode {t₁ = p₁ ⟶ q₁} {t₂ = p₂ ⟶ q₂} (c₁ , c₂) = ap² _⟶_ (decode c₁) (decode c₂)
  decode {t₁ = con s₁}    {t₂ = con s₂}    c        = ap con c

``-inj : {x y : ℕ} → `` x ＝ `` y → x ＝ y
``-inj = Term-code.encode

con-inj : ∀ {s₁ s₂} → con s₁ ＝ con s₂ → s₁ ＝ s₂
con-inj = Term-code.encode

⟶-inj : ∀ {p₁ q₁ p₂ q₂} → p₁ ⟶ q₁ ＝ p₂ ⟶ q₂ → (p₁ ＝ p₂) × (q₁ ＝ q₂)
⟶-inj e =
  let (c₁ , c₂) = Term-code.encode e in
  Term-code.decode c₁ , Term-code.decode c₂

``≠⟶ : ∀ {x p q} → `` x ≠ p ⟶ q
``≠⟶ = Term-code.encode

``≠con : ∀ {x s} → `` x ≠ con s
``≠con = Term-code.encode

⟶≠con : ∀ {p q s} → p ⟶ q ≠ con s
⟶≠con = Term-code.encode

_==tm_ : Term → Term → Bool
(`` x)      ==tm (`` y)     = x == y
(p₁ ⟶ q₁) ==tm (p₂ ⟶ q₂) = p₁ ==tm p₂ and q₁ ==tm q₂
(con s₁)    ==tm (con s₂)   = s₁ ==s s₂
_           ==tm _          = false

instance
  tm-eq-reflects : ∀ {x y} → Reflects (x ＝ y) (x ==tm y)
  tm-eq-reflects {x = `` x}      {y = `` y}     =
    Reflects.dmap (ap ``_) (contra ``-inj) Reflects-ℕ-Path
  tm-eq-reflects {x = `` _}      {y = _ ⟶ _}  = ofⁿ ``≠⟶
  tm-eq-reflects {x = `` _}      {y = con s₂}   = ofⁿ ``≠con
  tm-eq-reflects {x = _ ⟶ _}   {y = `` _}     = ofⁿ (``≠⟶ ∘ _⁻¹)
  tm-eq-reflects {x = p₁ ⟶ q₁} {y = p₂ ⟶ q₂} =
    Reflects.dmap
      (λ where (e₁ , e₂) → ap² _⟶_ e₁ e₂)
      (contra ⟶-inj)
      (Reflects-× ⦃ rp = tm-eq-reflects ⦄ ⦃ rq = tm-eq-reflects ⦄)
  tm-eq-reflects {x = _ ⟶ _}   {y = con s₂}   = ofⁿ ⟶≠con
  tm-eq-reflects {x = con s₁}    {y = `` _}     = ofⁿ (``≠con ∘ _⁻¹)
  tm-eq-reflects {x = con s₁}   {y = _ ⟶ _}   = ofⁿ (⟶≠con ∘ _⁻¹)
  tm-eq-reflects {x = con s₁}   {y = con s₂}   =
    Reflects.dmap
        (ap con)
        (contra con-inj)
        (Reflects-String-Path {s₁ = s₁} {s₂ = s₂})

  Term-is-discrete : is-discrete Term
  Term-is-discrete {x} {y} .does = x ==tm y
  Term-is-discrete .proof = tm-eq-reflects

  H-Level-Term : ∀ {n} → H-Level (2 + n) Term
  H-Level-Term = hlevel-basic-instance 2 (is-discrete→is-set auto)
  {-# OVERLAPPING H-Level-Term #-}

is-⟶ : Term → Bool
is-⟶ (p ⟶ q) = true
is-⟶ _        = false

⟶-split : Term → Maybe (Term × Term)
⟶-split (p ⟶ q) = just (p , q)
⟶-split _        = nothing

⟶-split=just : ∀ {t p q}
               → ⟶-split t ＝ just (p , q)
               → t ＝ p ⟶ q
⟶-split=just {t = `` _} e = false! e
⟶-split=just {t = p′ ⟶ q′} e =
  let pqeq = ×-path-inv $ just-inj e in
  ap² _⟶_ (pqeq .fst) (pqeq .snd)
⟶-split=just {t = con _} e = false! e

tm-size : Term → ℕ
tm-size (p ⟶ q) = suc (tm-size p + tm-size q)
tm-size _        = 1

0<tm-size : ∀ {t} → 0 < tm-size t
0<tm-size {t = `` _}    = z<s
0<tm-size {t = _ ⟶ _} = z<s
0<tm-size {t = con s}   = z<s

-- substitution

sub1 : Id → Term → Term → Term
sub1 v t (`` x)    = if v == x then t else `` x
sub1 v t (p ⟶ q) = sub1 v t p ⟶ sub1 v t q
sub1 v t (con s)   = con s

-- vars

vars : Term → LFSet Id
vars (`` x)    = x ∷ []
vars (p ⟶ q) = vars p ∪∷ vars q
vars (con _)   = []

-- syms

syms : Term → LFSet Sy
syms (`` _)    = []
syms (p ⟶ q) = syms p ∪∷ syms q
syms (con s)   = s ∷ []
