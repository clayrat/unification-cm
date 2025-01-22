{-# OPTIONS --safe #-}
module NominalA.Term where

open import Prelude

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.List
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Char
open import Data.String

open import Order.Strict
open import Order.Constructions.Minmax
open import Order.Constructions.Nat

-- ids

Id : 𝒰
Id = ℕ

Idₛ : StrictPoset 0ℓ 0ℓ
Idₛ = ℕₛ

-- symbols

Sy : 𝒰
Sy = String

-- terms

data Term : 𝒰 where
  ``_  : Id → Term
  con  : Sy → List Term → Term

module Term-code where

  mutual
    Code : Term → Term → 𝒰
    Code (`` x)       (`` y)       = x ＝ y
    Code (con s₁ ts₁) (con s₂ ts₂) = (s₁ ＝ s₂) × Codes ts₁ ts₂
    Code _            _            = ⊥

    Codes : List Term → List Term → 𝒰
    Codes []       []       = ⊤
    Codes (x ∷ xs) (y ∷ ys) = Code x y × Codes xs ys
    Codes _        _        = ⊥

  mutual
    code-refl : (t : Term) → Code t t
    code-refl (`` x)     = refl
    code-refl (con s ts) = refl , codes-refl ts

    codes-refl : (ts : List Term) → Codes ts ts
    codes-refl []       = tt
    codes-refl (t ∷ ts) = code-refl t , codes-refl ts

  encode : ∀ {t₁ t₂} → t₁ ＝ t₂ → Code t₁ t₂
  encode {t₁} e = subst (Code t₁) e (code-refl t₁)

  mutual
    decode : ∀ {t₁ t₂} → Code t₁ t₂ → t₁ ＝ t₂
    decode {t₁ = `` x}       {t₂ = `` y}       c         = ap ``_ c
    decode {t₁ = con s₁ ts₁} {t₂ = con s₂ ts₂} (cs , ct) = ap² con cs (decodes ct)

    decodes : ∀ {ts₁ ts₂} → Codes ts₁ ts₂ → ts₁ ＝ ts₂
    decodes {ts₁ = []}       {ts₂ = []}       c        = refl
    decodes {ts₁ = t₁ ∷ ts₁} {ts₂ = t₂ ∷ ts₂} (c , cs) = ap² _∷_ (decode c) (decodes cs)

``-inj : {x y : ℕ} → `` x ＝ `` y → x ＝ y
``-inj = Term-code.encode

con-inj : ∀ {s₁ s₂ ts₁ ts₂} → con s₁ ts₁ ＝ con s₂ ts₂ → (s₁ ＝ s₂) × (ts₁ ＝ ts₂)
con-inj e =
  let (c₁ , c₂) = Term-code.encode e in
  c₁ , Term-code.decodes c₂

``≠con : ∀ {x s ts} → `` x ≠ con s ts
``≠con = Term-code.encode

mutual
  _==t_ : Term → Term → Bool
  (`` x)       ==t (`` y)       = x == y
  (con s₁ ts₁) ==t (con s₂ ts₂) = (string→list s₁ =? string→list s₂) and (ts₁ ==ts ts₂)
  _            ==t _            = false

  _==ts_ : List Term → List Term → Bool
  [] ==ts [] = true
  (x ∷ xs) ==ts (y ∷ ys) = (x ==t y) and (xs ==ts ys)
  _ ==ts _ = false

instance
  mutual
    tm-eq-reflects : ∀ {x y} → Reflects (x ＝ y) (x ==t y)
    tm-eq-reflects {x = `` x}       {y = `` y}       =
      Reflects.dmap (ap ``_) (contra ``-inj) Reflects-ℕ-Path
    tm-eq-reflects {x = `` x}       {y = con s₂ ts₂} = ofⁿ ``≠con
    tm-eq-reflects {x = con s₁ ts₁} {y = `` y}       = ofⁿ (``≠con ∘ _⁻¹)
    tm-eq-reflects {x = con s₁ ts₁} {y = con s₂ ts₂} =
      Reflects.dmap
        (λ where (e , es) → ap² con e es)
        (contra con-inj)
        (Reflects-× ⦃ rp = Reflects-String-Path {s₁ = s₁} {s₂ = s₂} ⦄ ⦃ rq = tms-eq-reflects {xs = ts₁} {ys = ts₂} ⦄)

    tms-eq-reflects : ∀ {xs ys} → Reflects (xs ＝ ys) (xs ==ts ys)
    tms-eq-reflects {xs = []}     {ys = []}     = ofʸ refl
    tms-eq-reflects {xs = []}     {ys = x ∷ ys} = ofⁿ (false! ⦃ Reflects-[]≠∷ ⦄)
    tms-eq-reflects {xs = x ∷ xs} {ys = []}     = ofⁿ (false! ⦃ Reflects-∷≠[] ⦄)
    tms-eq-reflects {xs = x ∷ xs} {ys = y ∷ ys} =
      Reflects.dmap
        (λ where (e , es) → ap² _∷_ e es)
        (contra (λ e → (∷-head-inj e) , (∷-tail-inj e)) )
        (Reflects-× ⦃ rp = tm-eq-reflects {x = x} {y = y} ⦄ ⦃ rq = tms-eq-reflects {xs = xs} {ys = ys} ⦄)

  Term-is-discrete : is-discrete Term
  Term-is-discrete {x} {y} .does = x ==t y
  Term-is-discrete .proof = tm-eq-reflects

  H-Level-Term : ∀ {n} → H-Level (2 + n) Term
  H-Level-Term = hlevel-basic-instance 2 (is-discrete→is-set auto)
  {-# OVERLAPPING H-Level-Term #-}

-- arity

Arity : 𝒰
Arity = Sy → ℕ

-- size & height

mutual
  term-size : Term → ℕ
  term-size (`` x)     = 1   -- Ostvold has 0, but we need 1 for termination
  term-size (con s ts) = 1 + terms-size ts

  terms-size : List Term → ℕ
  terms-size [] = 0
  terms-size (t ∷ ts) = term-size t + terms-size ts

open decminmax ℕ-dec-total
mutual
  term-height : Term → ℕ
  term-height (`` x)     = 1   -- 0?
  term-height (con s ts) = 1 + terms-height ts

  terms-height : List Term → ℕ
  terms-height [] = 0
  terms-height (t ∷ ts) = max (term-height t) (terms-height ts)

0<ty-size : ∀ {t} → 0 < term-size t
0<ty-size {t = `` _}     = z<s
0<ty-size {t = con s ts} = z<s
