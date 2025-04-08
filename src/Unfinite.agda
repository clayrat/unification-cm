module Unfinite where

open import Prelude
open import Meta.Effect

open import Data.Empty hiding (_≠_ ; elim ; rec)
open import Data.Acc.Properties
open import Data.Nat
open import Data.Nat.Order.Base renaming (_<_ to _<ℕ_)
open import Data.String
open import Data.String.Properties.Unsafe
open import Data.Sum as Sum

open import Data.List
open import Data.Char

open import Order.Base
open import Order.Strict
open import Order.Total
open import Order.Complemented
open import Order.Diagram.Join

open import Order.Semilattice.Join
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
  joinₛ {js = Strᶜᵖ-join-slat} xs ++ₛ "'"  -- arbitrary
unfin-String .unfin {xs} xs∈ =
  joinₛ-∈-≤ {js = Strᶜᵖ-join-slat} xs∈ $
  subst (ListCharₛ .Order.Strict.StrictPoset._<_ (string→list (joinₛ {js = Strᶜᵖ-join-slat} xs)))
        (string→list-++ₛ {s₁ = joinₛ {js = Strᶜᵖ-join-slat} xs} ⁻¹) $
  List-lex<-++-r {xs = string→list (joinₛ {js = Strᶜᵖ-join-slat} xs)} z<s

{-
unfin-String : Unfinite String
unfin-String .new  xs  =
  joinₛ {js = Str-join-slat} xs ++ₛ "'"  -- arbitrary
unfin-String .unfin {xs} xs∈ =
  Str-≤→≯ {x = joinₛ {js = Str-join-slat} xs ++ₛ "'"} {y = joinₛ {js = Str-join-slat} xs}
    (joinₛ-∈-≤ {js = Str-join-slat} xs∈) $
    subst (ListCharₛ .Order.Strict.StrictPoset._<_ (string→list (joinₛ {js = Str-join-slat} xs)))
          (string→list-++ₛ {s₁ = joinₛ {js = Str-join-slat} xs} ⁻¹) $
    List-lex<-++-r {xs = string→list (joinₛ {js = Str-join-slat} xs)} z<s
-}
-- sums are unfinite if one side is

unlefts : {B : 𝒰 (level-of-type A)} → LFSet (A ⊎ B) → LFSet B
unlefts = bindₛ [ (λ _ → []) , sng ]ᵤ

unfin-⊎-r : {B : 𝒰 (level-of-type A)} → Unfinite B → Unfinite (A ⊎ B)
unfin-⊎-r ub .new abs = inr (ub .new (unlefts abs))
unfin-⊎-r ub .unfin {xs} r∈ =
  ub .unfin {xs = unlefts xs} $
  ∈-bind r∈ (hereₛ refl)

-- TODO we don't need to inherit from Unfinite
-- unfinite + complemented + joins

record UnfiniteJoin {o ℓ : Level} (P : ComplementedPoset o ℓ) : 𝒰 (o ⊔ ℓ) where
  field
    u : Unfinite ⌞ P ⌟
    j : is-join-semilattice (ComplementedPoset.complemented→poset P)
    unfin-join : {xs : LFSet ⌞ P ⌟} → P .ComplementedPoset._<_ (joinₛ {js = j} xs) (new u xs)

open UnfiniteJoin public

unfin-join-ℕ : UnfiniteJoin ℕᶜᵖ
unfin-join-ℕ .u = unfin-ℕ
unfin-join-ℕ .j = ℕ-join-slat
unfin-join-ℕ .unfin-join = <-ascend

unfin-join-String : UnfiniteJoin Strᶜᵖ
unfin-join-String .u = unfin-String
unfin-join-String .j = Strᶜᵖ-join-slat
unfin-join-String .unfin-join {xs} =
  subst (List-lex< (λ x y → char→ℕ x <ℕ char→ℕ y) (string→list (joinₛ {js = Strᶜᵖ-join-slat} xs)))
        (string→list-++ₛ {s₁ = joinₛ {js = Strᶜᵖ-join-slat} xs} ⁻¹)
        (List-lex<-++-r {xs = string→list (joinₛ {js = Strᶜᵖ-join-slat} xs)} z<s)

<-join∉ : {o ℓ : Level} {A : ComplementedPoset o ℓ} {uf : UnfiniteJoin A}
          (open is-join-semilattice (uf .j))
       → ∀ {x} {xs : LFSet ⌞ A ⌟}
       → A .ComplementedPoset._<_ (joinₛ {js = uf .j} xs) x
       → x ∉ xs
<-join∉ {A} {uf} {x} {xs} j<x x∈ =
   ComplementedPoset.≤→≯ A
     (l≤∪ {x = x} {y = joinₛ {js = uf .j} (rem ⦃ ComplementedPoset.has-dec-total-order A .is-decidable-total-order.has-discrete ⦄ x xs)})
     (subst (λ q → A .ComplementedPoset._<_ q x) joinₛ-∷ $
      subst (λ q → A .ComplementedPoset._<_ (joinₛ {js = uf .j} q) x)
            (rem-∈-eq ⦃ d = ComplementedPoset.has-dec-total-order A .is-decidable-total-order.has-discrete ⦄ x∈ ⁻¹)
      j<x)
  where
  open is-join-semilattice (uf .j)

new1< : {o ℓ : Level} {A : ComplementedPoset o ℓ} {uf : UnfiniteJoin A}
      → ∀ {x} {xs : LFSet ⌞ A ⌟}
      → A .ComplementedPoset._<_ (joinₛ {js = uf .j} xs) x
      → A .ComplementedPoset._<_ (joinₛ {js = uf .j} (x ∷ xs)) (new1 (uf .u) x)
new1< {A} {uf} {x} x< =
  subst (λ q → A .ComplementedPoset._<_ q (new1 (uf .u) x))
         (joinₛ-∷ ⁻¹)
         (ComplementedPoset.≤-<-trans A
           (∪≃≤× ⁻¹ $ (A .ComplementedPoset.≤-refl) , ComplementedPoset.<→≤ A x<)
            (subst (λ q → A .ComplementedPoset._<_ q (new1 (uf .u) x))
                   joinₛ-sng
                   (unfin-join uf {xs = sng x})))
  where
  open is-join-semilattice (uf .j)

{-
new1∉ : {o ℓ : Level} {A : ComplementedPoset o ℓ} {uf : UnfiniteJoin A}
      → ∀ {x} {xs : LFSet ⌞ A ⌟}
      → A .ComplementedPoset._<_ (joinₛ {js = uf .j} xs) x
      → new1 (uf .u) x ∉ (x ∷ xs)
new1∉ {A} {uf} {x} x< =
  ∉ₛ-∷
    (λ e → unfin (uf .u) (subst (_∈ₛ sng x) (e ⁻¹) (hereₛ refl)))
    (<-join∉ {uf = uf}
        (A .ComplementedPoset.<-trans x<
            (subst (λ q → A .ComplementedPoset._<_ q (new1 (uf .u) x))
                   joinₛ-sng
                   (unfin-join uf {xs = sng x}))))
  where
  open is-join-semilattice (uf .j)
-}
