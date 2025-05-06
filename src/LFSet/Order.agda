{-# OPTIONS --safe #-}
module LFSet.Order where

open import Cat.Prelude
open import Data.Sum

open import Order.Base
open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet

open import Order.Constructions.Subsets
open import Order.Morphism

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

-- assume discreteness to get rid of erasure (via set-ext)
-- TODO erased version without discreteness?

LFSetₚ : ∀ {ℓ} (A : 𝒰 ℓ) → ⦃ is-discrete A ⦄ → Poset ℓ ℓ
LFSetₚ A .Poset.Ob = LFSet A
LFSetₚ _ .Poset._≤_ = _⊆_
LFSetₚ _ .Poset.≤-thin = hlevel 1
LFSetₚ _ .Poset.≤-refl {x} = Refl-⊆ .refl {x = x}
LFSetₚ _ .Poset.≤-trans {x} = Trans-⊆ ._∙_ {x = x}
LFSetₚ _ .Poset.≤-antisym xy yx = set-ext λ z → prop-extₑ! xy yx

Map : ∀ {ℓ ℓ′} {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
    → ⦃ dA : is-discrete A ⦄ → ⦃ dB : is-discrete B ⦄
    → (A → B)
    → LFSetₚ A ⇒ LFSetₚ B
Map f .hom    = mapₛ f
Map f .pres-≤ = mapₛ-⊆

-- TODO filter etc

-- free semilattice structure

instance
  LFSet-bottom : ∀ {ℓ} {A : 𝒰 ℓ} → ⦃ dA : is-discrete A ⦄
               → Bottom (LFSetₚ A)
  LFSet-bottom .Bottom.bot = []
  LFSet-bottom .Bottom.bot-is-bot _ x∈[] = ⊥.absurd (∉ₛ[] x∈[])

  LFSet-joins : ∀ {ℓ} {A : 𝒰 ℓ} → ⦃ dA : is-discrete A ⦄
              → Has-joins (LFSetₚ A)
  LFSet-joins {x} {y} .Join.lub = x ∪∷ y
  LFSet-joins         .Join.has-join .is-join.l≤join = ∈ₛ-∪∷←l
  LFSet-joins {x}     .Join.has-join .is-join.r≤join = ∈ₛ-∪∷←r {s₁ = x}
  LFSet-joins {x} {y} .Join.has-join .is-join.least z xz yz {x = q} q∈ =
    [ xz , yz ]ᵤ $ ∈ₛ-∪∷→ {xs = x} q∈

  LFSet-meets : ∀ {ℓ} {A : 𝒰 ℓ} → ⦃ dA : is-discrete A ⦄
              → Has-meets (LFSetₚ A)
  LFSet-meets {x} {y} .Meet.glb = x ∩∷ y
  LFSet-meets .Meet.has-meet .is-meet.meet≤l = ∈-∩∷→l
  LFSet-meets .Meet.has-meet .is-meet.meet≤r = ∈-∩∷→r
  LFSet-meets .Meet.has-meet .is-meet.greatest z zx zy q∈ = ∈-∩∷← (zx q∈) (zy q∈)

-- TODO induced join/meet semilattice (when elements form one)

-- mapping to subsets

lf-subset-injᵖ : ∀ {ℓ} {A : 𝒰 ℓ} → ⦃ dA : is-discrete A ⦄
               → LFSetₚ A ⇒ Subsets A ℓ
lf-subset-injᵖ .hom    xs x = el! (x ∈ xs)
lf-subset-injᵖ .pres-≤ x⊆   = x⊆

lf-subset-injᵖ-is-order-embedding : ∀ {ℓ} {A : 𝒰 ℓ} → ⦃ dA : is-discrete A ⦄
                                  → is-order-embedding (LFSetₚ A) (Subsets A ℓ) (lf-subset-injᵖ $_)
lf-subset-injᵖ-is-order-embedding = refl
