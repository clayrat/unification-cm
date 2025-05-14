{-# OPTIONS --safe #-}
module LFSet.Order where

open import Cat.Prelude
open import Meta.Effect
open import Logic.Decidability

open import Data.Empty
open import Data.Bool
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Sum
open import Data.Acc

open import Order.Base
open import Order.Strict
open import Order.Diagram.Bottom
open import Order.Diagram.Join
open import Order.Diagram.Meet

open import Order.Constructions.Nat
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

MapLFS : ∀ {ℓ ℓ′} {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
    → ⦃ dA : is-discrete A ⦄ → ⦃ dB : is-discrete B ⦄
    → (A → B)
    → LFSetₚ A ⇒ LFSetₚ B
MapLFS f .hom    = mapₛ f
MapLFS f .pres-≤ = mapₛ-⊆

SizeLFS : ∀ {ℓ} {A : 𝒰 ℓ} → ⦃ dA : is-discrete A ⦄
        → LFSetₚ A ⇒ ℕₚ
SizeLFS .hom    = sizeₛ
SizeLFS .pres-≤ = size-⊆

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

-- strict

LFSet< : ∀ {ℓ} {A : 𝒰 ℓ}
       → LFSet A → LFSet A → 𝒰 ℓ
LFSet< {A} s t = (s ⊆ t) × (∃[ x ꞉ A ] x ∉ s × x ∈ t)

¬LFSet<[] : ∀ {ℓ} {A : 𝒰 ℓ} {x : LFSet A}
          → ¬ LFSet< x []
¬LFSet<[] (_ , nx) = rec! (λ a _ → ∉ₛ[]) nx

LFSet<-thin : ∀ {ℓ} {A : 𝒰 ℓ} {x y : LFSet A}
            → is-prop (LFSet< x y)
LFSet<-thin = hlevel!

LFSet<-irrefl : ∀ {ℓ} {A : 𝒰 ℓ} {x y : LFSet A}
              → ¬ (LFSet< x x)
LFSet<-irrefl (_ , ne) = rec! (λ a a∉ → a∉) ne

LFSet<-trans : ∀ {ℓ} {A : 𝒰 ℓ} {x y z : LFSet A}
             → LFSet< x y → LFSet< y z → LFSet< x z
LFSet<-trans {x} (sxy , nxy) (syz , nyz) =
    Trans-⊆ ._∙_ {x = x} sxy syz
  , map²
      (λ where _ (b , b∉y , b∈z) → b , contra sxy b∉y , b∈z)
      nxy nyz

LFSet<-dec : ∀ {ℓ} {A : 𝒰 ℓ}
           → ⦃ da : is-discrete A ⦄
           → {xs ys : LFSet A}
           → Dec (LFSet< xs ys)
LFSet<-dec {xs} {ys} =
  Dec-× ⦃ da = Dec-⊆ₛ ⦄
        ⦃ db = ≃→dec (∥-∥₁.ae $ Σ-ap-snd λ x → ×-swap) (Dec-anyₛ λ x → Dec-¬) ⦄

LFSet<-size : ∀ {ℓ} {A : 𝒰 ℓ}
            → ⦃ da : is-discrete A ⦄
            → {x y : LFSet A}
            → LFSet< x y → sizeₛ x < sizeₛ y
LFSet<-size (sxy , nxy) =
  rec! (λ a a∉x a∈y →
         [ (λ lt → lt)
         , (λ e → absurd (a∉x (size-≥-⊆ sxy e a∈y)))
         ]ᵤ (≤≃<⊎= $ size-⊆ sxy)
       )
       nxy

LFSet<-wf : ∀ {ℓ} {A : 𝒰 ℓ}
          → ⦃ is-discrete A ⦄       -- TODO can we get rid of discreteness?
          → is-wf (LFSet< {A = A})
LFSet<-wf = wf-map (λ x y → LFSet<-size) $ wf-lift sizeₛ <-is-wf
