{-# OPTIONS --guarded #-}
module NominalN.Cofinite.AU.Part where

open import Prelude
open import Meta.Effect
open import Meta.Effect.Traversable

open import Data.Acc
open import Data.Empty
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.String
open import Data.Maybe as Maybe
open import Data.List as List
open import Data.List.Correspondences.Unary.All
open import Data.Truncation.Propositional.Instances.Idiom
open import Data.Vec.Inductive as Vec
open import Data.Vec.Inductive.Operations

open import Order.Constructions.Minmax
open import Order.Constructions.Nat

open import Later
open import Clocked.Partial
open import Clocked.Partial.Converges
open import Clocked.Partial.All

open import LFSet
open import LFSet.Membership
open import Unfinite
open import State
open import SubC

open import Id
open import NominalN.Term
open import NominalN.Cofinite.BaseA
open import NominalN.Cofinite.Subq
open import NominalN.Cofinite.ISubq
open import NominalN.Cofinite.AU

private variable
  ℓᵃ ℓᵇ ℓᶜ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ
  κ : Cl

opaque
  unfolding SubC
  to-isubq : ∀ {n} → SubC (Vec Term n) Id → ISubq n
  to-isubq s .ifunq ts = lupS ts s
  to-isubq s .idomq = from-list (keyS s)
  to-isubq s .icofq ts∉ = lup∉ {s = s} (contra ∈-list ts∉)

AUTy : ℕ → 𝒰
AUTy n = State (Id × SubC (Vec Term n) Id) Term

au-θ-miss : ∀ {n} → Vec Term n → AUTy n
au-θ-miss ts =
  do s ← st-gets snd
     Maybe.rec
       (map ``_ (gen unfin-ℕ ts))
       (λ x → pure (`` x))
       (lupS ts s)

au-⟶ : ∀ {n} → AUTy n → AUTy n → AUTy n
au-⟶ p q =
  do p′ ← p
     q′ ← q
     pure (p′ ⟶ q′)

au-θᵏ-body : ∀ {n}
           → ▹ κ (Vec Term n → gPart κ (AUTy n))
           → Vec Term n → gPart κ (AUTy n)
au-θᵏ-body a▹ ts =
  Maybe.rec
    (Maybe.rec
       (now (au-θ-miss ts))
       (λ where (ps , qs) →
                  later (map²ᵏ au-⟶
                         ⍉ (a▹ ⊛ next ps)
                         ⊛ (a▹ ⊛ next qs)))
       (uncouple ts))
    (now ∘ pure)
    (unreplicate ts)

au-θᵏ : ∀ {n} → Vec Term n → gPart κ (AUTy n)
au-θᵏ = fix au-θᵏ-body

au-θ : ∀ {n} → Vec Term n → Part (AUTy n)
au-θ ts κ = au-θᵏ ts

au : List Term → Maybe (Part Term)
au []         = nothing
au ts@(_ ∷ _) =
  let (n , tsv , ne) = list→vec ts
      vs = bindₛ vars (from-vec tsv)
      (ts′ , s) = pre-process tsv
      is = invS s
    in
  just $
  mapᵖ (λ st → let s = evalState st ((new unfin-ℕ vs) , empS) in
               post-process s is)
       (au-θ ts′)

-- termination

open decminmax ℕ-dec-total
open decminmaxprops ℕ-dec-total ℕ-dec-total

au-θ⇓-body : ∀ {n} → 0 < n
           → ∀ ts
           → (∀ ts' → tm-sizes ts' < tm-sizes ts → au-θ ts' ⇓)
           → au-θ ts ⇓
au-θ⇓-body lt ts ih with unreplicate ts | recall unreplicate ts
au-θ⇓-body lt ts ih | just t  | _       = pure t , ∣ 0 , refl ∣₁
au-θ⇓-body lt ts ih | nothing | ⟪ eqa ⟫ with uncouple ts | recall uncouple ts
au-θ⇓-body lt ts ih | nothing | ⟪ eqa ⟫ | just (ps , qs) | ⟪ equ ⟫ =
  let (l< , r<) = uncouple-sizes>0 {ts = ts} lt equ
      (resp , cnvp) = ih ps l<
      (resq , cnvq) = ih qs r<
    in
    au-⟶ resp resq
  , map²
      (λ (kp , kpeq) (kq , kqeq) →
            1 + max kp kq
          , fun-ext λ κ →
              ap later (▹-ext λ α →
                               let ihe = ▹-ap (pfix {k = κ} (au-θᵏ-body)) α in
                                  ap² (map²ᵏ au-⟶)
                                      (happly ihe ps ∙ happly kpeq κ)
                                      (happly ihe qs ∙ happly kqeq κ)
                                ∙ delay-by-map²ᵏ au-⟶ kp resp kq resq))
      cnvp cnvq
au-θ⇓-body lt ts ih | nothing | ⟪ eqa ⟫ | nothing        | _       =
  au-θ-miss ts , ∣ 0 , refl ∣₁

au-θ⇓ : ∀ {n} → 0 < n
      → ∀ {ts} → au-θ ts ⇓
au-θ⇓ lt {ts} =
  to-induction
    (wf-lift tm-sizes <-is-wf)
    (λ zs → au-θ zs ⇓)
    (au-θ⇓-body lt)
    ts

au⇓ : ∀ {ts} → Maybe.rec ⊤ _⇓ (au ts)
au⇓ {ts = []}    = tt
au⇓ {ts = t ∷ ts} =
  let (n , tsv , ne) = list→vec (t ∷ ts)
      vs = bindₛ vars (from-vec tsv)
      (ts′ , s) = pre-process tsv
      is = invS s
      (r , r⇓) = au-θ⇓ z<s {ts = ts′}
     in
     post-process (evalState r (new unfin-ℕ vs , empS)) is
   , map⇓ (λ st → post-process (evalState st (new unfin-ℕ vs , empS)) is) r⇓

{-
-- correctness


st-inv : {t : Term} {ts : List Term} {σ τ : SubC (List Term) Id}
         {x y : Id}
       → AUTy → 𝒰
st-inv st = {!!}

au-θᵏ-inv-body : ▹ κ (   (t : Term)
                       → (ts : List Term)
                       → (σ τ : SubC (List Term) Id)
                       → (x y : Id)
                       → gAllᵖ κ st-inv (au-θᵏ t ts))
               → (t : Term)
               → (ts : List Term)
               → (σ τ : SubC (List Term) Id)
               → (x y : Id)
               → gAllᵖ κ st-inv (au-θᵏ t ts)
au-θᵏ-inv-body = {!!}
-}

