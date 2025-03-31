{-# OPTIONS --guarded #-}
module NominalN.Cofinite.AU.Part where

open import Prelude
open import Meta.Effect
open import Meta.Effect.Traversable

open import Data.Acc
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

open import Order.Constructions.Minmax
open import Order.Constructions.Nat

open import Later
open import Clocked.Partial
open import Clocked.Partial.Converges
open import Clocked.Partial.All

open import LFSet
open import Unfinite
open import State
open import SubC

open import Id
open import NominalN.Term
open import NominalN.Cofinite.BaseA
open import NominalN.Cofinite.Sub
open import NominalN.Cofinite.ISub
open import NominalN.Cofinite.AU

private variable
  ℓᵃ ℓᵇ ℓᶜ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ
  κ : Cl

{-
au-θ : Term → List Term → State (Id × SubT (List Term) Id) Term
au-θ t ts =
  if all (_=? t) ts
    then pure t
    else
      Maybe.rec
        (do s ← st-gets snd
            Maybe.rec
              (map ``_ (gen unfin-ℕ (t ∷ ts)))
              (λ x → pure (`` x))
              (lupST (t ∷ ts) s))
        (λ where (p , ps , q , qs) →
                   do p′ ← au-θ p ps
                      q′ ← au-θ q qs
                      pure (p′ ⟶ q′))
        (uncouple t ts)

au : List Term → Maybe Term
au []       = nothing
au (t ∷ ts) =
  let vs = bindₛ vars (from-list ts)
      (t′ , ts′ , s) = pre-process t ts
      is = invST s
      s = evalState
            (au-θ t′ ts′)
            ((new unfin-ℕ vs) , empST)
    in
  just (post-process s is)

-}

AUTy : 𝒰
AUTy = State (Id × SubC (List Term) Id) Term

au-θ-miss : List Term → AUTy
au-θ-miss ts =
  do s ← st-gets snd
     Maybe.rec
       (map ``_ (gen unfin-ℕ ts))
       (λ x → pure (`` x))
       (lupS ts s)

au-⟶ : AUTy → AUTy → AUTy
au-⟶ p q =
  do p′ ← p
     q′ ← q
     pure (p′ ⟶ q′)

au-θᵏ-body : ▹ κ (Term → List Term → gPart κ AUTy)
           → Term → List Term → gPart κ AUTy
au-θᵏ-body a▹ t ts =
  if all (_=? t) ts
    then now (pure t)
    else
      Maybe.rec
        (now $ au-θ-miss (t ∷ ts))
        (λ where ((p , ps) , (q , qs)) →
                   later (map²ᵏ au-⟶
                          ⍉ (a▹ ⊛ next p ⊛ next ps)
                          ⊛ (a▹ ⊛ next q ⊛ next qs)))
        (uncouple1 t ts)

au-θᵏ : Term → List Term → gPart κ AUTy
au-θᵏ = fix au-θᵏ-body

au-θ : Term → List Term → Part AUTy
au-θ t ts κ = au-θᵏ t ts

au : List Term → Maybe (Part Term)
au []       = nothing
au (t ∷ ts) =
  let vs = bindₛ vars (from-list (t ∷ ts))
      (t′ , ts′ , s) = pre-process t ts
      is = invS s
    in
  just $
  mapᵖ (λ st → let s = evalState st ((new unfin-ℕ vs) , empS) in
               post-process s is)
       (au-θ t′ ts′)

-- termination

open decminmax ℕ-dec-total
open decminmaxprops ℕ-dec-total ℕ-dec-total

au-θ⇓-body : ∀ t ts
           → (∀ t' ts' → tm-sizes (t' ∷ ts') < tm-sizes (t ∷ ts) → au-θ t' ts' ⇓)
           → au-θ t ts ⇓
au-θ⇓-body t ts ih with all (_=? t) ts | recall (all (_=? t)) ts
au-θ⇓-body t ts ih | true  | _       = pure t , ∣ 0 , refl ∣₁
au-θ⇓-body t ts ih | false | ⟪ eqa ⟫ with uncouple1 t ts | recall (uncouple1 t) ts
au-θ⇓-body t ts ih | false | ⟪ eqa ⟫ | just ((p , ps) , (q , qs)) | ⟪ equ ⟫ =
  let (l< , r<) = uncouple1-sizes {t = t} {ts = ts} equ
      (resp , cnvp) = ih p ps l<
      (resq , cnvq) = ih q qs r<
    in
    au-⟶ resp resq
  , map²
      (λ (kp , kpeq) (kq , kqeq) →
            1 + max kp kq
          , fun-ext λ κ →
              ap later (▹-ext λ α →
                                let ihe = ▹-ap (pfix {k = κ} au-θᵏ-body) α in
                                ap² (map²ᵏ au-⟶)
                                    (happly (happly ihe p) ps ∙ happly kpeq κ)
                                    (happly (happly ihe q) qs ∙ happly kqeq κ)
                              ∙ delay-by-map²ᵏ au-⟶ kp resp kq resq))
      cnvp cnvq
au-θ⇓-body t ts ih | false | ⟪ eqa ⟫ | nothing | equ =
  au-θ-miss (t ∷ ts) , ∣ 0 , refl ∣₁

au-θ⇓ : ∀ {t ts} → au-θ t ts ⇓
au-θ⇓ {t} {ts} =
  to-induction
    (wf-lift (λ (z , zs) → tm-sizes (z ∷ zs)) <-is-wf)
    (λ (z , zs) → au-θ z zs ⇓)
    (λ (z , zs) ih → au-θ⇓-body z zs λ z' zs' → ih (z' , zs'))
    (t , ts)

au⇓ : ∀ {ts} → Maybe.rec ⊤ _⇓ (au ts)
au⇓ {ts = []}     = tt
au⇓ {ts = t ∷ ts} =
  let vs = bindₛ vars (from-list (t ∷ ts))
      (t′ , ts′ , s) = pre-process t ts
      is = invS s
      (r , r⇓) = au-θ⇓ {t = t′} {ts = ts′}
     in
     post-process (evalState r (new unfin-ℕ vs , empS)) is
   , map⇓ (λ st → post-process (evalState st (new unfin-ℕ vs , empS)) is) r⇓

-- correctness
