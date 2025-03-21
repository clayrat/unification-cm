{-# OPTIONS --guarded #-}
module NominalN.Cofinite.AU.Part where

open import Prelude
open import Meta.Effect
open import Meta.Effect.Traversable

open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.String
open import Data.Maybe as Maybe
open import Data.List as List
open import Data.List.Correspondences.Unary.All

open import Later
open import Clocked.Partial
open import Clocked.Partial.Converges
open import Clocked.Partial.All

open import LFSet
open import Unfinite
open import State

open import Id
open import NominalN.Term
open import NominalN.Cofinite.Base
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

au-θᵏ-body : ▹ κ (Term → List Term → gPart κ (State (Id × SubT (List Term) Id) Term))
           → Term → List Term → gPart κ (State (Id × SubT (List Term) Id) Term)
au-θᵏ-body a▹ t ts =
  if all (_=? t) ts
    then now (pure t)
    else
       Maybe.rec
        (now $
         do s ← st-gets snd
            Maybe.rec
              (map ``_ (gen unfin-ℕ (t ∷ ts)))
              (λ x → pure (`` x))
              (lupST (t ∷ ts) s))
        (λ where (p , ps , q , qs) →
                   later ((λ p′ q′ → p′ >>=ᵏ λ pm →
                                     q′ >>=ᵏ λ qm →
                                     now (do pt ← pm
                                             qt ← qm
                                             pure (pt ⟶ qt)))
                         ⍉ (a▹ ⊛ next p ⊛ next ps)
                         ⊛ (a▹ ⊛ next q ⊛ next qs)))
        (uncouple t ts)

au-θᵏ : Term → List Term → gPart κ (State (Id × SubT (List Term) Id) Term)
au-θᵏ = fix au-θᵏ-body

au-θ : Term → List Term → Part (State (Id × SubT (List Term) Id) Term)
au-θ t ts κ = au-θᵏ t ts

au : List Term → Maybe (Part Term)
au []       = nothing
au (t ∷ ts) =
  let vs = bindₛ vars (from-list (t ∷ ts))
      (t′ , ts′ , s) = pre-process t ts
      is = invST s
    in
  just $
  mapᵖ (λ st → let s = evalState st ((new unfin-ℕ vs) , empST) in
               post-process s is)
       (au-θ t′ ts′)
