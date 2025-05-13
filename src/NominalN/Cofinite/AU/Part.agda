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

  to-isubq-ins : ∀ {n} {ts : Vec Term n} {x} {θ : SubC (Vec Term n) Id}
               → to-isubq (insS ts x θ) ＝ insq ts x (to-isubq θ)
  to-isubq-ins = isubq-ext refl refl

  to-isubq-∉lup : ∀ {n} {ts : Vec Term n} {θ : SubC (Vec Term n) Id}
                → lupS ts θ ＝ nothing → ts ∉ to-isubq θ .idomq
  to-isubq-∉lup {θ} = ∉-list ∘ ∉lup {s = θ}

AUTy : ℕ → 𝒰
AUTy n = State (Id × SubC (Vec Term n) Id) Term

au-θ-miss : ∀ {n} → Vec Term n → AUTy n
au-θ-miss ts =
  do s ← st-gets snd
     Maybe.rec
       (map ``_ (gen unfin-ℕ ts))
       (λ x → pure (`` x))
       (lupS ts s)

au-θ-⟶ : ∀ {n} → AUTy n → AUTy n → AUTy n
au-θ-⟶ p q =
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
                  later (map²ᵏ au-θ-⟶
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
      vs = varsq tsv
      (ts′ , s) = pre-process tsv
      is = invS s
    in
  just $
  mapᵖ (λ st → let s = evalState st (new unfin-ℕ vs , empS) in
               post-process s is)
       (au-θ ts′)

-- termination

open decminmax ℕ-dec-total
open decminmaxprops ℕ-dec-total ℕ-dec-total

-- TODO try elim-un
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
    au-θ-⟶ resp resq
  , map²
      (λ (kp , kpeq) (kq , kqeq) →
            1 + max kp kq
          , fun-ext λ κ →
              ap later (▹-ext λ α →
                               let ihe = ▹-ap (pfix {k = κ} (au-θᵏ-body)) α in
                                  ap² (map²ᵏ au-θ-⟶)
                                      (happly ihe ps ∙ happly kpeq κ)
                                      (happly ihe qs ∙ happly kqeq κ)
                                ∙ delay-by-map²ᵏ au-θ-⟶ kp resp kq resq))
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

-- correctness

st-invΣ : ∀ {n} → SubC (Vec Term n) Id → Subq n → Id → Vec Term n → AUTy n → 𝒰
st-invΣ {n} θi θ x ts st =
   Σ[ s ꞉ Term ] Σ[ σi ꞉ SubC (Vec Term n) Id ] Σ[ σ ꞉ Subq n ] Σ[ y ꞉ Id ]
        (to-isubq σi ＝ inv-subq σ)
      × (runState st (x , θi) ＝ (s , y , σi))
      × Injective (σ .funq)  -- (II)
      × σ ≤↦q θ              -- (I)
      × ∥``↦q ts σ           -- (VI)
      × (joinₛ {js = ℕ-join-slat} (σ .domq) < y)

st-inv : ∀ {n} → Vec Term n → AUTy n → 𝒰
st-inv {n} ts st =
    (θi : SubC (Vec Term n) Id)
  → (θ : Subq n)
  → Injective (θ .funq)
  → to-isubq θi ＝ inv-subq θ
  → ∥``↦q ts θ
  → (x : Id)
  → joinₛ {js = ℕ-join-slat} (θ .domq) < x
  → st-invΣ θi θ x ts st

au-θ-miss-inv : ∀ {n}
              → 0 < n
              → (ts : Vec Term n)
              → unreplicate ts ＝ nothing
              → uncouple ts ＝ nothing
              → st-inv ts (au-θ-miss ts)
au-θ-miss-inv {n} lt ts unr unc θi θ θinj θe θd x xgt =
  Maybe.elim
    (λ q → lupS ts θi ＝ q → st-invΣ θi θ x ts (au-θ-miss ts))
    (λ ln →
          (`` x) , insS ts x θi , (θ ◇q (x ≔q ts)) , new1 unfin-ℕ x
        ,   to-isubq-ins
          ∙ ap (insq ts x) θe
          ∙ inv-insq (nothing-unrep-unrepvar {ts = ts} unr) unc
                (λ ts∈ → to-isubq-∉lup ln $ subst (λ q → ts ∈ₛ q .idomq) (θe ⁻¹) ts∈)
                (<-join∉ {uf = unfin-join-ℕ} xgt)
        ,   runState-bind
          ∙ ap (λ q → runState (Maybe.rec (st-map ``_ (gen unfin-ℕ ts))
                                          (st-pure ∘ ``_)
                                          (lupS ts (q .fst)))
                               (q .snd))
               runState-gets
          ∙ ap (λ q → runState (Maybe.rec (st-map ``_ (gen unfin-ℕ ts))
                                          (st-pure ∘ ``_)
                                          q)
                               (x , θi))
               ln
          ∙ runState-map
          ∙ ap (λ q → `` q .fst , q .snd)
               (  runState-bind
                ∙ ap (λ q → runState (st-bind (λ _ → st-pure (q .fst .fst)) 
                                              (st-put ( new1 unfin-ℕ (q .fst .fst)
                                                      , insS ts (q .fst .fst) (q .fst .snd))))
                                     (q .snd)) runState-get
                ∙ runState-bind
                ∙ runState-pure)
          ∙ ap (λ q → (`` x) , q .snd) runState-put
        , {!!}
        , {!!}
        , {!!}
        , new1< {uf = unfin-join-ℕ} xgt)
    (λ z lj →   `` z , θi , θ , x , θe
              ,   runState-bind
                ∙ ap (λ q → runState (Maybe.rec (st-map ``_ (gen unfin-ℕ ts))
                                                (st-pure ∘ ``_)
                                                (lupS ts (q .fst)))
                                     (q .snd))
                     runState-gets
                ∙ ap (λ q → runState (Maybe.rec (st-map ``_ (gen unfin-ℕ ts))
                                                (st-pure ∘ ``_)
                                                q)
                                     (x , θi))
                     lj
                ∙ runState-pure
              , (λ {x} {y} → θinj)
              , ≤↦q-refl {f = θ}
              , θd
              , xgt)
    (lupS ts θi)
    refl

au-θ-⟶-inv : ∀ {n}
             → 0 < n
             → (ps qs ts : Vec Term n)
             → ts ＝ couple ps qs
             → (sp sq : AUTy n)
             → st-inv ps sp → st-inv qs sq
             → st-inv ts (au-θ-⟶ sp sq)
au-θ-⟶-inv lt ps qs ts ets sp sq invp invq θi θ θinj θe θd x xgt =
  let (p , θi′ , θ′ , y , θe′ , ste′ , θinj′ , θ′≤ , θ∥′ , ygt) = invp θi  θ  θinj  θe  {!θd!} x xgt
      (q , θi″ , θ″ , z , θe″ , ste″ , θinj″ , θ″≤ , θ∥″ , zgt) = invq θi′ θ′ θinj′ θe′ {!θd!} y ygt
    in
    (p ⟶ q) , θi″ , θ″ , z
  , θe″
  ,   runState-bind
    ∙ runState-bind
    ∙ runState-pure
    ∙ ap (λ w → (w .fst ⟶ runState sq (w .snd) .fst) , runState sq (w .snd) .snd) ste′
    ∙ ap (λ w → (p ⟶ w .fst) , w .snd) ste″
  , θinj″
  , ≤↦-trans {f = θ″} {g = θ′} {h = θ} θ″≤ θ′≤
  , {!!}
  , zgt

au-θᵏ-inv-body : ∀ {n}
               → 0 < n
               → ▹ κ ((ts : Vec Term n) → gAllᵖ κ (st-inv ts) (au-θᵏ ts))
               → (ts : Vec Term n) → gAllᵖ κ (st-inv ts) (au-θᵏ ts)
au-θᵏ-inv-body     lt ih▹ ts with unreplicate ts | recall unreplicate ts
au-θᵏ-inv-body     lt ih▹ ts | just t  | ⟪ equr ⟫ =
  gAll-now λ θi θ θinj θe θd x xgt →
      t , θi , θ , x , θe
    , runState-pure
    , (λ {x} {y} → θinj)
    , ≤↦q-refl {f = θ}
    , θd
    , xgt
au-θᵏ-inv-body     lt ih▹ ts | nothing | ⟪ equr ⟫ with uncouple ts | recall uncouple ts
au-θᵏ-inv-body {κ} lt ih▹ ts | nothing | ⟪ equr ⟫ | just (ps , qs) | ⟪ equc ⟫ =
  let ec = couple-uncouple equc in
  gAll-later λ α →
    all-map²ᵏ
      (λ {x} {y} → au-θ-⟶-inv lt ps qs ts (ec ⁻¹) x y)
      (subst (gAllᵖ κ (st-inv ps))
             (happly (▹-ap (pfix au-θᵏ-body ⁻¹) α) ps)
             ((ih▹ ⊛ next ps) α))
      (subst (gAllᵖ κ (st-inv qs))
             (happly (▹-ap (pfix au-θᵏ-body ⁻¹) α) qs)
             ((ih▹ ⊛ next qs) α))
au-θᵏ-inv-body     lt ih▹ ts | nothing | ⟪ equr ⟫ | nothing        | ⟪ equc ⟫ =
  gAll-now $
  au-θ-miss-inv lt ts equr equc

au-θ-inv : ∀ {n}
         → 0 < n
         → (ts : Vec Term n)
         → Allᵖ (st-inv ts) (au-θ ts)
au-θ-inv lt ts κ = fix {k = κ} (au-θᵏ-inv-body lt) ts
