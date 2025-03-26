{-# OPTIONS --safe #-}
module State where

open import Prelude
open import Meta.Effect
open import Meta.Effect.Map
open import Meta.Effect.Idiom
open import Meta.Effect.Bind

open import Data.List

-- TODO generelize to StateT and unify with TcM in Nominal.Ribeiro.Infer

private variable
  ℓˢ ℓᵃ ℓᵇ ℓᶜ : Level
  S : 𝒰 ℓˢ
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ

opaque
  State : 𝒰 ℓˢ → 𝒰 ℓᵃ → 𝒰 (ℓˢ ⊔ ℓᵃ)
  State S A = S → A × S

  st-map : (A → B) → State S A → State S B
  st-map f sa s = first f (sa s)

  st-pure : A → State S A
  st-pure a s = a , s

  st-ap : State S (A → B) → State S A → State S B
  st-ap sab sa s =
    let (ab , s′) = sab s
        (b , s″) = sa s′
      in
    (ab b) , s″

  st-bind : (A → State S B) → State S A → State S B
  st-bind asb sa s =
    let (a , s′) = sa s
      in
    asb a s′

  -- derived

  st-get : State S S
  st-get s = s , s

  st-gets : (S → A) → State S A
  st-gets f s = f s , s

  st-put : S → State S ⊤
  st-put s _ = tt , s

  st-wrap : (S → A × S) → State S A
  st-wrap = id

  st-modify : (S → S) → State S ⊤
  st-modify f s = tt , f s

  runState : State S A → S → A × S
  runState = id

  evalState : State S A → S → A
  evalState sa s = fst (sa s)

  execState : State S A → S → S
  execState sa s = snd (sa s)

  -- laws

  st-map-pres-id : {S : 𝒰 ℓˢ} {A : 𝒰 ℓᵃ}
                 → st-map {A = A} {S = S} id ＝ id
  st-map-pres-id = refl

  st-map-pres-comp : {S : 𝒰 ℓˢ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {C : 𝒰 ℓᶜ}
                     {f : A → B} {g : B → C}
                   → st-map {S = S} (f ∙ g) ＝ st-map f ∙ st-map g
  st-map-pres-comp = refl

  st-pure-id : {S : 𝒰 ℓˢ} {A : 𝒰 ℓᵃ}
               {v : State S A}
             → st-ap (st-pure id) v ＝ v
  st-pure-id = refl

  st-pure-pres-ap : {S : 𝒰 ℓˢ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ}
                    {f : A → B} {x : A}
                   → st-ap {S = S} (st-pure f) (st-pure x) ＝ st-pure (f x)
  st-pure-pres-ap = refl

  st-pure-interchange : {S : 𝒰 ℓˢ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ}
                        {u : State S (A → B)} {v : A}
                      → st-ap {S = S} u (st-pure v) ＝ st-ap {S = S} (st-pure (_$ v)) u
  st-pure-interchange = refl

  st-pure-comp : {S : 𝒰 ℓˢ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {C : 𝒰 ℓᶜ}
                 {u : State S (B → C)} {v : State S (A → B)} {w : State S A}
               → st-ap (st-ap (st-ap (st-pure _∘ˢ_) u) v) w ＝ st-ap u (st-ap v w)
  st-pure-comp = refl

  st-map-pure : {S : 𝒰 ℓˢ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ}
                {f : A → B}
               → st-map {S = S} f ＝ λ x → st-ap (st-pure f) x
  st-map-pure = refl

  st-bind-id-l : {S : 𝒰 ℓˢ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ}
                 {f : A → State S B} {x : A}
               → st-bind f (st-pure x) ＝ f x
  st-bind-id-l = refl

  st-bind-id-r : {S : 𝒰 ℓˢ} {A : 𝒰 ℓᵃ}
                 {mx : State S A}
               → st-bind st-pure mx ＝ mx
  st-bind-id-r = refl

  st-bind-assoc : {S : 𝒰 ℓˢ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {C : 𝒰 ℓᶜ}
                  {mx : State S A} {f : A → State S B} {g : B → State S C}
                → st-bind g (st-bind f mx) ＝ st-bind (λ x → st-bind g (f x)) mx
  st-bind-assoc = refl

  st-ap-bind : {S : 𝒰 ℓˢ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ}
               {mf : State S (A → B)} {mx : State S A}
             → st-ap mf mx ＝ st-bind (λ f → st-bind (st-pure ∘ f) mx) mf
  st-ap-bind = refl

  -- running

  runState-pure : {S : 𝒰 ℓˢ} {A : 𝒰 ℓᵃ} {x : A} {s : S}
                → runState (st-pure x) s ＝ (x , s)
  runState-pure = refl

  runState-ap : {S : 𝒰 ℓˢ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ} {f : State S (A → B)} {x : State S A} {s : S}
              → runState (st-ap f x) s ＝ let (ab , s′) = runState f s in
                                          let (b , s″)  = runState x s′ in
                                          (ab b) , s″
  runState-ap = refl

  eval-run : {S : 𝒰 ℓˢ} {A : 𝒰 ℓᵃ} {x : State S A} {s : S}
           → evalState x s ＝ (runState x s) .fst
  eval-run = refl

instance
  Map-State : Map (eff (State S))
  Map-State .map = st-map

  Lawful-Map-State : Lawful-Map (eff (State S))
  Lawful-Map-State .map-pres-id = st-map-pres-id
  Lawful-Map-State .map-pres-comp = st-map-pres-comp

  Idiom-State : Idiom (eff (State S))
  Idiom-State .pure  = st-pure
  Idiom-State ._<*>_ = st-ap

  Lawful-Idiom-State : Lawful-Idiom (eff (State S))
  Lawful-Idiom-State .has-lawful-map = Lawful-Map-State
--  Lawful-Idiom-State .pure-id = st-pure-id
  Lawful-Idiom-State .pure-pres-app = st-pure-pres-ap
  Lawful-Idiom-State .pure-interchange = st-pure-interchange
  Lawful-Idiom-State .pure-comp = st-pure-comp
  Lawful-Idiom-State .map-pure = st-map-pure

  Bind-State : Bind (eff (State S))
  Bind-State ._>>=_ = flip st-bind

  Lawful-Bind-State : Lawful-Bind (eff (State S))
  Lawful-Bind-State .has-lawful-idiom = Lawful-Idiom-State
  Lawful-Bind-State .>>=-id-l = st-bind-id-l
  Lawful-Bind-State .>>=-id-r = st-bind-id-r
  Lawful-Bind-State .>>=-assoc = st-bind-assoc
  Lawful-Bind-State .<*>->>= = st-ap-bind

opaque
  -- TODO is there a more generic way?

  runState-traverse-length : {S : 𝒰 ℓˢ} {A : 𝒰 ℓᵃ} {B : 𝒰 ℓᵇ}
                             {f : A → State S B} {s : S} {xs : List A}
                           → length xs ＝ length (evalState (traverse f xs) s)
  runState-traverse-length {f} {s} {xs = []}     = ap length (ap fst (runState-pure ⁻¹) ∙ eval-run ⁻¹)
  runState-traverse-length {f} {s} {xs = x ∷ xs} =
      ap suc
         (  runState-traverse-length {f = f} {s = (runState (f x) s .snd)}
          ∙ ap length eval-run)
    ∙ ap length
          (  ap (λ q → (q .fst (runState (f x) (q .snd) .fst) (runState (list-traverse f xs) (runState (f x) (q .snd) .snd) .fst)))
                (runState-pure {x = _∷_} ⁻¹)
           ∙ ap fst (  ap (λ q → ( q .fst (runState (list-traverse f xs) (q .snd) .fst)
                               , runState (list-traverse f xs) (q .snd) .snd))
                        (runState-ap ⁻¹)
                   ∙ runState-ap ⁻¹)
           ∙ eval-run ⁻¹)
