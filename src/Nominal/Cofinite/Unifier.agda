{-# OPTIONS --safe #-}
module Nominal.Cofinite.Unifier where

open import Prelude
open import Meta.Effect

open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.List as List
open import Data.List.Correspondences.Unary.All

open import LFSet

open import Nominal.Term
open import Nominal.Cofinite.Base
open import Nominal.Cofinite.Sub

-- unifier

unifies : Term → Term → ↦𝒫
unifies x y s = s $↦ x ＝ s $↦ y

unifies-swap : {s t : Term} → ↦𝒫≃ (unifies s t) (unifies t s)
unifies-swap {s} {t} f = prop-extₑ! _⁻¹ _⁻¹

↦thin-unifies : {s t : Term} → ↦thin (unifies s t)
↦thin-unifies {s} {t} f w u =
  thin-$↦ {xs = w} {t = s} ∙ u ∙ thin-$↦ {xs = w} {t = t} ⁻¹

thin↦-unifies : {s t : Term} → thin↦ (unifies s t)
thin↦-unifies {s} {t} f w u =
  thin-$↦ {xs = w} {t = s} ⁻¹ ∙ u ∙ thin-$↦ {xs = w} {t = t}

unifier : List Constr → ↦𝒫
unifier cs s = All (λ where (x , y) → unifies x y s) cs

↦thin-unifier : ∀ {xs} → ↦thin (unifier xs)
↦thin-unifier f w = all-map λ where {x = x , y} → ↦thin-unifies {s = x} {t = y} f w

thin↦-unifier : ∀ {xs} → thin↦ (unifier xs)
thin↦-unifier f w = all-map λ where {x = x , y} → thin↦-unifies {s = x} {t = y} f w

DCl-unifies : ∀ {s t} → DCl (unifies s t)
DCl-unifies {s} {t} f g (fg , fgw , fge) u =
  thin↦-unifies {s = s} {t = t} f fgw $
     subst (unifies s t) fge $
     (  sub-◇ {s1 = fg} {s2 = g} {t = s}
      ∙ ap (fg $↦_) u
      ∙ sub-◇ {s1 = fg} {s2 = g} {t = t} ⁻¹)

DCl-unifier : ∀ {ls} → DCl (unifier ls)
DCl-unifier {ls} f g le =
  all-map (λ where {x = x , y} → DCl-unifies {s = x} {t = y} f g le)

unifier-eq : ∀ {p q l} → p ＝ q → ↦𝒫≃ (unifier l) (unifier ((p , q) ∷ l))
unifier-eq e s = prop-extₑ! (λ u → (ap (s $↦_) e) ∷ u) all-tail

unifier-append→ : ∀ {v t su} l
               → unifier ((v ≔ t) $↦L l) su
               → unifier l (su ◇ (v ≔ t))
unifier-append→ []            []       = []
unifier-append→ ((x , y) ∷ l) (u ∷ us) =
  (sub-◇ {t = x} ∙ u ∙ sub-◇ {t = y} ⁻¹)
   ∷ unifier-append→ l us

unifier-append← : ∀ {v t su} l
               → unifier l (su ◇ (v ≔ t))
               → unifier ((v ≔ t) $↦L l) su
unifier-append← []            []       = []
unifier-append← ((x , y) ∷ l) (u ∷ us) =
  (sub-◇ {t = x} ⁻¹ ∙ u ∙ sub-◇ {t = y})
   ∷ unifier-append← l us

unifier-append≃ : ∀ {v t su l}
                → unifier ((v ≔ t) $↦L l) su ≃ unifier l (su ◇ (v ≔ t))
unifier-append≃ {l} = prop-extₑ! (unifier-append→ l) (unifier-append← l)

unifier-⟶≃ : ∀ {pl ql pr qr lc}
             → ↦𝒫≃ (unifier (((pl ⟶ ql) , (pr ⟶ qr)) ∷ lc))
                    (unifier ((pl , pr) ∷ (ql , qr) ∷ lc))
unifier-⟶≃ {pl} {ql} {pr} {qr} {lc} s =
  prop-extₑ!
    (λ where (a ∷ as) →
               (⟶-inj a .fst) ∷ (⟶-inj a .snd) ∷ as)
    λ where (al ∷ ar ∷ as) → (ap² _⟶_ al ar) ∷ as

unify-tm : ∀ {v t′ s} t
         → unifies (`` v) t′ s
         → unifies t ((v ≔ t′) $↦ t) s
unify-tm {v} {t′} {s} (`` x)    ea =
  Dec.elim
    {C = λ q → (s $ x) ＝ (s $↦ (if ⌊ q ⌋ then t′ else (`` x)))}
    (λ evx → ap (s $_) (evx ⁻¹) ∙ ea)
    (λ _ → refl)
    (v ≟ x)
unify-tm         {s} (p ⟶ q) ea =
  ap² _⟶_ (unify-tm {s = s} p ea) (unify-tm {s = s} q ea)
unify-tm              con      ea = refl

unifier-subs : ∀ {v t s} l
             → unifies (`` v) t s
             → unifier l s
             → unifier ((v ≔ t) $↦L l) s
unifier-subs     []              ea       u  = []
unifier-subs {s} ((tl , tr) ∷ l) ea (et ∷ u) =
  unify-tm {s = s} tl ea ⁻¹ ∙ et ∙ unify-tm {s = s} tr ea ∷ unifier-subs {s = s} l ea u

max-flex-rigid : ∀ {v t}
               → ¬ occurs v t
               → Max↦ (unifies (`` v) t) (v ≔ t)
max-flex-rigid {v} {t} noc =
    (given-yes (the (v ＝ v) refl)
       return (λ q → (if ⌊ q ⌋ then t else `` v) ＝ (v ≔ t) $↦ t)
       then sub-occurs t noc)
  , λ f′ u′ →
      ( f′ , v ∷ []
      , sub-ext
           (fun-ext λ x →
                Dec.elim
                   {C = λ q → f′ $↦ (if ⌊ q ⌋ then t else `` x) ＝ (f′ $ x)}
                   (λ e → u′ ⁻¹ ∙ ap (f′ $_) e)
                   (λ _ → refl)
                   (v ≟ x))
           refl)

no-unify-+var : ∀ {x : Id} {p ps}
              → ↦𝒫∅ (unifies (`` x) ((p ∷ ps) +: (`` x)))
no-unify-+var {p} {ps} f u =
  false! $ no-cycle-lemma ((u ∙ +:-subst {f = f} {ps = p ∷ ps}) ⁻¹)
