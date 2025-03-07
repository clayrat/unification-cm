{-# OPTIONS --safe #-}
module NominalN.Cofinite.MM where

open import Prelude
open import Meta.Effect

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.List as List
open import Data.List.Correspondences.Unary.All
open import Data.List.Operations.Properties
open import Data.List.Operations.Discrete
open import Data.Sum as ⊎
open import Data.Plus
open import Data.AF
open import Data.Acc

open import Order.Constructions.Lex

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

open import Id
open import NominalN.Term
open import NominalN.Cofinite.Base
open import NominalN.Cofinite.Sub
open import NominalN.Cofinite.Unifier

-- Naive Martelli-Montanari algorithm

-- computational (triangular) substitution

SubT : 𝒰
SubT = List (Id × Term)

to-sub : SubT → Sub
to-sub = List.rec id↦ (λ where (x , t) → _◇ (x ≔ t))

app-sng : Id → Term → Term → Term
app-sng v t (`` x)    = if v == x then t else `` x
app-sng v t (p ⟶ q) = app-sng v t p ⟶ app-sng v t q
app-sng v t (con s)   = con s

app-sngL : Id → Term → List Constr → List Constr
app-sngL v t = map (bimap (app-sng v t) (app-sng v t))

app-sng-$↦ : ∀ {v t q} → app-sng v t q ＝ (v ≔ t) $↦ q
app-sng-$↦ {q = `` x}    = refl
app-sng-$↦ {q = p ⟶ q} = ap² _⟶_ (app-sng-$↦ {q = p}) (app-sng-$↦ {q = q})
app-sng-$↦ {q = con s}   = refl

app-sngL-$↦L : ∀ {v t l} → app-sngL v t l ＝ (v ≔ t) $↦L l
app-sngL-$↦L {l} =
  ap (λ q → mapₗ (bimap q q) l) (fun-ext λ q → app-sng-$↦ {q = q})

-- TODO decompose
wf-sub-insert : ∀ {ctx su v t}
              → wf-tm (rem v ctx) t
              → v ∈ ctx
              → Wf-subst (rem v ctx) (to-sub su)
              → Wf-subst ctx (to-sub ((v , t) ∷ su))
wf-sub-insert {ctx} {su} {v} {t} wr vin wf {x} xin =
  caseᵈ v ＝ x of
    λ where
       (yes v=x) →
           subst (_∈ ctx) v=x vin
         , (given-yes v=x
              return (λ q → wf-tm (minus ctx (v ∷ to-sub su .dom))
                                  (to-sub su $↦ (if ⌊ q ⌋ then t else `` x)))
              then subst (λ q → wf-tm q (to-sub su $↦ t))
                         (minus-rem-l ∙ minus-∷-r ⁻¹)
                         (substs-remove wf wr))
       (no v≠x) →
            Recomputable-×
             Recomputable-∈ₛ (wf-tm-recomp {t = to-sub ((v , t) ∷ su) $ x})
             .recompute $
               erase
                (elim! {P = λ _ → (x ∈ₛ ctx)
                                    ×ₜ wf-tm (minus ctx (v ∷ to-sub su .dom))
                                             (to-sub ((v , t) ∷ su) $ x)}
                   [ (λ e → absurd (v≠x (e ⁻¹)))
                   , (λ x∈′ → let (x∈r , wtx) = wf (⇉∈ₛ $ erase x∈′) in
                                 rem-⊆ x∈r
                               , (given-no v≠x
                             return (λ q → wf-tm (minus ctx (v ∷ to-sub su .dom))
                                                 (to-sub su $↦ (if ⌊ q ⌋ then t else `` x)))
                             then subst (λ q → wf-tm q (to-sub su $ x))
                                        (minus-rem-l ∙ minus-∷-r ⁻¹)
                                        wtx))
                   ]ᵤ (∈ₛ⇉ xin .erased))

-- failure

data UnifyFailure : List Constr → 𝒰 where
  -- occurrence failures
  occ-fail-l  : ∀ {v t lc}
              → t ≠ `` v → occurs v t
              → UnifyFailure ((`` v , t) ∷ lc)
  occ-fail-r  : ∀ {v t lc}
              → t ≠ `` v → occurs v t
              → UnifyFailure ((t , `` v) ∷ lc)
  -- symbol mismatches
  con-con-sym : ∀ {sl sr lc}
              → sl ≠ sr
              → UnifyFailure ((con sl , con sr) ∷ lc)
  con-app     : ∀ {l r s lc}
              → UnifyFailure ((con s , l ⟶ r) ∷ lc)
  app-con     : ∀ {l r s lc}
              → UnifyFailure ((l ⟶ r , con s) ∷ lc)
  -- recursive propagation
  arrarr-rec  : ∀ {l l' r r' lc}
              → UnifyFailure ((l , l') ∷ (r , r') ∷ lc)
              → UnifyFailure ((l ⟶ r , l' ⟶ r') ∷ lc)
  eq-rec      : ∀ {t t' l}
              → t ＝ t'
              → UnifyFailure l
              → UnifyFailure ((t , t') ∷ l)
  subs-rec-l  : ∀ {v t l}
              → UnifyFailure (app-sngL v t l)
              → UnifyFailure ((`` v , t) ∷ l)
  subs-rec-r  : ∀ {v t l}
              → UnifyFailure (app-sngL v t l)
              → UnifyFailure ((t , `` v) ∷ l)

failure→no-unifier : ∀ {lc} → UnifyFailure lc → ↦𝒫∅ (unifier lc)
failure→no-unifier (occ-fail-l {t} ne oc) s u with occ→ctx {t = t} oc
... | []    , e = ne e
... | p ∷ c , e = no-unify-+var {p = p} s (all-head u ∙ ap (s $↦_) e)
failure→no-unifier (occ-fail-r {t} ne oc) s u with occ→ctx {t = t} oc
... | []    , e = ne e
... | p ∷ c , e = no-unify-+var {p = p} s (all-head u ⁻¹ ∙ ap (s $↦_) e)
failure→no-unifier (con-con-sym ne)       s u =
  ne (con-inj (all-head u))
failure→no-unifier  con-app        s u = ⟶≠con (all-head u ⁻¹)
failure→no-unifier  app-con        s u = ⟶≠con (all-head u)
failure→no-unifier (arrarr-rec uf) s u =
  failure→no-unifier uf s (unifier-⟶≃ s $ u)
failure→no-unifier (eq-rec _ uf)   s u =
  failure→no-unifier uf s (all-tail u)
failure→no-unifier (subs-rec-l {l} uf) s u =
  failure→no-unifier uf s $
  subst (λ q → unifier q s)
         (app-sngL-$↦L ⁻¹)
        (unifier-subs l (all-head u) (all-tail u))
failure→no-unifier (subs-rec-r {l} uf) s u =
  failure→no-unifier uf s $
  subst (λ q → unifier q s)
         (app-sngL-$↦L ⁻¹)
         (unifier-subs l (all-head u ⁻¹) (all-tail u))

-- constraint order

_<C_ : Constrs → Constrs → 𝒰
_<C_ = ×-lex (λ v₁ v₂ → sizeₛ v₁ < sizeₛ v₂) (λ c₁ c₂ → list-measure c₁ < list-measure c₂)

_≤C_ : Constrs → Constrs → 𝒰
(v₁ , c₁) ≤C (v₂ , c₂) = (sizeₛ v₁ ≤ sizeₛ v₂) × (list-measure c₁ ≤ list-measure c₂)

≤C-af : AF _≤C_
≤C-af = af-× (af-comap sizeₛ af-≤) (af-comap list-measure af-≤)

<∩≤C=∅ : ∀ {v₁ c₁ v₂ c₂}
              → Plus _<C_ (v₁ , c₁) (v₂ , c₂)
              → (v₂ , c₂) ≤C (v₁ , c₁)
              → ⊥
<∩≤C=∅ {v₁} {c₁} {v₂} {c₂} p (le₁ , le₂) =
  [ ≤→≯ le₁ , ≤→≯ le₂ ∘ snd ]ᵤ
   (plus-fold1
      (record { _∙_ = λ {x} {y} {z} →
              ×-lex-trans <-trans <-trans {pqx = x} {pqy = y} {pqz = z}})
       p)

<C-wf : is-wf _<C_
<C-wf = AF→WF ≤C-af <∩≤C=∅

lt-list-constr-lt-constraints : ∀ {t t′ c l} → (c , l) <C (c , (t , t′) ∷ l)
lt-list-constr-lt-constraints {t} {t′} {l} =
  inr (refl , <-+-0lr (<-+-r (0<tm-size {t = t})))

app-lt-measure : ∀ {l l′ r r′ lc}
               → list-measure ((l , l′) ∷ (r , r′) ∷ lc) < list-measure ((l ⟶ r , l′ ⟶ r′) ∷ lc)
app-lt-measure {l} {l′} {r} {r′} {lc} =
  subst (_< list-measure ((l ⟶ r , l′ ⟶ r′) ∷ lc))
        (+-assoc (tm-size l + tm-size l′) (tm-size r + tm-size r′) (list-measure lc) ⁻¹) $
  <-≤-+ {m = tm-size l + tm-size l′ + (tm-size r + tm-size r′)}
    (subst (λ q → tm-size l + tm-size l′ + (tm-size r + tm-size r′) < suc q)
           (+-suc-r (tm-size l + tm-size r) (tm-size l′ + tm-size r′) ⁻¹) $
     subst (λ q → tm-size l + tm-size l′ + (tm-size r + tm-size r′) < suc (suc q))
           (+-interchange (tm-size l) (tm-size l′) (tm-size r) (tm-size r′)) $
     <-+-lr {n = 1})
    (=→≤ refl)

app-lt-constraints : ∀ {l l′ r r′ lc c}
                   → (c , (l , l′) ∷ (r , r′) ∷ lc) <C (c , (l ⟶ r , l′ ⟶ r′) ∷ lc)
app-lt-constraints {l} {l′} {r} {r′} {lc} =
  inr (refl , app-lt-measure {l = l} {l′ = l′} {r = r} {r′ = r′} {lc = lc})

rem<C : ∀ {c v xs ys} → v ∈ c → (rem v c , xs) <C (c , ys)
rem<C {v} vi = inl (rem-size-neg vi)
