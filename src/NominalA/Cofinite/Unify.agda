{-# OPTIONS --safe #-}
module NominalA.Cofinite.Unify where

open import Prelude
open import Meta.Effect

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.String
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

open import NominalA.Term
open import NominalA.Cofinite.Base
open import NominalA.Cofinite.Sub

-- unifier

unifies : Term → Term → ↦𝒫
unifies x y s = s $↦ x ＝ s $↦ y

unifies-s : List Term → List Term → ↦𝒫
unifies-s xs ys s = s $↦[] xs ＝ s $↦[] ys

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

unifier→zip : ∀ {xs ys s}
            → length xs ＝ length ys
            → unifier (zip xs ys) s → unifies-s xs ys s
unifier→zip {xs = []}     {ys = []}     e  u      = refl
unifier→zip {xs = []}     {ys = y ∷ ys} e  u      = false! e
unifier→zip {xs = x ∷ xs} {ys = []}     e  u      = false! e
unifier→zip {xs = x ∷ xs} {ys = y ∷ ys} e (q ∷ u) =
  ap² {C = λ x xs → List Term} _∷_ q (unifier→zip (suc-inj e) u)

unifier←zip : ∀ {xs ys s}
            → length xs ＝ length ys
            → unifies-s xs ys s → unifier (zip xs ys) s
unifier←zip {xs = []}     {ys = []}     e u = []
unifier←zip {xs = []}     {ys = y ∷ ys} e u = false! e
unifier←zip {xs = x ∷ xs} {ys = []}     e u = false! e
unifier←zip {xs = x ∷ xs} {ys = y ∷ ys} e u =
  ∷-head-inj u ∷ unifier←zip (suc-inj e) (∷-tail-inj u)

-- unused
unifier-zip : {xs ys : List Term}
            → length xs ＝ length ys
            → ↦𝒫≃ (unifier (zip xs ys)) (unifies-s xs ys)
unifier-zip {xs} {ys} e s =
  prop-extₑ!
    (unifier→zip e)
    (unifier←zip e)

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

unifier-con≃ : ∀ {sl sr tsl tsr lc}
             → sl ＝ sr
             → length tsl ＝ length tsr
             → ↦𝒫≃ (unifier ((con sl tsl , con sr tsr) ∷ lc))
                    (unifier (zip tsl tsr ++ lc))
unifier-con≃ {tsl} {tsr} e et s =
  prop-extₑ!
    (λ where (a ∷ as) →
                all-++ {xs = zip tsl tsr} (unifier←zip et (con-inj a .snd)) as)
    λ a → let (az , al) = all-split a in ap² con e (unifier→zip et az) ∷ al

mutual
  unify-tm : ∀ {v t′ s} t
           → unifies (`` v) t′ s
           → unifies t ((v ≔ t′) $↦ t) s
  unify-tm {v} {t′} {s} (`` x)     ea =
    Dec.elim
      {C = λ q → (s $ x) ＝ (s $↦ (if ⌊ q ⌋ then t′ else (`` x)))}
      (λ evx → ap (s $_) (evx ⁻¹) ∙ ea)
      (λ _ → refl)
      (v ≟ x)
  unify-tm         {s} (con sy ts) ea =
    ap (con sy) (unify-tms ts ea)

  unify-tms : ∀ {v t′ s} ts
            → unifies (`` v) t′ s
            → unifies-s ts ((v ≔ t′) $↦[] ts) s
  unify-tms []       u = refl
  unify-tms (t ∷ ts) u = ap² {C = λ x xs → List Term} _∷_ (unify-tm t u) (unify-tms ts u)

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

-- computational (triangular) substitution

SubT : 𝒰
SubT = List (Id × Term)

to-sub : SubT → Sub
to-sub = List.rec id↦ (λ where (x , t) → _◇ (x ≔ t))

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
                                    × wf-tm (minus ctx (v ∷ to-sub su .dom))
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
  occ-fail-l  : ∀ {v t lc}
              → t ≠ `` v → occurs v t
              → UnifyFailure ((`` v , t) ∷ lc)
  occ-fail-r  : ∀ {v t lc}
              → t ≠ `` v → occurs v t
              → UnifyFailure ((t , `` v) ∷ lc)
  con-con-sym : ∀ {sl sr tsl tsr lc}
              → sl ≠ sr
              → UnifyFailure ((con sl tsl , con sr tsr) ∷ lc)
  con-con-rec : ∀ {sl sr tsl tsr lc}
              → sl ＝ sr
              → length tsl ＝ length tsr
              → UnifyFailure (zip tsl tsr ++ lc)
              → UnifyFailure ((con sl tsl , con sr tsr) ∷ lc)
  constr-rec  : ∀ {t t' l}
              → UnifyFailure l
              → UnifyFailure ((t , t') ∷ l)
  subs-rec-l  : ∀ {v t l}
              → UnifyFailure ((v ≔ t) $↦L l)
              → UnifyFailure ((`` v , t) ∷ l)
  subs-rec-r  : ∀ {v t l}
              → UnifyFailure ((v ≔ t) $↦L l)
              → UnifyFailure ((t , `` v) ∷ l)

failure→no-unifier : ∀ {lc} → UnifyFailure lc → ↦𝒫∅ (unifier lc)
failure→no-unifier (occ-fail-l {t} ne oc) s u with occ→ctx {t = t} oc
... | []    , e = ne e
... | p ∷ c , e = no-unify-+var {p = p} s (all-head u ∙ ap (s $↦_) e)
failure→no-unifier (occ-fail-r {t} ne oc) s u with occ→ctx {t = t} oc
... | []    , e = ne e
... | p ∷ c , e = no-unify-+var {p = p} s (all-head u ⁻¹ ∙ ap (s $↦_) e)
failure→no-unifier (con-con-sym ne)       s u =
  ne (con-inj (all-head u) .fst)
failure→no-unifier (con-con-rec e et uf)     s u =
  failure→no-unifier uf s (all-++ (unifier←zip et (con-inj (all-head u) .snd)) (all-tail u))
failure→no-unifier (constr-rec uf)        s u =
  failure→no-unifier uf s (all-tail u)
failure→no-unifier (subs-rec-l {l} uf)    s u =
  failure→no-unifier uf s (unifier-subs l (all-head u) (all-tail u))
failure→no-unifier (subs-rec-r {l} uf)    s u =
  failure→no-unifier uf s (unifier-subs l (all-head u ⁻¹) (all-tail u))

-- constraint order

_<C_ : Constrs → Constrs → 𝒰
_<C_ = ×-lex (λ v₁ v₂ → sizeₛ v₁ < sizeₛ v₂) (λ c₁ c₂ → list-measure (c₁ .snd) < list-measure (c₂ .snd))

_≤C_ : Constrs → Constrs → 𝒰
(v₁ , _ , c₁) ≤C (v₂ , _ , c₂) = (sizeₛ v₁ ≤ sizeₛ v₂) × (list-measure c₁ ≤ list-measure c₂)

≤C-af : AF _≤C_
≤C-af = af-× (af-comap sizeₛ af-≤) (af-comap (list-measure ∘ snd) af-≤)

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

lt-list-constr-lt-constraints : ∀ {t t′ c a l} → (c , a , l) <C (c , a , (t , t′) ∷ l)
lt-list-constr-lt-constraints {t} {t′} {l} =
  inr (refl , <-+-0lr (<-+-r (0<ty-size {t = t})))

app-lt-measure : ∀ {s ts ts′ lc}
               → length ts ＝ length ts′
               → list-measure (zip ts ts′ ++ lc) < list-measure ((con s ts , con s ts′) ∷ lc)
app-lt-measure {s} {ts} {ts′} {lc} e =
  subst (_< list-measure ((con s ts , con s ts′) ∷ lc))
        (list-measure-++ {xs = zip ts ts′} {ys = lc} ⁻¹) $
  <-≤-+ {m = list-measure (zip ts ts′)}
    (subst (_< suc (terms-size ts + suc (terms-size ts′)))
           (list-measure-zip e ⁻¹) $
     subst (λ q → terms-size ts + terms-size ts′ < suc q)
           (+-suc-r (terms-size ts) (terms-size ts′) ⁻¹) $
     <-+-lr {n = 1})
    (=→≤ refl)

app-lt-constraints : ∀ {c a s ts ts′ lc}
                   → length ts ＝ length ts′
                   → (c , a , zip ts ts′ ++ lc) <C (c , a , (con s ts , con s ts′) ∷ lc)
app-lt-constraints {s} e = inr (refl , app-lt-measure {s = s} e)

rem<C : ∀ {c a v xs ys} → v ∈ c → (rem v c , a , xs) <C (c , a , ys)
rem<C vi = inl (rem-size-neg vi)

-- main algorithm

unify-type : Constrs → 𝒰
unify-type (ctx , ar , lc) =
  wf-constr-list ctx lc → wa-constr-list ar lc →
  (Σ[ s ꞉ SubT ]
     (Wf-subst ctx (to-sub s) × Max↦ (unifier lc) (to-sub s)))
  ⊎ UnifyFailure lc

unify-body : (l : Constrs)
           → (ih : (l' : Constrs) → l' <C l → unify-type l')
           → unify-type l
unify-body (ctx , ar , [])                             ih _  _    = inl ([] , wf-idsub , [] , (λ f′ _ → ≤↦-id {f = f′}))
unify-body (ctx , ar , (tl         , tr)         ∷ lc) ih wcl wal with tl ≟ tr
unify-body (ctx , ar , (tl         , tr)         ∷ lc) ih wcl wal | yes e with ih (ctx , ar , lc)
                                                                                  (lt-list-constr-lt-constraints {t = tl} {t′ = tr} {a = ar} {l = lc})
                                                                                  (all-tail wcl)
                                                                                  (all-tail wal)
unify-body (ctx , ar , (tl         , tr)         ∷ lc) ih wcl wal | yes e | inl (su , wsu , mx) =
  inl (su , wsu , (Max↦≃ (unifier-eq e) (to-sub su) $ mx))
unify-body (ctx , ar , (tl         , tr)         ∷ lc) ih wcl wal | yes e | inr uf = inr (constr-rec uf)
unify-body (ctx , ar , (`` v       , tr)         ∷ lc) ih wcl wal | no ne with occurs-dec {v} {t = tr}
unify-body (ctx , ar , (`` v       , tr)         ∷ lc) ih wcl wal | no ne | yes oc = inr (occ-fail-l (ne ∘ _⁻¹) oc)
unify-body (ctx , ar , (`` v       , tr)         ∷ lc) ih wcl wal | no ne | no noc with ih (rem v ctx , ar , (v ≔ tr) $↦L lc)
                                                                                           (rem<C {a = ar} {xs = (v ≔ tr) $↦L lc} {ys = (`` v , tr) ∷ lc}
                                                                                              (wf-tm-var (all-head wcl .fst)))
                                                                                           (wf-constr-list-remove (wf-tm-var (all-head wcl .fst))
                                                                                                                  noc (all-head wcl .snd) (all-tail wcl))
                                                                                           (wa-constr-list-≔ (all-head wal .snd) (all-tail wal))
unify-body (ctx , ar , (`` v       , tr)         ∷ lc) ih wcl wal | no ne | no noc | inl (su , wsu , mx) =
  inl ( (v , tr) ∷ su
      , wf-sub-insert {su = su} (occurs-wf-tm (all-head wcl .snd) noc) (wf-tm-var (all-head wcl .fst)) wsu
      , (Max↦≃
           (λ f →   ↦𝒫◇-id≃ {p = ↦𝒫× (unifies (`` v) tr) (unifier lc) } f
                  ∙ all-×≃ {P = λ where (x , y) → unifies x y f} ⁻¹)
           (to-sub su ◇ (v ≔ tr)) $
           optimist-lemma {p = unifies (`` v) tr} {q = unifier lc} {a = id↦}
                          {f = v ≔ tr} {g = to-sub su}
              (DCl-unifies {t = tr})
              (Max↦≃ (_⁻¹ ∘ ↦𝒫◇-id≃ {p = unifies (`` v) tr}) (v ≔ tr) $
               max-flex-rigid noc)
              (↦thin-unifier {xs = lc})
              (subst (λ q → Max↦ (↦𝒫◇ (unifier lc) q) (to-sub su))
                     (◇-id-r {s = v ≔ tr} ⁻¹) $
               Max↦≃ (λ s → unifier-append≃) (to-sub su) $ mx))
       )
unify-body (ctx , ar , (`` v       , tr)         ∷ lc) ih wcl wal | no ne | no noc | inr uf = inr (subs-rec-l uf)
unify-body (ctx , ar , (con sl tsl , con sr tsr) ∷ lc) ih wcl wal | no ne with sl ≟ sr
unify-body (ctx , ar , (con sl tsl , con sr tsr) ∷ lc) ih wcl wal | no ne | yes se with ih (ctx , ar , zip tsl tsr ++ lc)
                                                                                           (app-lt-constraints {a = ar} {s = sl}
                                                                                              (  wa-tm-con (all-head wal .fst) .fst ⁻¹
                                                                                               ∙ ap ar se
                                                                                               ∙ wa-tm-con (all-head wal .snd) .fst))
                                                                                           (all-++
                                                                                              (all→zip (wf-tm-con (all-head wcl .fst)) ((wf-tm-con (all-head wcl .snd))))
                                                                                              (all-tail wcl))
                                                                                           (all-++
                                                                                              (all→zip (wa-tm-con (all-head wal .fst) .snd) (wa-tm-con (all-head wal .snd) .snd))
                                                                                              (all-tail wal))
unify-body (ctx , ar , (con sl tsl , con sr tsr) ∷ lc) ih wcl wal | no ne | yes se | inl (su , wsu , mx) =
  inl (su , wsu ,
        (Max↦≃
           (λ s → unifier-con≃ se (  wa-tm-con (all-head wal .fst) .fst ⁻¹
                                   ∙ ap ar se
                                   ∙ wa-tm-con (all-head wal .snd) .fst) s ⁻¹)
           (to-sub su) $
           mx))
unify-body (ctx , ar , (con sl tsl , con sr tsr) ∷ lc) ih wcl wal | no ne | yes se | inr uf =
  inr (con-con-rec se (  wa-tm-con (all-head wal .fst) .fst ⁻¹
                       ∙ ap ar se
                       ∙ wa-tm-con (all-head wal .snd) .fst) uf)
unify-body (ctx , ar , (con sl tsl , con sr tsr) ∷ lc) ih wcl wal | no ne | no nse = inr (con-con-sym nse)

unify-body (ctx , ar , (tl         , `` v)       ∷ lc) ih wcl wal | no ne with occurs-dec {v} {t = tl}
unify-body (ctx , ar , (tl         , `` v)       ∷ lc) ih wcl wal | no ne | yes oc = inr (occ-fail-r ne oc)
unify-body (ctx , ar , (tl         , `` v)       ∷ lc) ih wcl wal | no ne | no noc with ih (rem v ctx , ar , (v ≔ tl) $↦L lc)
                                                                                           (rem<C {a = ar} {xs = (v ≔ tl) $↦L lc} {ys = (tl , `` v) ∷ lc}
                                                                                              (wf-tm-var (all-head wcl .snd)))
                                                                                           (wf-constr-list-remove (wf-tm-var (all-head wcl .snd)) noc (all-head wcl .fst) (all-tail wcl))
                                                                                           (wa-constr-list-≔ (all-head wal .fst) (all-tail wal))
unify-body (ctx , ar , (tl         , `` v)       ∷ lc) ih wcl wal | no ne | no noc | inl (su , wsu , mx) =
  inl ( (v , tl) ∷ su
      , wf-sub-insert {su = su} (occurs-wf-tm (all-head wcl .fst) noc) (wf-tm-var (all-head wcl .snd)) wsu
      , (Max↦≃
           (λ f →   ↦𝒫◇-id≃ {p = ↦𝒫× (unifies tl (`` v)) (unifier lc) } f
                  ∙ all-×≃ {P = λ where (x , y) → unifies x y f} ⁻¹)
           (to-sub su ◇ (v ≔ tl)) $
           optimist-lemma {p = unifies tl (`` v)} {q = unifier lc} {a = id↦}
                           {f = v ≔ tl} {g = to-sub su}
                           (DCl-unifies {s = tl})
                           (Max↦≃ (λ s → unifies-swap {t = tl} s ∙ (↦𝒫◇-id≃ {p = unifies tl (`` v)} s) ⁻¹)
                                  (v ≔ tl) $
                            max-flex-rigid noc)
                           (↦thin-unifier {xs = lc})
                           (subst (λ q → Max↦ (↦𝒫◇ (unifier lc) q) (to-sub su))
                                  (◇-id-r {s = v ≔ tl} ⁻¹) $
                            Max↦≃ (λ s → unifier-append≃) (to-sub su) $ mx))
      )
unify-body (ctx , ar , (tl         , `` v)       ∷ lc) ih wcl wal | no ne | no noc | inr uf = inr (subs-rec-r uf)

unify : (l : Constrs) → unify-type l
unify = to-induction <C-wf unify-type unify-body
