{-# OPTIONS --safe #-}
module Nominal.Cofinite.Unify where

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
open import LFSet.Mem

open import Nominal.Ty
open import Nominal.Cofinite.Base
open import Nominal.Cofinite.Sub

-- unifier

unifies : Ty → Ty → ↦𝒫
unifies x y s = s $↦ x ＝ s $↦ y

unifies-swap : {s t : Ty} → ↦𝒫≃ (unifies s t) (unifies t s)
unifies-swap {s} {t} f = prop-extₑ! _⁻¹ _⁻¹

↦thin-unifies : {s t : Ty} → ↦thin (unifies s t)
↦thin-unifies {s} {t} f w u =
  thin-$↦ {xs = w} {t = s} ∙ u ∙ thin-$↦ {xs = w} {t = t} ⁻¹

thin↦-unifies : {s t : Ty} → thin↦ (unifies s t)
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
    (thin↦-unifies {s = s} {t = t} f fgw $
     subst (unifies s t) fge $
     (  sub-◇ {s1 = fg} {s2 = g} {t = s}
      ∙ ap (fg $↦_) u
      ∙ sub-◇ {s1 = fg} {s2 = g} {t = t} ⁻¹))

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

unify-ty : ∀ {v t′ s} t
         → unifies (`` v) t′ s
         → unifies t ((v ≔ t′) $↦ t) s
unify-ty {v} {t′} {s} (`` x)    ea =
  Dec.elim
    {C = λ q → (s $ x) ＝ (s $↦ (if ⌊ q ⌋ then t′ else (`` x)))}
    (λ evx → ap (s $_) (evx ⁻¹) ∙ ea)
    (λ _ → refl)
    (v ≟ x)
unify-ty         {s} (p ⟶ q) ea =
  ap² _⟶_ (unify-ty {s = s} p ea) (unify-ty {s = s} q ea)
unify-ty              con      ea = refl

unifier-subs : ∀ {v t s} l
              → unifies (`` v) t s
              → unifier l s
              → unifier ((v ≔ t) $↦L l) s
unifier-subs     []              ea       u  = []
unifier-subs {s} ((tl , tr) ∷ l) ea (et ∷ u) =
  unify-ty {s = s} tl ea ⁻¹ ∙ et ∙ unify-ty {s = s} tr ea ∷ unifier-subs {s = s} l ea u

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
                   {C = λ q → f′ $↦ (if ⌊ q ⌋ then t else  `` x) ＝ (f′ $ x)}
                   (λ e → u′ ⁻¹ ∙ ap (f′ $_) e)
                   (λ _ → refl)
                   (v ≟ x))
           refl)

no-unify-+var : ∀ {x : Id} {p ps}
              → ↦𝒫∅ (unifies (`` x) ((p ∷ ps) +: (`` x)))
no-unify-+var {p} {ps} f u =
  false! $ no-cycle-lemma ((u ∙ +:-subst {f = f} {ps = p ∷ ps}) ⁻¹)

-- computational substitution

SubC : 𝒰
SubC = List (Id × Ty)

to-sub : SubC → Sub
to-sub = List.rec id↦ (λ where (x , t) → _◇ (x ≔ t))

wf-sub-insert : ∀ {ctx su v t}
              → wf-ty (rem v ctx) t
              → v ∈ ctx
              → Wf-subst (rem v ctx) (to-sub su)
              → Wf-subst ctx (to-sub ((v , t) ∷ su))
wf-sub-insert {ctx} {su} {v} {t} wr vin wf {x} xin =
  caseᵈ v ＝ x of
    λ where
       (yes v=x) →
           subst (_∈ ctx) v=x vin
         , (given-yes v=x
              return (λ q → wf-ty (minus ctx (v ∷ to-sub su .dom))
                                  (to-sub su $↦ (if ⌊ q ⌋ then t else `` x)))
              then subst (λ q → wf-ty q (to-sub su $↦ t))
                         (minus-rem-l ∙ minus-∷-r ⁻¹)
                         (substs-remove wf wr))
       (no v≠x) →
            Recomputable-×
             Recomputable-∈ₛ (wf-ty-recomp {t = to-sub ((v , t) ∷ su) $ x})
             .recompute $
               erase
                (elim! {P = λ _ → (x ∈ₛ ctx)
                                    ×ₜ wf-ty (minus ctx (v ∷ to-sub su .dom))
                                             (to-sub ((v , t) ∷ su) $ x)}
                   [ (λ e → absurd (v≠x (e ⁻¹)))
                   , (λ x∈′ → let (x∈r , wtx) = wf (⇉∈ₛ $ erase x∈′) in
                                 rem-⊆ x∈r
                               , (given-no v≠x
                             return (λ q → wf-ty (minus ctx (v ∷ to-sub su .dom))
                                                 (to-sub su $↦ (if ⌊ q ⌋ then t else `` x)))
                             then subst (λ q → wf-ty q (to-sub su $ x))
                                        (minus-rem-l ∙ minus-∷-r ⁻¹)
                                        wtx))
                   ]ᵤ (∈ₛ⇉ xin .erased))

-- failure

data UnifyFailure : List Constr → 𝒰 where
  occ-fail-l : ∀ {v t lc}
             → t ≠ `` v → occurs v t
             → UnifyFailure ((`` v , t) ∷ lc)
  occ-fail-r : ∀ {v t lc}
             → t ≠ `` v → occurs v t
             → UnifyFailure ((t , `` v) ∷ lc)
  con-app    : ∀ {l r lc}
             → UnifyFailure ((con , l ⟶ r) ∷ lc)
  app-con    : ∀ {l r lc}
             → UnifyFailure ((l ⟶ r , con) ∷ lc)
  arr-arr    : ∀ {l l' r r' lc}
             → UnifyFailure ((l , l') ∷ (r , r') ∷ lc) → UnifyFailure ((l ⟶ r , l' ⟶ r') ∷ lc)
  constr-rec : ∀ {t t' l}
             → UnifyFailure l → UnifyFailure ((t , t') ∷ l)
  subs-rec-l : ∀ {v t l}
             → UnifyFailure ((v ≔ t) $↦L l) → UnifyFailure ((`` v , t) ∷ l)
  subs-rec-r : ∀ {v t l}
             → UnifyFailure ((v ≔ t) $↦L l) → UnifyFailure ((t , `` v) ∷ l)

failure→no-unifier : ∀ {lc} → UnifyFailure lc → ↦𝒫∅ (unifier lc)
failure→no-unifier (occ-fail-l {t} ne oc) s u with occ→ctx {t = t} oc
... | []    , e = ne e
... | p ∷ c , e = no-unify-+var {p = p} s (all-head u ∙ ap (s $↦_) e)
failure→no-unifier (occ-fail-r {t} ne oc) s u with occ→ctx {t = t} oc
... | []    , e = ne e
... | p ∷ c , e = no-unify-+var {p = p} s (all-head u ⁻¹ ∙ ap (s $↦_) e)
failure→no-unifier  con-app        s u = ⟶≠con (all-head u ⁻¹)
failure→no-unifier  app-con        s u = ⟶≠con (all-head u)
failure→no-unifier (arr-arr uf)    s u =
  failure→no-unifier uf s (unifier-⟶≃ s $ u)
failure→no-unifier (constr-rec uf) s u =
  failure→no-unifier uf s (all-tail u)
failure→no-unifier (subs-rec-l {l} uf) s u =
  failure→no-unifier uf s (unifier-subs l (all-head u) (all-tail u))
failure→no-unifier (subs-rec-r {l} uf) s u =
  failure→no-unifier uf s (unifier-subs l (all-head u ⁻¹) (all-tail u))

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

lt-list-constr-lt-measure : ∀ {t t′ l} → list-measure l < list-measure ((t , t′) ∷ l)
lt-list-constr-lt-measure {t} = <-+-0lr $ <-+-r $ 0<ty-size {t = t}

lt-list-constr-lt-constraints : ∀ {t t′ c l} → (c , l) <C (c , (t , t′) ∷ l)
lt-list-constr-lt-constraints {t} {t′} {l} =
  inr (refl , lt-list-constr-lt-measure {t = t} {t′ = t′} {l = l})

app-lt-measure : ∀ {l l′ r r′ lc}
               → list-measure ((l , l′) ∷ (r , r′) ∷ lc) < list-measure ((l ⟶ r , l′ ⟶ r′) ∷ lc)
app-lt-measure {l} {l′} {r} {r′} {lc} =
  subst (_< list-measure ((l ⟶ r , l′ ⟶ r′) ∷ lc))
        (+-assoc (ty-size l + ty-size l′) (ty-size r + ty-size r′) (list-measure lc) ⁻¹) $
  <-≤-+ {m = ty-size l + ty-size l′ + (ty-size r + ty-size r′)}
    (subst (λ q → ty-size l + ty-size l′ + (ty-size r + ty-size r′) < suc q)
           (+-suc-r (ty-size l + ty-size r) (ty-size l′ + ty-size r′) ⁻¹) $
     subst (λ q → ty-size l + ty-size l′ + (ty-size r + ty-size r′) < suc (suc q))
           (+-interchange (ty-size l) (ty-size l′) (ty-size r) (ty-size r′)) $
     <-+-lr {n = 1})
    (=→≤ refl)

app-lt-constraints : ∀ {l l′ r r′ lc c}
                   → (c , (l , l′) ∷ (r , r′) ∷ lc) <C (c , (l ⟶ r , l′ ⟶ r′) ∷ lc)
app-lt-constraints {l} {l′} {r} {r′} {lc} =
  inr (refl , app-lt-measure {l = l} {l′ = l′} {r = r} {r′ = r′} {lc = lc})

opaque
  unfolding rem
  rem<C : ∀ {c v xs ys} → v ∈ c → (rem v c , xs) <C (c , ys)
  rem<C {v} vi =
    inl (filter-size-neg (not-so $ ¬so≃is-false ⁻¹ $ ap not (so≃is-true $ true→so! (the (v ＝ v) refl))) vi)

-- main algorithm

unify-type : Constrs → 𝒰
unify-type (ctx , lc) =
  wf-constr-list ctx lc →
  (Σ[ s ꞉ SubC ]
     (Wf-subst ctx (to-sub s) × Max↦ (unifier lc) (to-sub s)))
  ⊎ UnifyFailure lc

unify-body : (l : Constrs)
           → (ih : (l' : Constrs) → l' <C l → unify-type l')
           → unify-type l
unify-body (ctx , [])                         ih _   = inl ([] , wf-idsub , [] , (λ f′ _ → ≤↦-id {f = f′}))
unify-body (ctx , (tl , tr) ∷ lc) ih wcl with tl ≟ tr
unify-body (ctx , (tl , tr) ∷ lc) ih wcl | yes e with ih (ctx , lc)
                                                         (lt-list-constr-lt-constraints {t = tl} {t′ = tr} {l = lc})
                                                         (all-tail wcl)
unify-body (ctx , (tl , tr) ∷ lc) ih wcl | yes e | inl (su , wsu , mx) =
  inl ( su , wsu
      , (Max↦≃ (unifier-eq e) (to-sub su) $ mx))
unify-body (ctx , (tl , tr) ∷ lc) ih wcl | yes e | inr uf = inr (constr-rec uf)
unify-body (ctx , (`` v      , tr)        ∷ lc) ih wcl | no ne with occurs-dec {v} {t = tr}
unify-body (ctx , (`` v      , tr)        ∷ lc) ih wcl | no ne | yes oc = inr (occ-fail-l (ne ∘ _⁻¹) oc)
unify-body (ctx , (`` v      , tr)        ∷ lc) ih wcl | no ne | no noc with ih (rem v ctx , (v ≔ tr) $↦L lc)
                                                                                (rem<C
                                                                                   {xs = (v ≔ tr) $↦L lc} {ys = (`` v , tr) ∷ lc}
                                                                                   (wf-ty-var (all-head wcl .fst)))
                                                                                (wf-constr-list-remove (wf-ty-var (all-head wcl .fst))
                                                                                                       noc (all-head wcl .snd) (all-tail wcl))
unify-body (ctx , (`` v      , tr)        ∷ lc) ih wcl | no ne | no noc | inl (su , wsu , mx) =
  inl ( (v , tr) ∷ su
      , wf-sub-insert {su = su} (occurs-wf-ty (all-head wcl .snd) noc) (wf-ty-var (all-head wcl .fst)) wsu
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
               Max↦≃ (λ s → unifier-append≃) (to-sub su) $ mx)
               )
       )
unify-body (ctx , (`` v      , tr)        ∷ lc) ih wcl | no ne | no noc | inr uf = inr (subs-rec-l uf)
unify-body (ctx , (pl ⟶ ql , pr ⟶ qr)  ∷ lc) ih wcl | no ne with ih (ctx , (pl , pr) ∷ (ql , qr) ∷ lc)
                                                                       (app-lt-constraints {l = pl} {l′ = pr} {r = ql} {r′ = qr} {lc = lc})
                                                                       (  (wf-ty-arr (all-head wcl .fst) .fst , wf-ty-arr (all-head wcl .snd) .fst)
                                                                        ∷ (wf-ty-arr (all-head wcl .fst) .snd , wf-ty-arr (all-head wcl .snd) .snd)
                                                                        ∷ all-tail wcl)
unify-body (ctx , (pl ⟶ ql , pr ⟶ qr)  ∷ lc) ih wcl | no ne | inl (su , wsu , mx) =
  inl ( su
      , wsu
      , (Max↦≃
           (λ s → (unifier-⟶≃ s) ⁻¹)
           (to-sub su) $
           mx)
      )
unify-body (ctx , (pl ⟶ ql , pr ⟶ qr)  ∷ lc) ih wcl | no ne | inr uf = inr (arr-arr uf)
unify-body (ctx , (pl ⟶ ql , con)       ∷ lc) ih wcl | no ne = inr app-con
unify-body (ctx , (con       , pr ⟶ qr) ∷ lc) ih wcl | no ne = inr con-app
unify-body (ctx , (con       , con)       ∷ lc) ih wcl | no ne = absurd (ne refl)
unify-body (ctx , (tl        , `` v)      ∷ lc) ih wcl | no ne with occurs-dec {v} {t = tl}
unify-body (ctx , (tl        , `` v)      ∷ lc) ih wcl | no ne | yes oc = inr (occ-fail-r ne oc)
unify-body (ctx , (tl        , `` v)      ∷ lc) ih wcl | no ne | no noc with ih (rem v ctx , (v ≔ tl) $↦L lc)
                                                                                (rem<C
                                                                                   {xs = (v ≔ tl) $↦L lc} {ys = (tl , `` v) ∷ lc}
                                                                                   (wf-ty-var (all-head wcl .snd))
                                                                                   )
                                                                                (wf-constr-list-remove (wf-ty-var (all-head wcl .snd)) noc (all-head wcl .fst) (all-tail wcl))
unify-body (ctx , (tl        , `` v)      ∷ lc) ih wcl | no ne | no noc | inl (su , wsu , mx) =
  inl ((v , tl) ∷ su
      , wf-sub-insert {su = su} (occurs-wf-ty (all-head wcl .fst) noc) (wf-ty-var (all-head wcl .snd)) wsu
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
unify-body (ctx , (tl        , `` v)      ∷ lc) ih wcl | no ne | no noc | inr uf = inr (subs-rec-r uf)

unify : (l : Constrs) → unify-type l
unify = to-induction <C-wf unify-type unify-body

