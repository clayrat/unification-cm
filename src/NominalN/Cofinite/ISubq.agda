{-# OPTIONS --safe #-}
module NominalN.Cofinite.ISubq where

open import Prelude
open import Foundations.Sigma
open import Meta.Effect

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Maybe as Maybe
open import Data.Maybe.Instances.Map.Properties
open import Data.Sum as ⊎
open import Data.Vec.Inductive as Vec
open import Data.Vec.Inductive.Correspondences.Unary.All
open import Data.Vec.Inductive.Operations.Properties

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

open import Id
open import NominalN.Term
open import NominalN.Cofinite.BaseA
open import NominalN.Cofinite.Subq

-- inverse sequence substitution as a cofinitely quantified map

record ISubq (n : ℕ) : 𝒰 where
  constructor is-isubq
  field
    ifunq : Vec Term n → Maybe Id
    idomq : LFSet (Vec Term n)
    icofq : ∀ {xs} → xs ∉ idomq → ifunq xs ＝ nothing

open ISubq public

unquoteDecl ISubq-Iso = declare-record-iso ISubq-Iso (quote ISubq)
unquoteDecl H-Level-ISubq = declare-record-hlevel 2 H-Level-ISubq (quote ISubq)

instance
  Funlike-ISubq : ∀ {n} → Funlike ur (ISubq n) (Vec Term n) (λ _ → Maybe Id)
  Funlike-ISubq ._#_ = ifunq

isq-just-∈ : ∀ {n} {isq : ISubq n} {xs x}
           → isq .ifunq xs ＝ just x → xs ∈ isq .idomq
isq-just-∈ {isq} ej =
  dec→essentially-classical Dec-∈ₛ
    λ xs∉ → false! $ ej ⁻¹ ∙ isq .icofq xs∉

-- applying as relation
data _$q←_⇒_ : ∀ {n} → ISubq n → Vec Term n → Vec Term n → 𝒰 where
  $q←-∈  : ∀ {n s ts x}
          → s .ifunq ts ＝ just x
          → s $q← ts ⇒ replicate n (`` x)
  $q←-⟶ : ∀ {n s ps qs xs ys} {ts : Vec Term n}
          → s .ifunq ts ＝ nothing
          → uncouple ts ＝ just (ps , qs)  -- TODO couple ps qs ＝ ts ?
          → s $q← ps ⇒ xs
          → s $q← qs ⇒ ys
          → s $q← ts ⇒ couple xs ys
  $q←-def : ∀ {n s} {ts : Vec Term n}
          → s .ifunq ts ＝ nothing
          → uncouple ts ＝ nothing
          → s $q← ts ⇒ ts

-- TODO isubq-ext

empiq : (n : ℕ) → ISubq n
empiq n .ifunq _ = nothing
empiq n .idomq = []
empiq n .icofq _ = refl

-- TODO pull out filter+graph
filt-graph-∈ : ∀ {n} {sq : Subq n} {ts}
              → Injective (sq .funq)
              → ts ∈ codomq sq
              → ∃[ x ꞉ Id ] (filterₛ (λ q → ts =? q .snd) (graphq sq) ＝ sng (x , ts)) × (sq # x ＝ ts)
filt-graph-∈ {sq} {ts} inj ts∈ =
  map
    (λ where (x , xt∈) →
               let (x∈ , sxe) = ∈-graphq {sq = sq} xt∈ in
                 x
               , filter-sng
                     (true→so! ⦃ (Vec-is-discrete {x = ts} .proof) ⦄ refl)
                     xt∈
                     (λ {x = z} z∈ zeb →
                       let ze = so→true! ⦃ (Vec-is-discrete {x = ts} .proof) ⦄ zeb ⁻¹ in
                       rec!
                        (λ y y∈ ye →
                           ×-path (ap fst ye ∙ inj (ap snd ye ⁻¹ ∙ ze ∙ sxe ⁻¹)) ze)
                        (mapₛ-∈ z∈))
               , sxe)
    (∈-codom-graph {sq = sq} ts∈)

filt-graph-∉ : ∀ {n} {sq : Subq n} {ts}
              → ts ∉ codomq sq
              → filterₛ (λ q → ts =? q .snd) (graphq sq) ＝ []
filt-graph-∉ {sq} {ts} ts∉ =
  filter-none
    (λ {(x , qs)} xqs∈ →
       let (x∈ , sqe) = ∈-graphq {sq = sq} xqs∈ in
       false→so! ⦃ (Vec-is-discrete {x = ts} .proof) ⦄
         (contra (λ tse → codom-∈ {sq = sq} (sqe ∙ tse ⁻¹) x∈) ts∉))

inj-size-graph : ∀ {n} {sq : Subq n} {ts}
               → Injective (sq .funq)
               → sizeₛ (filterₛ (λ q → ts =? q .snd) (graphq sq)) ≤ 1
inj-size-graph {sq} {ts} inj with ts ∈? codomq sq
... | yes ts∈ =
  rec!
    (λ x fe eq → =→≤ (ap sizeₛ fe ∙ size-sng))
    (filt-graph-∈ {sq = sq} inj ts∈)
... | no ts∉ =
  subst (_≤ 1) (size-[] ⁻¹ ∙ ap sizeₛ (filt-graph-∉ {sq = sq} ts∉ ⁻¹)) z≤

-- build the whole graph and look up the term
inv-fun : ∀ {n} → Subq n → Vec Term n → Maybe Id
inv-fun sq ts = map fst (extract1 (filterₛ (λ q → ts =? q .snd) (graphq sq)))

inv-fun-just : ∀ {n} {sq : Subq n} {ts x}
             → inv-fun sq ts ＝ just x
             → x ∈ sq .domq × (sq # x ＝ ts)
inv-fun-just {sq} {x} e =
  let ((y , qs) , (e′ , y=x)) = mapₘ=just e
      xqs∈′ = subst ((x , qs) ∈_) (extract1-just e′ ⁻¹) (hereₛ (×-path (y=x ⁻¹) refl))
      (tse , xqs∈) = filter-∈ₛ xqs∈′
    in
    ∈-graphq {x = x} {sq = sq} $
    subst (λ q → (x , q) ∈ₛ graphq sq)
          (so→true! tse ⁻¹)
          xqs∈

just-inv-fun : ∀ {n} {sq : Subq n} {x}
             → Injective (sq .funq)
             → x ∈ sq .domq
             → inv-fun sq (sq # x) ＝ just x
just-inv-fun {sq} inj x∈ =
  rec!
    (λ y fe eq → ap (mapₘ fst) (ap extract1 fe ∙ extract1-x∷) ∙ ap just (inj eq))
    (filt-graph-∈ {sq = sq} inj (codom-∈ {sq = sq} refl x∈))

inv-fun-inj-nothing : ∀ {n} {sq : Subq n} {ts}
                    → Injective (sq .funq)
                    → inv-fun sq ts ＝ nothing
                    → {x : Id} → x ∈ sq .domq → sq # x ≠ ts    -- ~ ts ∉ codom sq
inv-fun-inj-nothing {sq} {ts} inj e {x} x∈ sqx =
  rec!
    [ (λ f0 → so-not
                 (none-filter f0 {z = x , ts} $
                  graphq-∈ {sq = sq} x∈ sqx)
                 (true→so! ⦃ (Vec-is-discrete {x = ts} .proof) ⦄ -- wtf
                    refl))
    , (λ f2 → <→≱ f2 (inj-size-graph {sq = sq} {ts = ts} inj))
    ]ᵤ
    (extract1-nothing $ mapₘ=nothing e)

nothing-inv-fun : ∀ {n} {sq : Subq n} {ts}
                → ({x : Id} → x ∈ sq .domq → sq # x ≠ ts)    -- ~ ts ∉ codom sq
                → inv-fun sq ts ＝ nothing
nothing-inv-fun {sq} {ts} ne =
  ap (mapₘ fst) $
    ap extract1
       (filt-graph-∉ {sq = sq} {ts = ts}
          λ ts∈ → rec! (λ x xts∈ →
                            let (x∈ , xe) = ∈-graphq {sq = sq} xts∈ in
                            ne x∈ xe)
                        (∈-codom-graph {sq = sq} ts∈))
  ∙ extract1-[]

inv-subq : ∀ {n} → Subq n → ISubq n
inv-subq sq .ifunq ts = inv-fun sq ts
inv-subq sq .idomq = codomq sq
inv-subq sq .icofq {xs} xs∉ =
  ap (mapₘ fst) $
    ap extract1
       (filter-none
          λ where {x = v , ts} vx∈ →
                    false→so!
                       {P = xs ＝ ts}
                       (contra
                          (λ e →
                               let (v∈ , ve) = ∈-graphq {sq = sq} vx∈ in
                               subst (_∈ₛ codomq sq) (e ⁻¹) (codom-∈ {sq = sq} ve v∈))
                          xs∉))
  ∙ extract1-[]

invq-$q←-$q↦ : ∀ {n} {sq : Subq n} {ts zs}
             → Injective (sq .funq)
             → ((x : Id) → x ∈ bindₛ vars (from-vec ts) → x ∈ sq .domq → ⊥)
             → inv-subq sq $q← ts ⇒ zs
             → sq $q↦ zs ⇒ ts
invq-$q←-$q↦ {n} {sq} {ts}       _ _ ($q←-∈ {x} invj) =
  let (x∈ , e) = inv-fun-just {sq = sq} invj in
  subst (sq $q↦ replicate n (`` x) ⇒_) e $
  $q-``∈ refl x∈
invq-$q←-$q↦ {sq} {ts} {zs} si vd ($q←-⟶ {ps} {qs} {xs} {ys} invn uncj isqp isqq) =
  let ce = couple-uncouple uncj in
  subst (sq $q↦ couple xs ys ⇒_)
        ce $
  $q-⟶ uncouple-couple
    (invq-$q←-$q↦ si
              (λ x x∈ps x∈sq →
                   rec!
                     (λ y y∈ x∈ →
                         let (z , z∈ , yz∈) = ∈-zip-with-l {f = _⟶_} {as = ps} {bs = qs}
                                                  (vec-∈ {xs = ps} y∈)
                           in
                         vd x (∈-bind {y = y ⟶ z}
                                  (∈-vec {xs = ts} (subst ((y ⟶ z) ∈_) ce yz∈))
                                  (∈ₛ-∪∷←l x∈))
                               x∈sq)
                     (bind-∈ x∈ps))
              isqp)
    (invq-$q←-$q↦ si
              (λ x x∈qs x∈sq →
                    rec!
                      (λ y y∈ x∈ →
                         let (z , z∈ , yz∈) = ∈-zip-with-r {f = _⟶_} {as = ps} {bs = qs}
                                                  (vec-∈ {xs = qs} y∈)
                           in
                         vd x (∈-bind {y = z ⟶ y}
                                  (∈-vec {xs = ts} (subst ((z ⟶ y) ∈_) ce yz∈))
                                  (∈ₛ-∪∷←r {s₁ = vars z} x∈))
                               x∈sq)
                      (bind-∈ x∈qs))
              isqq)
invq-$q←-$q↦ {n} {sq} {ts} {zs} si vd ($q←-def invn uncn) =
  let sz0 = uncouple-nothing-size {ts = ts} uncn in
  Dec.rec
    (λ (t , te) →
        Dec.rec
            (λ (x , xe) →
                 Dec.rec
                    (λ x∈ → absurd (vd x (subst (λ q → x ∈ₛ bindₛ vars (from-vec q))
                                                 (te ⁻¹) $
                                           subst (λ q → x ∈ₛ bindₛ vars (from-vec (replicate n q)))
                                                 (xe ⁻¹) $
                                           subst (λ q → x ∈ₛ bindₛ vars q)
                                                 (from-vec-replicate-0< sz0 ⁻¹) $
                                           subst (x ∈ₛ_)
                                                 (bindₛ-sng ⁻¹) $
                                          hereₛ refl)
                                        x∈))
                    ($q-``∉ (te ∙ ap (replicate n) xe))
                    (x ∈? sq .domq))
            (λ nx →
                 $q-def
                         (λ x xe →
                              nx (x , ∷-head-inj
                                        (subst (λ q → replicate q t ＝ replicate q (`` x))
                                               (z<-suc-pred sz0)
                                               (te ⁻¹ ∙ xe)))) uncn)
            (Dec-unvar {t}))
    (λ nxe → $q-def (λ x xe → nxe ((`` x) , xe)) uncn)
    (Dec-unreplicate {ts = ts} sz0)

{-
invq-$q↦-$q← : ∀ {ts zs sq}
             → Injective (sq .funq)
             → ((x : Id) → x ∈ bindₛ vars (from-list ts) → x ∈ sq .domq → ⊥)
             → sq $q↦ zs ⇒ ts
             → inv-subq sq $q← ts ⇒ zs
invq-$q↦-$q← {sq} si vd ($q-``∈ {x} tse x∈)      =
  subst (inv-subq sq $q← sq # x ⇒_) (tse ⁻¹) $
  subst (λ q → inv-subq sq $q← sq # x ⇒ replicate q (`` x)) (sq .cohq x∈) $
  $q←-∈ (just-inv-fun {sq = sq} si x∈)
invq-$q↦-$q← {ts} {sq} si vd ($q-``∉ tse x∉)      =
  $q←-def
    (ap length tse ∙ length-replicate)
    {!!}
    {!!}
invq-$q↦-$q← {zs} {sq} si vd ($q-⟶ {xs} {ys} le uj pev qev) =
  let (ec , le′) = couple-uncouple {ts = zs} uj
      (ihp , ihx) = $q↦-length pev
      (ihq , ihy) = $q↦-length qev
    in
  subst (inv-subq sq $q← couple xs ys ⇒_) ec $
  $q←-⟶
    {!!}
    (uncouple-couple (ihx ∙ ihy ⁻¹))
    (invq-$q↦-$q← si {!!} pev)
    (invq-$q↦-$q← si {!!} qev)
invq-$q↦-$q← {ts} {sq} si vd ($q-def le nr un)     =
  $q←-def
    le
    {!!}
    un
-}
