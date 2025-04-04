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

-- inverse sequence substitution

$q←-rec : ∀ {n} → (s : ISubq n) → Rec-un n Id (s #_) (λ n → Vec Term n)
$q←-rec {n = zero}  _ .ru[] _     = []
$q←-rec {n = suc n} _ .ru[] e     = false! e
$q←-rec {n}         _ .ruf  x _   = replicate n (`` x)
$q←-rec             _ .runj ps qs = couple ps qs
$q←-rec             _ .runn ts    = ts

_$q←_ : ∀ {n} → ISubq n → Vec Term n → Vec Term n
s $q← ts = rec-un ($q←-rec s) ts

$q←-[] : {s : ISubq 0} → s $q← [] ＝ []
$q←-[] = subst-refl {A = ℕ} {B = λ n → Vec Term n} {x = 0} []

$q←-sj : ∀ {n}
       → {s : ISubq n} {ts : Vec Term n} {x : Id}
       → s # ts ＝ just x
       → s $q← ts ＝ replicate n (`` x)
$q←-sj {n = zero}  {s} {ts} sj =
  ap {x = ts} (s $q←_) size0-nil ∙ $q←-[] {s = s}
$q←-sj {n = suc n} {s} {ts} sj =
  elim-un-step-fj hlevel! (rec→elim→-un ($q←-rec s)) sj

$q←-ucj : ∀ {n}
        → {s : ISubq n} {ts ps qs : Vec Term n}
        → s # ts ＝ nothing
        → uncouple ts ＝ just (ps , qs)
        → s $q← ts ＝ couple (s $q← ps) (s $q← qs)
$q←-ucj {n = zero}  {s} {ts = []} {ps = []} {qs = []} sn uj =
  $q←-[] {s = s} ∙ ap² couple ($q←-[] {s = s} ⁻¹) ($q←-[] {s = s} ⁻¹)
$q←-ucj {n = suc n} {s} {ts}      {ps}      {qs}      sn uj =
  elim-un-step-uj hlevel! (rec→elim→-un ($q←-rec s)) sn uj

$q←-un : ∀ {n}
       → {s : ISubq n} {ts : Vec Term n}
       → s # ts ＝ nothing
       → uncouple ts ＝ nothing
       → s $q← ts ＝ ts
$q←-un {n = zero}      {ts = []} sn un = false! un
$q←-un {n = suc n} {s} {ts}      sn un =
  elim-un-step-un hlevel! (rec→elim→-un ($q←-rec s)) sn un

-- properties

-- NB: injectivity of s not needed!
invq-$q←-$q↦ : ∀ {n} {s : Subq n} {ts}
             → ((x : Id) → x ∈ bindₛ vars (from-vec ts) → x ∈ s .domq → ⊥)
             → s $q↦ (inv-subq s $q← ts) ＝ ts
invq-$q←-$q↦ {s} {ts} vd = elim-un go ts vd
  where
  go : ∀ {n} → {s : Subq n}
             → Elim-un Id (inv-subq s #_)
                 λ q → ((x : Id) → x ∈ bindₛ vars (from-vec q) → x ∈ s .domq → ⊥)
                     → s $q↦ (inv-subq s $q← q) ＝ q
  go {n = zero}  {s} .eu[] {ts} e vd                             =
      ap {x = ts} (λ q → s $q↦ (inv-subq s $q← q)) size0-nil
    ∙ ap (s $q↦_) ($q←-[] {s = inv-subq s})
    ∙ $q↦-[] {s = s}
    ∙ size0-nil ⁻¹
  go {n = suc n}     .eu[] e = false! e
  go             {s} .euf {ts} lt invj vd                      =
      ap (s $q↦_) ($q←-sj invj)
    ∙ $q↦-``
    ∙ inv-fun-just {sq = s} invj .snd
  go             {s} .eunj {ps} {qs} {ts} lt invn uj ihp ihq vd  =
    let ce = couple-uncouple {ts = ts} uj in
      ap (s $q↦_) ($q←-ucj invn uj)
    ∙ $q↦-ucj (unrepvar-couple {xs = inv-subq s $q← ps}) uncouple-couple
    ∙ ap² couple
          (ihp λ x x∈p x∈s →
             rec!
               (λ y y∈ x∈ →
                   let (z , z∈ , yz∈) = ∈-zip-with-l {f = _⟶_} {as = ps} {bs = qs}
                                            (vec-∈ {xs = ps} y∈)
                     in
                   vd x (∈-bind {y = y ⟶ z}
                           (∈-vec {xs = ts} (subst ((y ⟶ z) ∈_) ce yz∈))
                           (∈ₛ-∪∷←l x∈))
                      x∈s)
               (bind-∈ x∈p))
          (ihq λ x x∈q x∈s →
             rec!
               (λ y y∈ x∈ →
                   let (z , z∈ , yz∈) = ∈-zip-with-r {f = _⟶_} {as = ps} {bs = qs}
                                            (vec-∈ {xs = qs} y∈)
                     in
                   vd x (∈-bind {y = z ⟶ y}
                           (∈-vec {xs = ts} (subst ((z ⟶ y) ∈_) ce yz∈))
                           (∈ₛ-∪∷←r {s₁ = vars z} x∈))
                      x∈s)
               (bind-∈ x∈q))
    ∙ couple-uncouple uj
  go {n}         {s} .eunn {ts} lt invn un     vd              =
    let sz0 = uncouple-nothing-size {ts = ts} un in
      ap (s $q↦_) ($q←-un invn un)
    ∙ Maybe.elim
        (λ q → unrepvar ts ＝ q → s $q↦ ts ＝ ts)
        (λ urvn → $q↦-un urvn un)
        (λ x urvj →
           let tse = unrepvar-just-eq {ts = ts} urvj in
             ap (s $q↦_) tse
           ∙ $q↦-``
           ∙ s .cofq (vd x (subst (λ q → x ∈ₛ bindₛ vars (from-vec q))
                                  (tse ⁻¹) $
                            subst (λ q → x ∈ₛ bindₛ vars q)
                                  (from-vec-replicate-0< sz0 ⁻¹) $
                            subst (x ∈ₛ_)
                                  (bindₛ-sng ⁻¹) $
                           hereₛ refl))
           ∙ tse ⁻¹)
        (unrepvar ts)
        refl
