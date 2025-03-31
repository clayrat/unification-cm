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

open import Data.List as List
open import Data.List.Correspondences.Unary.All
open import Data.List.Operations.Properties
open import Data.Sum as ⊎

open import Order.Constructions.Minmax
open import Order.Constructions.Nat
open import Order.Diagram.Meet
import Order.Diagram.Meet.Reasoning as MR

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

open import Id
open import NominalN.Term
open import NominalN.Cofinite.BaseA
open import NominalN.Cofinite.Subq

-- inverse sequence substitution as a cofinitely quantified map

record ISubq : 𝒰 where
  constructor is-isubq
  field
    ifunq : List Term → Maybe Id
    isizq : ℕ
    idomq : LFSet (List Term)
    idszq : ∀ {xs} → xs ∈ idomq → length xs ＝ isizq
    icofq : ∀ {xs} → xs ∉ idomq → ifunq xs ＝ nothing

open ISubq public

unquoteDecl ISubq-Iso = declare-record-iso ISubq-Iso (quote ISubq)
unquoteDecl H-Level-ISubq = declare-record-hlevel 2 H-Level-ISubq (quote ISubq)

instance
  Funlike-ISubq : Funlike ur ISubq (List Term) (λ _ → Maybe Id)
  Funlike-ISubq ._#_ = ifunq

isq-just-∈ : ∀ {isq xs x} → isq .ifunq xs ＝ just x → xs ∈ isq .idomq
isq-just-∈ {isq} ej =
  dec→essentially-classical Dec-∈ₛ
    λ xs∉ → false! $ ej ⁻¹ ∙ isq .icofq xs∉

-- applying as relation
data _$q←_⇒_ : ISubq → List Term → List Term → 𝒰 where
  $q←-∈  : ∀ {s ts x}
          → s .ifunq ts ＝ just x
          → s $q← ts ⇒ replicate (length ts) (`` x)
  $q←-⟶ : ∀ {s ts ps qs xs ys}
          → s .ifunq ts ＝ nothing
          → uncouple ts ＝ just (ps , qs)  -- TODO couple ps qs ＝ ts + length ps ＝ length qs ?
          → s $q← ps ⇒ xs
          → s $q← qs ⇒ ys
          → s $q← ts ⇒ couple xs ys
  $q←-def : ∀ {s ts}
          → length ts ＝ s .isizq
          → s .ifunq ts ＝ nothing
          → uncouple ts ＝ nothing
          → s $q← ts ⇒ ts

-- TODO isubq-ext

open decminmax ℕ-dec-total
open decminmaxprops ℕ-dec-total ℕ-dec-total

$q←⇒-length : ∀ {isq ts zs}
            → isq $q← zs ⇒ ts
            → (length zs ＝ isq .isizq) × (length ts ＝ isq .isizq)
$q←⇒-length {isq} ($q←-∈ ej)             =
  let e = isq .idszq (isq-just-∈ {isq = isq} ej) in
  e , length-replicate ∙ e
$q←⇒-length {zs}  ($q←-⟶ en uj pev qev) =
  let (ihp , ihx) = $q←⇒-length pev
      (ihq , ihy) = $q←⇒-length qev
    in
    ap length (couple-uncouple {ts = zs} uj .fst ⁻¹) ∙ zip-with-length ∙ ap² min ihp ihq ∙ MR.∩-idem ℕₚ min-meets
  , zip-with-length ∙ ap² min ihx ihy ∙ MR.∩-idem ℕₚ min-meets -- TODO syntax
$q←⇒-length ($q←-def le en un)     = le , le

empiq : ℕ → ISubq
empiq n .ifunq _ = nothing
empiq n .isizq = n
empiq n .idomq = []
empiq n .icofq _ = refl

inj-size-graph : ∀ {sq ts}
               → Injective (sq .funq)
               → sizeₛ (filterₛ (λ q → ts =? q .snd) (graphq sq)) ≤ 1
inj-size-graph {sq} {ts} inj with ts ∈? codomq sq
... | yes ts∈ =
  rec!
    (λ x xt∈ →
       let (x∈ , sxe) = ∈-graphq {sq = sq} xt∈ in
       =→≤ (  ap sizeₛ
                (filter-sng
                   (true→so! ⦃ (List-is-discrete {x = ts} .proof) ⦄ (sxe ⁻¹)) -- wtf
                   (∈-mapₛ x∈)
                   λ {x = z} z∈ zeb →
                      let ze = (sxe ∙ so→true! ⦃ (List-is-discrete {x = ts} .proof) ⦄ zeb) ⁻¹ in
                     rec!
                        (λ y y∈ ye →
                           let sy=sx = ap snd ye ⁻¹ ∙ ze in
                           ye ∙ ×-path (inj sy=sx) sy=sx)
                        (mapₛ-∈ z∈))
              ∙ size-sng {x = x , sq # x}))
    (∈-codom-graph {sq = sq} ts∈)
... | no ts∉ =
  subst (_≤ 1)
    (  size-[] ⁻¹
     ∙ ap sizeₛ
          (filter-none
             (λ {(x , qs)} xqs∈ →
                let (x∈ , sqe) = ∈-graphq {sq = sq} xqs∈ in
                false→so! ⦃ (List-is-discrete {x = ts} .proof) ⦄
                  (contra (λ tse → codom-∈ {sq = sq} (sqe ∙ tse ⁻¹) x∈) ts∉))
             ⁻¹))
    z≤

-- build the whole graph and look up the term
-- TODO pull out filter+graph ?
inv-fun : Subq → List Term → Maybe Id
inv-fun sq ts = map fst (extract1 (filterₛ (λ q → ts =? q .snd) (graphq sq)))

inv-fun-just : ∀ {sq ts x}
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

inv-fun-inj-nothing : ∀ {sq ts}
                    → Injective (sq .funq)
                    → inv-fun sq ts ＝ nothing
                    → {x : Id} → x ∈ sq .domq → sq # x ≠ ts
inv-fun-inj-nothing {sq} {ts} inj e {x} x∈ sqx =
  rec!
    [ (λ f0 → so-not
                 (none-filter f0 {z = x , ts} $
                  graphq-∈ {sq = sq} x∈ sqx)
                 (true→so! ⦃ (List-is-discrete {x = ts} .proof) ⦄ -- wtf
                    refl))
    , (λ f2 → <→≱ f2 (inj-size-graph {sq = sq} {ts = ts} inj))
    ]ᵤ
    (extract1-nothing $ mapₘ=nothing e)

inv-subq : Subq → ISubq
inv-subq sq .ifunq ts = inv-fun sq ts
inv-subq sq .isizq = sq .sizq
inv-subq sq .idomq = codomq sq
inv-subq sq .idszq {xs} xs∈ =
  rec!
    (λ x xts∈ →
        let (x∈ , sxe) = ∈-graphq {sq = sq} xts∈ in
        ap length (sxe ⁻¹) ∙ sq .cohq x∈)
    (∈-codom-graph {sq} xs∈)
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

invq-$q←-$q↦ : ∀ {ts zs sq}
             → Injective (sq .funq)
             → ((x : Id) → x ∈ bindₛ vars (from-list ts) → x ∈ sq .domq → ⊥)
             → inv-subq sq $q← ts ⇒ zs
             → sq $q↦ zs ⇒ ts
invq-$q←-$q↦ {ts}      {sq} _ _ ($q←-∈ {x} invj) =
  let (x∈ , e) = inv-fun-just {sq = sq} invj in
  subst (sq $q↦ replicate (length ts) (`` x) ⇒_) e $
  $q-``∈ (ap (λ q → replicate q (`` x)) (ap length (e ⁻¹) ∙ sq .cohq x∈)) x∈
invq-$q←-$q↦ {ts} {zs} {sq} si vd ($q←-⟶ {ps} {qs} {xs} {ys} invn uncj isqp isqq) =
  let (ce , le) = couple-uncouple uncj
      (ihlp , ihlx) = $q←⇒-length isqp
      (ihlq , ihly) = $q←⇒-length isqq
    in
  subst (sq $q↦ couple xs ys ⇒_)
        ce $
  $q-⟶ (zip-with-length ∙ ap² min ihlx ihly ∙ MR.∩-idem ℕₚ min-meets)
    (uncouple-couple (ihlx ∙ ihly ⁻¹))
    (invq-$q←-$q↦ si
              (λ x x∈ps x∈sq →
                   rec!
                     (λ y y∈ x∈ →
                         let (z , z∈ , yz∈) = ∈-zip-with-l {f = _⟶_} le (list-∈ y∈) in
                         vd x (∈-bind {y = y ⟶ z}
                                  (∈-list (subst ((y ⟶ z) ∈_) ce yz∈))
                                  (∈ₛ-∪∷←l x∈))
                               x∈sq)
                     (bind-∈ x∈ps))
              isqp)
    (invq-$q←-$q↦ si
              (λ x x∈qs x∈sq →
                    rec!
                      (λ y y∈ x∈ →
                         let (z , z∈ , yz∈) = ∈-zip-with-r {f = _⟶_} le (list-∈ y∈) in
                         vd x (∈-bind {y = z ⟶ y}
                                  (∈-list (subst ((z ⟶ y) ∈_) ce yz∈))
                                  (∈ₛ-∪∷←r {s₁ = vars z} x∈))
                               x∈sq)
                      (bind-∈ x∈qs))
              isqq)
invq-$q←-$q↦ {ts} {zs} {sq} si vd ($q←-def sz invn uncn) =
  let sz0 = uncouple-nothing-size {ts = ts} uncn in
  Dec.rec
    (λ (x , xe) →
          Dec.rec
            (λ x∈ → absurd (vd x (subst (λ q → x ∈ₛ bindₛ vars (from-list q))
                                         (xe ⁻¹) $
                                  subst (λ q → x ∈ₛ bindₛ vars q)
                                        (from-replicate-0< sz0 ⁻¹) $
                                  subst (x ∈ₛ_)
                                        (bindₛ-sng ⁻¹) $
                                  hereₛ refl)
                                 x∈))
            ($q-``∉ (xe ∙ ap (λ q → replicate q (`` x)) sz))
            (x ∈? sq .domq))
    (λ nxe → $q-def sz (λ x e → nxe (x , e ∙ ap (λ q → replicate q (`` x)) (sz ⁻¹))) uncn)
    (Dec-unreplicate sz0)

