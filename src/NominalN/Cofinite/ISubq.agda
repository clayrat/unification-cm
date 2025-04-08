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

isubq-ext : ∀ {n} {s₁ s₂ : ISubq n} → s₁ .ifunq ＝ s₂ .ifunq → s₁ .idomq ＝ s₂ .idomq → s₁ ＝ s₂
isubq-ext {s₁ = is-isubq f₁ d₁ c₁} {s₂ = is-isubq f₂ d₂ c₂} ef ed =
  ap² (is-isubq $²_)
      (×-path ef ed)
      (to-pathᴾ ((∀-is-of-hlevel 1 λ x → Π-is-of-hlevel 1 λ x∉ → hlevel 1) _ c₂))

empiq : (n : ℕ) → ISubq n
empiq n .ifunq _ = nothing
empiq n .idomq = []
empiq n .icofq _ = refl

insq : ∀ {n} → Vec Term n → Id → ISubq n → ISubq n
insq ts x s .ifunq xs = if xs =? ts then just x else s .ifunq xs
insq ts x s .idomq = ts ∷ s .idomq
insq ts x s .icofq {xs} xs∉ =
  let (xs≠ts , xs∉′) = ∉ₛ-uncons xs∉ in
  given-no xs≠ts
     return (λ q → (if ⌊ q ⌋ then just x else s .ifunq xs) ＝ nothing)
     then s .icofq xs∉′

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

inv-insq : ∀ {n} {ts : Vec Term n} {z} {θ : Subq n}
         → unrepvar ts ＝ nothing
         → uncouple ts ＝ nothing
         → ts ∉ codomq θ
         → z ∉ θ .domq
         → insq ts z (inv-subq θ) ＝ inv-subq (θ ◇q (z ≔q ts))
inv-insq {ts} {z} {θ} urn ucn ts∉ z∉ =
  let eq1 = $q↦-un urn ucn ⁻¹ ∙ ap (θ $q↦_) (if-true (true→so! (the (z ＝ z) refl)) ⁻¹)
      eq2 = eq-∈-mapₛ λ {x} x∈ →
              $q↦-`` ⁻¹
            ∙ ap (θ $q↦_)
                 (if-false $
                  false→so! (the (z ≠ x) $
                             contra (λ e → subst (_∈ₛ θ .domq) (e ⁻¹) x∈) z∉)) ⁻¹
    in
  isubq-ext
    (fun-ext λ qs →
         Dec.elim
            {C = λ q →
                 (if ⌊ q ⌋ then just z else inv-fun θ qs)
               ＝ (mapₘ fst (extract1 (if ⌊ q ⌋
                                         then (z , ts) ∷ filterₛ (λ q → qs =? q .snd) (graphq θ)
                                         else filterₛ (λ q → qs =? q .snd) (graphq θ))))}
            (λ qs=ts → ap (mapₘ fst)
                          (  extract1-x∷ ⁻¹
                           ∙ ap (λ q → extract1 ((z , ts) ∷ q))
                                (filter-none (λ where {x = (a , as)} as∈ →
                                                         false→so! (the (qs ≠ as)
                                                                        (contra (λ qs=as →
                                                                               let (a∈ , ae) = ∈-graphq {sq = θ} as∈ in
                                                                               codom-∈ {sq = θ} (ae ∙ qs=as ⁻¹ ∙ qs=ts) a∈) ts∉))) ⁻¹)))
            (λ _ → refl)
            (qs ≟ ts)
       ∙ ap² (λ u w → map fst (extract1
                                (if qs =? u
                                  then (z , u) ∷ filterₛ (λ q → qs =? q .snd) w
                                  else filterₛ (λ q → qs =? q .snd) w)))
            eq1
            -- TODO duplication
            (eq-∈-mapₛ λ {x} x∈ →
                           ×-path refl ($q↦-`` ⁻¹
                         ∙ ap (θ $q↦_)
                              (if-false $
                               false→so! (the (z ≠ x) $
                                          contra (λ e → subst (_∈ₛ θ .domq) (e ⁻¹) x∈) z∉)) ⁻¹))
       ∙ ap (λ w → map fst (extract1 w)) (filter-∷ ⁻¹)
       ∙ ap (λ w → map fst (extract1 (filterₛ (λ q → qs =? q .snd) w))) (mapₛ-∷ ⁻¹))
    (  ap² {C = λ _ _ → LFSet _} _∷_
         eq1
         eq2
     ∙ mapₛ-∷ ⁻¹)

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

{-
-- TODO can be simplified?
invq-fun-inj : ∀ {n} {s t : Subq n}
             → Injective (s .funq)
--             → Injective (t .funq)
             → inv-fun s ＝ inv-fun t
             → s .funq ＝ t .funq
invq-fun-inj {s} {t} injs {- injt -} e =
  fun-ext λ x →
    let es = happly e (s # x)
        et = happly e (t # x)
      in
    Dec.rec
      (λ x∈s →
        inv-fun-just {sq = t} {ts = s # x} (es ⁻¹ ∙ just-inv-fun {sq = s} injs x∈s) .snd ⁻¹)
      (λ x∉s →
        let qq = s .cofq x∉s
            zz = nothing-inv-fun {sq = s} {ts = s # x} λ {x} x∈ xe → x∉s (subst (_∈ₛ s .domq) (injs xe) x∈)
            es′ = the (inv-fun t (s # x) ＝ nothing)
                      (es ⁻¹ ∙ zz)
          in
        Dec.rec
          (λ x∈t →
              {!!}
              --absurd (x∉s (inv-fun-just {sq = s} {ts = t # x} (et ∙ just-inv-fun {sq = t} injt x∈t) .fst))
              )
          (λ x∉t → s .cofq x∉s ∙ t .cofq x∉t ⁻¹)
          (x ∈? t .domq)
          )

      (x ∈? s .domq)
-}
{-
invq-inj : ∀ {n} {s t : Subq n}
         → Injective (s .funq)
         → Injective (t .funq)
         → inv-subq s ＝ inv-subq t
         → s ＝ t
invq-inj {s} {t} injs injt e =
  let ef = invq-fun-inj {s = s} {t = t} injs injt (ap ifunq e) in
  subq-ext ef (mapₛ-inj injs (ap idomq e ∙ ap (λ q → mapₛ q (t .domq)) (ef ⁻¹)))
-}

-- NB: injectivity of s not needed!
invq-$q←-$q↦ : ∀ {n} {s : Subq n} {ts}
             → ∥``↦q ts s
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
          (ihp λ x x∈p →
             vd x (subst (λ q → x ∈ₛ bindₛ vars (from-vec q)) ce $
                   varsq-couple-l {xs = ps} x∈p))
          (ihq λ x x∈q →
             vd x (subst (λ q → x ∈ₛ bindₛ vars (from-vec q)) ce $
                   varsq-couple-r {xs = ps} x∈q))
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
                            subst (x ∈ₛ_)
                                  (varsq-replicate sz0 ⁻¹)
                           (hereₛ refl)))
           ∙ tse ⁻¹)
        (unrepvar ts)
        refl
