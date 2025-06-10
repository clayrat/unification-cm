{-# OPTIONS --safe #-}
module NominalN.Cofinite.Subq where

open import Prelude
open import Foundations.Sigma
open import Meta.Effect

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Reflects.Sigma as ReflectsΣ
open import Data.Dec as Dec
open import Data.Acc
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Maybe as Maybe
open import Data.Maybe.Correspondences.Unary.Any
open import Data.Vec.Inductive as Vec
open import Data.Vec.Inductive.Correspondences.Unary.All
open import Data.Vec.Inductive.Operations.Properties
open import Data.Sum as ⊎

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

open import Id
--open import Ren
--open import Ren.Quasi
open import NominalN.Term
open import NominalN.Cofinite.BaseA

-- (idempotent) substitution on sequences

record Subq (n : ℕ) : 𝒰 where
  constructor is-subq
  field
    funq : Id → Vec Term n
    domq : LFSet Id
    cofq : ∀ {x} → x ∉ domq → funq x ＝ replicate n (`` x)

open Subq public

unquoteDecl Subq-Iso = declare-record-iso Subq-Iso (quote Subq)
unquoteDecl H-Level-Subq = declare-record-hlevel 2 H-Level-Subq (quote Subq)

instance
  Funlike-Subq : ∀ {n} → Funlike ur (Subq n) Id (λ _ → Vec Term n)
  Funlike-Subq ._#_ = funq

subq-ext : ∀ {n} {s₁ s₂ : Subq n} → s₁ .funq ＝ s₂ .funq → s₁ .domq ＝ s₂ .domq → s₁ ＝ s₂
subq-ext {s₁ = is-subq f₁ d₁ c₁} {s₂ = is-subq f₂ d₂ c₂} ef ed =
  ap² (is-subq $²_)
      (×-path ef ed)
      (to-pathᴾ ((∀-is-of-hlevel 1 λ x → Π-is-of-hlevel 1 λ x∉ → hlevel 1) _ c₂))

id↦q : (n : ℕ) → Subq n
id↦q n .funq x = replicate n (`` x)
id↦q n .domq = []
id↦q n .cofq _ = refl

_≔q_ : ∀ {n} → Id → Vec Term n → Subq n
(_≔q_ {n} v ts) .funq x = if v == x then ts else replicate n (`` x)
(v ≔q ts) .domq = sng v
(_≔q_ {n} v ts) .cofq {x} x∉ =
  given-no ∉ₛ-uncons x∉ .fst ∘ _⁻¹
    return (λ q → (if ⌊ q ⌋ then ts else replicate n (`` x)) ＝ replicate n (`` x))
    then refl

thinq : ∀ {n} → LFSet Id → Subq n → Subq n
thinq xs s .funq = s .funq
thinq xs s .domq = xs ∪∷ s .domq
thinq xs s .cofq x∉ = s .cofq (∉ₛ-∪∷ {xs = xs} x∉ .snd)

graphq : ∀ {n} → Subq n → LFSet (Id × Vec Term n)
graphq sq = mapₛ (λ x → x , sq .funq x) (sq .domq)

codomq : ∀ {n} → Subq n → LFSet (Vec Term n)
codomq sq = mapₛ (sq .funq) (sq .domq)

-- sequence substitution

_$q↦?_!_ : ∀ {n} → Subq n → Id → Vec Term n → Vec Term n
s $q↦? x ! ts = if x ∈ₛ? s .domq then s # x else ts

$q↦-rec : ∀ {n} → Subq n → Rec-un n Id unrepvar (λ n → Vec Term n)
$q↦-rec {n = zero}  _ .ru[] _     = []
$q↦-rec {n = suc n} _ .ru[] e     = false! e
$q↦-rec             s .ruf  x ts  = s $q↦? x ! ts
$q↦-rec             _ .runj ps qs = couple ps qs
$q↦-rec             _ .runn ts    = ts

_$q↦_ : ∀ {n} → Subq n → Vec Term n → Vec Term n
s $q↦ t = rec-un ($q↦-rec s) t

$q↦-[] : {s : Subq 0} → s $q↦ [] ＝ []
$q↦-[] = subst-refl {A = ℕ} {B = λ n → Vec Term n} {x = 0} []

-- unfolding

$q↦-urj : ∀ {n}
         → {ts : Vec Term n} {x : Id}
         → x ∈ unrepvar ts
         → {s : Subq n} → s $q↦ ts ＝ s $q↦? x ! ts
$q↦-urj {n = zero}  {ts} urvj {s} =
  let (t , e , _) = unrepvar-just {ts = ts} urvj
    in
  false! $ ∈→true reflectsΣ-= e ⁻¹ ∙ ap unreplicate (size0-nil {xs = ts})
$q↦-urj {n = suc n} {ts} urvj {s} =
  elim-un-step-fj hlevel!
                  (rec→elim→-un ($q↦-rec s))
                  (∈→true reflectsΣ-= urvj)

$q↦-ucj : ∀ {n}
            → {ts ps qs : Vec Term n}
            → unrepvar ts ＝ nothing
            → uncouple ts ＝ just (ps , qs)
            → {s : Subq n} → s $q↦ ts ＝ couple (s $q↦ ps) (s $q↦ qs)
$q↦-ucj {n = zero}  {ts = []} {ps = []} {qs = []} urvn uj {s} =
  $q↦-[] {s = s} ∙ ap² couple ($q↦-[] {s = s} ⁻¹) ($q↦-[] {s = s} ⁻¹) -- refl
$q↦-ucj {n = suc n} {ts}      {ps}      {qs}      urvn uj {s} =
  elim-un-step-uj hlevel! (rec→elim→-un ($q↦-rec s)) urvn uj

$q↦-un : ∀ {n}
       → {ts : Vec Term n}
       → unrepvar ts ＝ nothing
       → uncouple ts ＝ nothing
       → {s : Subq n} → s $q↦ ts ＝ ts
$q↦-un {n = zero}  {ts = []} urvn un     = false! un
$q↦-un {n = suc n} {ts}      urvn un {s} =
  elim-un-step-un hlevel! (rec→elim→-un ($q↦-rec s)) urvn un

-- substitution on vars

$q↦-`` : ∀ {n} {s : Subq n} {x}
       → s $q↦ replicate n (`` x) ＝ s # x
$q↦-`` {n = zero}  {s}     = $q↦-[] {s = s} ∙ size0-nil ⁻¹
$q↦-`` {n = suc n} {s} {x} =
    $q↦-urj (∈ₘ-bind (just-unreplicate {n = suc n} {z = `` x} z<s) (here refl)) {s = s}
  ∙ Dec.elim
      {C = λ q → (if ⌊ q ⌋ then funq s x else replicate (suc n) (`` x)) ＝ s # x}
      (λ _ → refl)
      (λ x∉ → s .cofq x∉ ⁻¹)
      (x ∈? s .domq)

-- composition

_◇q_ : ∀ {n} → Subq n → Subq n → Subq n
(g ◇q f) .funq x = g $q↦ (f # x)
(g ◇q f) .domq = f .domq ∪∷ g .domq
(g ◇q f) .cofq x∉ =
  let (x∉f , x∉g) = ∉ₛ-∪∷ {xs = f .domq} x∉ in
  ap (g $q↦_) (f .cofq x∉f) ∙ $q↦-`` ∙ g .cofq x∉g

-- properties

≔q-inj : ∀ {n} {v} {ts : Vec Term n}
       → 0 < n
       → unreplicate ts ＝ nothing
       → Injective ((v ≔q ts) .funq)
≔q-inj {n} {v} {ts} lt unr {x} {y} =
  Dec.elim
    {C = λ q → (if ⌊ q ⌋ then ts else replicate n (`` x)) ＝ (if v == y then ts else replicate n (`` y)) → x ＝ y}
    (λ v=x →
         Dec.elim
            {C = λ q → ts ＝ (if ⌊ q ⌋ then ts else replicate n (`` y)) → x ＝ y}
            (λ v=y _ → v=x ⁻¹ ∙ v=y)
            (λ _   e → absurd (unreplicate-nothing lt unr e))
            (v ≟ y))
    (λ v≠x →
        Dec.elim
            {C = λ q → replicate n (`` x) ＝ (if ⌊ q ⌋ then ts else replicate n (`` y)) → x ＝ y}
            (λ _   e → absurd (unreplicate-nothing lt unr (e ⁻¹)))
            (λ v≠y e → ``-inj (replicate-inj n lt e))
            (v ≟ y))
    (v ≟ x)

{-
◇q-inj : ∀ {n} {s t : Subq n}
       → Injective (s .funq)
       → Injective (t .funq)
       → Injective ((s ◇q t) .funq)
◇q-inj is it e =
  {!!}
-}

subq-idq : ∀ {n} {ts} → id↦q n $q↦ ts ＝ ts
subq-idq {n} {ts} = elim-un go ts
  where
  go : ∀ {n} → Elim-un Id unrepvar λ q → id↦q n $q↦ q ＝ q
  go {n = zero}  .eu[] {ts} _                    =
    ap {x = ts} (id↦q 0 $q↦_) size0-nil ∙ $q↦-[] {s = id↦q 0} ∙ size0-nil ⁻¹
  go {n = suc n} .eu[] {ts} e                    = false! e
  go {n}         .euf  {ts} {a} lt fj            =
    $q↦-urj {ts = ts} (=just→∈ fj) {s = id↦q n}
  go             .eunj {ps} {qs} lt fn ej ihp ihq =
    $q↦-ucj fn ej ∙ ap² couple ihp ihq ∙ couple-uncouple (=just→∈ ej)
  go             .eunn          lt fn en         = $q↦-un fn en

subq?-◇ : ∀ {n} {s1 s2 : Subq n} {x} {ts}
        → x ∈ unrepvar ts
        → (s1 ◇q s2) $q↦? x ! ts ＝ s1 $q↦ (s2 $q↦? x ! ts)
subq?-◇ {s1} {s2} {x} {ts} fj =
    ap (λ q → if q then s1 $q↦ (s2 # x) else ts)
       (∈ₛ?-∪∷ {s₁ = s2 .domq})
  ∙ Dec.elim
      {C = λ q → (if ⌊ q ⌋ or (x ∈ₛ? s1 .domq) then s1 $q↦ (s2 # x) else ts)
               ＝ s1 $q↦ (if ⌊ q ⌋ then s2 # x else ts)}
      (λ _ → refl)
      (λ x∉2 →   ap (λ q → if x ∈ₛ? s1 .domq then q else ts)
                    (ap (s1 $q↦_) (s2 .cofq x∉2) ∙ $q↦-``)
               ∙ $q↦-urj fj ⁻¹)
      (x ∈? s2 .domq)

subq-◇ : ∀ {n} {s1 s2 : Subq n} {ts}
       → (s1 ◇q s2) $q↦ ts ＝ s1 $q↦ (s2 $q↦ ts)
subq-◇ {s1} {s2} {ts} = elim-un go ts
  where
  go : ∀ {n} {s1 s2 : Subq n} → Elim-un Id unrepvar λ q → (s1 ◇q s2) $q↦ q ＝ s1 $q↦ (s2 $q↦ q)
  go {n = zero}  {s1} {s2} .eu[] {ts}           _               =
      ap {x = ts} ((s1 ◇q s2) $q↦_) size0-nil
    ∙ $q↦-[] {s = s1 ◇q s2}
    ∙ $q↦-[] {s = s1} ⁻¹
    ∙ ap (s1 $q↦_) ($q↦-[] {s = s2} ⁻¹)
    ∙ ap {y = ts} (λ q → s1 $q↦ (s2 $q↦ q)) (size0-nil ⁻¹)
  go {n = suc n}           .eu[] e = false! e
  go             {s1} {s2} .euf {ts}            lt fj           =
    let fj′ = =just→∈ fj in
      $q↦-urj fj′
    ∙ subq?-◇ {s2 = s2} {ts = ts} fj′
    ∙ ap (s1 $q↦_) ($q↦-urj fj′ ⁻¹)
  go             {s1} {s2} .eunj {ps} {qs} {ts} lt fn ej ihp ihq =
      $q↦-ucj fn ej
    ∙ ap² couple ihp ihq
    ∙ $q↦-ucj {ps = s2 $q↦ ps}
         (unrepvar-couple {xs = s2 $q↦ ps})
         (∈→true reflectsΣ-= uncouple-couple)
         ⁻¹
    ∙ ap (s1 $q↦_) ($q↦-ucj fn ej ⁻¹)
  go {s1}                  .eunn                lt fn en        =
      $q↦-un fn en
    ∙ $q↦-un fn en ⁻¹
    ∙ ap (s1 $q↦_) ($q↦-un fn en ⁻¹)

◇q-id-l : ∀ {n} {s : Subq n} → id↦q n ◇q s ＝ s
◇q-id-l {s} = subq-ext (fun-ext λ x → subq-idq) (∪∷-id-r (s .domq))

◇q-id-r : ∀ {n} {s : Subq n} → s ◇q id↦q n ＝ s
◇q-id-r {s} = subq-ext (fun-ext λ x → $q↦-``) refl

◇q-assoc : ∀ {n} {f g h : Subq n}
          → (f ◇q g) ◇q h ＝ f ◇q (g ◇q h)
◇q-assoc {f} {g} {h} =
  subq-ext
    (fun-ext λ x → subq-◇ {ts = h $ x})
    (∪∷-assoc (h .domq))

thinq-$? : ∀ {n} {xs} {s : Subq n} {x} {ts}
         → x ∈ unrepvar ts
         → thinq xs s $q↦? x ! ts ＝ s $q↦? x ! ts
thinq-$? {n} {xs} {s} {x} {ts} urvj =
  let (t , urj , uvj) = unrepvar-just {ts = ts} urvj in
    ap (λ q → if q then s # x else ts) (∈ₛ?-∪∷ {s₁ = xs} ∙ or-comm (x ∈ₛ? xs) _)
  ∙ Dec.elim
      {C = λ q → (if ⌊ q ⌋ or (x ∈ₛ? xs) then s # x else ts)
               ＝ (if ⌊ q ⌋ then s # x else ts)}
       (λ _ → refl)
       (λ x∉s →
          Dec.elim
            {C = λ q → (if ⌊ q ⌋ then s # x else ts) ＝ ts}
            (λ _ →
                 s .cofq x∉s
               ∙ ap (replicate n) (∈→true Reflects-unvar uvj ⁻¹)
               ∙ unreplicate-just urj ⁻¹)
            (λ _ → refl)
            (x ∈? xs))
       (x ∈? s .domq)

thinq-$↦ : ∀ {n} {xs} {f : Subq n} {ts} → thinq xs f $q↦ ts ＝ f $q↦ ts
thinq-$↦ {xs} {f} {ts} = elim-un go ts
  where
  go : ∀ {n} → {f : Subq n} → Elim-un Id unrepvar λ q → thinq xs f $q↦ q ＝ f $q↦ q
  go {n = zero}  {f} .eu[] {ts} _ =
      ap {x = ts} (thinq xs f $q↦_) size0-nil
    ∙ $q↦-[] {s = thinq xs f}
    ∙ $q↦-[] {s = f} ⁻¹
    ∙ ap {y = ts} (f $q↦_) (size0-nil ⁻¹)
  go {n = suc n}     .eu[] e = false! e
  go             {f} .euf {ts} lt urvj =
    let urvj′ = =just→∈ urvj in
      $q↦-urj urvj′
    ∙ thinq-$? {xs = xs} {s = f} urvj′
    ∙ $q↦-urj urvj′ ⁻¹
  go .eunj lt urvn uj ihp ihq =
      $q↦-ucj urvn uj
    ∙ ap² couple ihp ihq
    ∙ $q↦-ucj urvn uj ⁻¹
  go .eunn lt urvn un =
      $q↦-un urvn un
    ∙ $q↦-un urvn un ⁻¹

thinq-[] : ∀ {n} {f : Subq n} → thinq [] f ＝ f
thinq-[] = subq-ext refl refl

thinq-∪∷ : ∀ {n} {xs ys} {f : Subq n} → thinq xs (thinq ys f) ＝ thinq (xs ∪∷ ys) f
thinq-∪∷ {xs} = subq-ext refl (∪∷-assoc xs)

thinq-◇-l : ∀ {n} {xs} {f g : Subq n} → thinq xs f ◇q g ＝ thinq xs (f ◇q g)
thinq-◇-l {xs} {f} {g} =
  subq-ext
    (fun-ext λ x → thinq-$↦ {xs = xs} {f = f} {ts = g # x})
    (  ∪∷-assoc {y = xs} (g .domq)
     ∙ ap (_∪∷ f .domq) (∪∷-comm {x = g .domq})
     ∙ ∪∷-assoc xs ⁻¹)

thinq-◇-r : ∀ {n} {xs} {f g : Subq n} → f ◇q thinq xs g ＝ thinq xs (f ◇q g)
thinq-◇-r {xs} = subq-ext refl (∪∷-assoc xs ⁻¹)

$q↦?-replicate-eq : ∀ {n} {p s : Subq n} {x : Id}
            → p # x ＝ s # x
            → p $q↦? x ! replicate n (`` x) ＝ s $q↦? x ! replicate n (`` x)
$q↦?-replicate-eq {n} {p} {s} {x} pse =
  Dec.elim
    {C = λ q → (if ⌊ q ⌋ then p # x else replicate n (`` x)) ＝ s $q↦? x ! replicate n (`` x)}
    (λ _ →
       Dec.elim
         {C = λ q → p # x ＝ (if ⌊ q ⌋ then s # x else replicate n (`` x))}
         (λ _   → pse)
         (λ x∉s → pse ∙ s .cofq x∉s)
         (x ∈? s .domq))
    (λ x∉p →
      Dec.elim
         {C = λ q → replicate n (`` x) ＝ (if ⌊ q ⌋ then s # x else replicate n (`` x))}
         (λ _ → p .cofq x∉p ⁻¹ ∙ pse)
         (λ _ → refl)
         (x ∈? s .domq))
    (x ∈? p .domq)

varsq-eq : ∀ {n} {p s : Subq n} {ts : Vec Term n}
         → ({x : Id} → x ∈ varsq ts → (p # x) ＝ (s # x))
         → (p $q↦ ts) ＝ (s $q↦ ts)
varsq-eq {p} {s} {ts} = elim-un go ts
  where
  go : ∀ {n} → {p s : Subq n}
     → Elim-un Id unrepvar λ q → ({x : Id} → x ∈ varsq q → (p # x) ＝ (s # x))
                               → (p $q↦ q) ＝ (s $q↦ q)
  go {n = zero}  {p} {s} .eu[] {ts} _ _ =
       ap {x = ts} (p $q↦_) size0-nil ∙ $q↦-[] {s = p}
    ∙ (ap {x = ts} (s $q↦_) size0-nil ∙ $q↦-[] {s = s}) ⁻¹
  go {n = suc n}         .eu[] e = false! e
  go             {p} {s} .euf {ts} {a} lt urvj e =
    let urvj′ = =just→∈ urvj
        tse = unrepvar-just-eq {ts = ts} {x = a} urvj′
      in
      $q↦-urj urvj′
    ∙ ap (p $q↦? a !_) tse
    ∙ $q↦?-replicate-eq {p = p} {s = s} {x = a}
         (e $ subst (a ∈ₛ_)
                    (varsq-replicate lt ⁻¹ ∙ ap varsq tse ⁻¹)
                    (hereₛ refl))
    ∙ ap (s $q↦? a !_) (tse ⁻¹)
    ∙ $q↦-urj urvj′ ⁻¹
  go .eunj {ps} {qs} {ts} lt urvn uj ihp ihq e =
    let ec = couple-uncouple {ts = ts} (=just→∈ uj) in
      $q↦-ucj urvn uj
    ∙ ap² couple
          (ihp λ {x} x∈ → e (subst (λ q → x ∈ₛ varsq q) ec (varsq-couple-l {xs = ps} x∈)))
          (ihq λ {x} x∈ → e (subst (λ q → x ∈ₛ varsq q) ec (varsq-couple-r {xs = ps} x∈)))
    ∙ $q↦-ucj urvn uj ⁻¹
  go .eunn _ urvn un _ =
      $q↦-un urvn un
    ∙ $q↦-un urvn un ⁻¹

$q↦?-eq-replicate : ∀ {n} {p s : Subq n} {x : Id}
                  → p $q↦? x ! replicate n (`` x) ＝ s $q↦? x ! replicate n (`` x)
                  → p # x ＝ s # x
$q↦?-eq-replicate {n} {p} {s} {x} =
  Dec.elim
    {C = λ q → (if ⌊ q ⌋ then p # x else replicate n (`` x)) ＝ s $q↦? x ! replicate n (`` x) → p # x ＝ s # x}
    (λ _ →
       Dec.elim
         {C = λ q → p # x ＝ (if ⌊ q ⌋ then s # x else replicate n (`` x)) → p # x ＝ s # x}
         (λ _     → id)
         (λ x∉s e → e ∙ s .cofq x∉s ⁻¹)
         (x ∈? s .domq))
    (λ x∉p →
      Dec.elim
         {C = λ q → replicate n (`` x) ＝ (if ⌊ q ⌋ then s # x else replicate n (`` x)) → p # x ＝ s # x}
         (λ _ e   → p .cofq x∉p ∙ e)
         (λ x∉s _ → p .cofq x∉p ∙ s .cofq x∉s ⁻¹)
         (x ∈? s .domq))
    (x ∈? p .domq)

{-
eq-varsq : ∀ {n} {p s : Subq n} {ts : Vec Term n}
         → (p $q↦ ts) ＝ (s $q↦ ts)
         → ({x : Id} → x ∈ varsq ts → (p # x) ＝ (s # x))
eq-varsq {p} {s} {ts} = elim-un go ts
  where
  go : ∀ {n} → {p s : Subq n}
     → Elim-un Id unrepvar λ q → (p $q↦ q) ＝ (s $q↦ q)
                               → ({x : Id} → x ∈ varsq q → (p # x) ＝ (s # x))
  go {n = zero}  {p} {s} .eu[] {ts} _ _ {x} x∈ =
    false! ⦃ Refl-x∉ₛ[] ⦄ (subst (x ∈ₛ_) (ap {x = ts} varsq size0-nil ∙ bindₛ-[]) x∈)
  go {n = suc n}         .eu[] e = false! e
  go {n}         {p} {s} .euf {ts} {a} lt urvj e {x} x∈ =
    let tse = unrepvar-just-eq {ts = ts} {x = a} urvj
        x=a = sng-∈ $ subst (x ∈ₛ_) (varsq-replicate lt) $ subst (λ q → x ∈ₛ varsq q) tse x∈
      in
    $q↦?-eq-replicate {p = p} {s = s} $
       ap (λ q → p $q↦? q ! replicate n (`` q)) x=a
     ∙ ap (p $q↦? a !_) (tse ⁻¹)
     ∙ $q↦-urj urvj ⁻¹
     ∙ e
     ∙ $q↦-urj urvj
     ∙ ap (s $q↦? a !_) tse
     ∙ ap (λ q → s $q↦? q ! replicate n (`` q)) (x=a ⁻¹)
  go             {p} {s} .eunj {ps} {qs} {ts} _ urvn uj ihp ihq e {x} x∈ =
    let e′ = $q↦-ucj {ts = ts} urvn uj ⁻¹ ∙ e ∙ $q↦-ucj {ts = ts} urvn uj
        (eps , eqs) = couple-inj e′
      in
    [ ihp eps
    , ihq eqs
    ]ᵤ (∈ₛ-∪∷→ {xs = varsq ps} $
        varsq-couple-∪∷ {xs = ps} $
        subst (λ q → x ∈ₛ varsq q)
              (couple-uncouple {ts = ts} uj ⁻¹)
              x∈)
  go {p} {s} .eunn {ts} _ urvn un e x∈ =
    {!!}  -- doesn't hold?
-}

∈-graphq : ∀ {n} {x : Id} {ts : Vec Term n} {sq : Subq n}
         → (x , ts) ∈ graphq sq
         → x ∈ sq .domq × (sq # x ＝ ts)
∈-graphq {x} {ts} {sq} xt∈ =
  rec!
    (λ z z∈ xte →
        let (xe , te) = ×-path-inv xte in
          subst (_∈ sq .domq) (xe ⁻¹) z∈
        , ap (sq .funq) xe ∙ te ⁻¹)
    (mapₛ-∈ xt∈)

graphq-∈ : ∀ {n} {x : Id} {ts : Vec Term n} {sq : Subq n}
         → x ∈ sq .domq
         → sq # x ＝ ts
         → (x , ts) ∈ graphq sq
graphq-∈ {x} {sq} x∈ sqx =
  subst (λ q → (x , q) ∈ graphq sq) sqx (∈-mapₛ x∈)

∈-codom-graph : ∀ {n} {sq : Subq n} {ts : Vec Term n}
               → ts ∈ codomq sq → ∃[ x ꞉ Id ] (x , ts) ∈ graphq sq
∈-codom-graph {sq} ts∈ =
  rec!  -- why not map
    (λ x x∈ tse → ∣ x , graphq-∈ {sq = sq} x∈ (tse ⁻¹) ∣₁)
    (mapₛ-∈ ts∈)

codom-∈ : ∀ {n} {sq : Subq n} {x : Id} {ts : Vec Term n}
        → sq # x ＝ ts
        → x ∈ sq .domq
        → ts ∈ codomq sq
codom-∈ {sq} e x∈ = subst (_∈ₛ codomq sq) e (∈-mapₛ x∈)

-- substitution properties

↦𝒫q : ℕ → 𝒰₁
↦𝒫q n = Subq n → 𝒰

-- disjointness of variables

∥``↦q : ∀ {n} → Vec Term n → ↦𝒫q n
∥``↦q ts s = (x : Id) → x ∈ varsq ts → x ∈ s .domq → ⊥

-- thinned "order" on seq substitutions

-- TODO should be flipped?

-- TODO these are actually categories, not orders
-- to get propositionality one should truncate

_≤↦q_ : ∀ {n} → Subq n → Subq n → 𝒰
_≤↦q_ {n} f g =
   Σ[ h ꞉ Subq n ] Σ[ xs ꞉ LFSet Id ] (h ◇q g ＝ thinq xs f)

≤↦q-refl : ∀ {n} {f : Subq n} → f ≤↦q f
≤↦q-refl {n} {f} = id↦q n , [] , ◇q-id-l ∙ thinq-[] ⁻¹

≤↦-trans : ∀ {n} {f g h : Subq n}
          → f ≤↦q g → g ≤↦q h → f ≤↦q h
≤↦-trans {f} {g} {h} (fg , wfg , efg) (gh ,  wgh , ehg) =
  ( fg ◇q gh
  , wgh ∪∷ wfg
  , (  ◇q-assoc {h = h}
     ∙ ap (fg ◇q_) ehg
     ∙ thinq-◇-r {xs = wgh} {f = fg} {g = g}
     ∙ ap (thinq wgh) efg
     ∙ thinq-∪∷ {xs = wgh} {ys = wfg} {f = f}
     )
  )

≤↦q-id : ∀ {n} {f : Subq n} → f ≤↦q id↦q n
≤↦q-id {f} = f , [] , ◇q-id-r ∙ thinq-[] ⁻¹

≤↦q-thinq : ∀ {n} {f : Subq n} {w} → f ≤↦q thinq w f
≤↦q-thinq {n} {f} {w} = id↦q n , w , ◇q-id-l

≤↦-◇-r : ∀ {n} {f g h : Subq n}
        → f ≤↦q g → (f ◇q h) ≤↦q (g ◇q h)
≤↦-◇-r {f} {h} (fg , wfg , efg) =
  ( fg
  , wfg
  , (  ◇q-assoc {h = h} ⁻¹
     ∙ ap (_◇q h) efg
     ∙ thinq-◇-l {xs = wfg} {f = f} {g = h})
  )
