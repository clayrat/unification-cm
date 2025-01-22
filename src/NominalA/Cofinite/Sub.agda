{-# OPTIONS --safe #-}
module NominalA.Cofinite.Sub where

open import Prelude
open import Foundations.Sigma
open import Meta.Effect

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.List as List
open import Data.List.Correspondences.Unary.All
open import Data.List.Operations.Properties
open import Data.Sum as ⊎

open import LFSet
open import LFSet.Mem

open import NominalA.Term
open import NominalA.Cofinite.Base

-- substitution as a cofinitely quantified map
-- (dom overapproximates the actual domain)

record Sub : 𝒰 where
  constructor is-sub
  field
    fun : Id → Term
    dom : LFSet Id
    cof : ∀ {x} → x ∉ dom → fun x ＝ `` x

open Sub public

unquoteDecl Sub-Iso = declare-record-iso Sub-Iso (quote Sub)
unquoteDecl H-Level-Sub = declare-record-hlevel 2 H-Level-Sub (quote Sub)

instance
  Funlike-Sub : Funlike ur Sub Id (λ _ → Term)
  Funlike-Sub ._#_ = fun

sub-ext : {s₁ s₂ : Sub} → s₁ .fun ＝ s₂ .fun → s₁ .dom ＝ s₂ .dom → s₁ ＝ s₂
sub-ext {s₁ = is-sub f₁ d₁ c₁} {s₂ = is-sub f₂ d₂ c₂} ef ed =
  ap² (is-sub $²_)
      (×-path ef ed)
      (to-pathᴾ ((∀-is-of-hlevel 1 λ x → Π-is-of-hlevel 1 λ x∉ → hlevel 1) _ c₂))

-- applying substitution

mutual
  _$↦_ : Sub → Term → Term
  su $↦ (`` x)     = su $ x
  su $↦ (con s ts) = con s (su $↦[] ts)

  _$↦[]_ : Sub → List Term → List Term
  su $↦[] [] = []
  su $↦[] (t ∷ ts) = su $↦ t ∷ su $↦[] ts

$↦[]-length : ∀ {s ts} → length (s $↦[] ts) ＝ length ts
$↦[]-length {ts = []}     = refl
$↦[]-length {ts = t ∷ ts} = ap suc $↦[]-length

$↦[]-map : ∀ {s ts} → s $↦[] ts ＝ map (s $↦_) ts
$↦[]-map     {ts = []}     = refl
$↦[]-map {s} {ts = t ∷ ts} = ap ((s $↦ t) ∷_) $↦[]-map

-- identity
id↦ : Sub
id↦ .fun = ``_
id↦ .dom = []
id↦ .cof _  = refl

-- composition
_◇_ : Sub → Sub → Sub
(g ◇ f) .fun = g $↦_ ∘ f #_
(g ◇ f) .dom = f .dom ∪∷ g .dom
(g ◇ f) .cof x∉ =
  let (x∉f , x∉g) = ∉ₛ-∪∷ {xs = f .dom} x∉ in
   ap (g $↦_) (f .cof x∉f) ∙ g .cof  x∉g

-- singleton
_≔_ : Id → Term → Sub
(v ≔ t) .fun x = if v == x then t else `` x
(v ≔ t) .dom = v ∷ []
(v ≔ t) .cof {x} x∉ =
  given-no ∉ₛ-uncons x∉ .fst ∘ _⁻¹
    return (λ q → (if ⌊ q ⌋ then t else (`` x)) ＝ (`` x))
    then refl

-- weakening the domain
thin : LFSet Id → Sub → Sub
thin xs s .fun = s .fun
thin xs s .dom = xs ∪∷ s .dom
thin xs s .cof x∉ = s .cof (∉ₛ-∪∷ {xs = xs} x∉ .snd)

-- interaction lemmas

mutual
  sub-id : ∀ {t} → id↦ $↦ t ＝ t
  sub-id {t = `` x}     = refl
  sub-id {t = con s ts} = ap (con s) sub-ids

  sub-ids : ∀ {ts} → id↦ $↦[] ts ＝ ts
  sub-ids {ts = []}     = refl
  sub-ids {ts = t ∷ ts} = ap² {C = λ x xs → List Term} _∷_ sub-id sub-ids

mutual
  sub-◇ : ∀ {s1 s2 t} → (s1 ◇ s2) $↦ t ＝ s1 $↦ (s2 $↦ t)
  sub-◇ {t = `` x} = refl
  sub-◇ {t = con s ts} = ap (con s) sub-◇-s

  sub-◇-s : ∀ {s1 s2 ts} → (s1 ◇ s2) $↦[] ts ＝ s1 $↦[] (s2 $↦[] ts)
  sub-◇-s {ts = []} = refl
  sub-◇-s {ts = t ∷ ts} = ap² {C = λ x xs → List Term} _∷_ (sub-◇ {t = t}) sub-◇-s

◇-id-l : {s : Sub} → id↦ ◇ s ＝ s
◇-id-l {s} = sub-ext (fun-ext λ x → sub-id) (∪∷-id-r (s .dom))

◇-id-r : {s : Sub} → s ◇ id↦ ＝ s
◇-id-r {s} = sub-ext (fun-ext λ x → refl) refl

◇-assoc : ∀ {f g h : Sub}
         → (f ◇ g) ◇ h ＝ f ◇ (g ◇ h)
◇-assoc {f} {g} {h} =
  sub-ext
    (fun-ext λ x → sub-◇ {t = h $ x})
    (∪∷-assoc (h .dom))

mutual
  sub-occurs : ∀ {v t} u → ¬ occurs v u → u ＝ (v ≔ t) $↦ u
  sub-occurs {t} (`` x)    noc =
    given-no noc
      return (λ q → (`` x) ＝ (if ⌊ q ⌋ then t else (`` x)))
      then refl
  sub-occurs     (con s ts) noc = ap (con s) (sub-occurs-s ts noc)

  sub-occurs-s : ∀ {v t} ts → ¬ occurs-list v ts → ts ＝ ((v ≔ t) $↦[] ts)
  sub-occurs-s []       noc = refl
  sub-occurs-s (t ∷ ts) noc = ap² {C = λ x xs → List Term} _∷_ (sub-occurs t (contra inl noc)) (sub-occurs-s ts (contra inr noc))

mutual
  sub-rem : ∀ {x c t}
            → wf-tm c t
            → x ∈ c
            → ∀ u → wf-tm (rem x c) u
            → wf-tm (rem x c) ((x ≔ u) $↦ t)
  sub-rem {x} {c} (wf-var {x = y} y∈) x∈ u wr =
    Dec.elim
      {C = λ q → wf-tm (rem x c) (if ⌊ q ⌋ then u else (`` y))}
      (λ _ → wr)
      (λ ¬p → wf-var (rem-∈-≠ (¬p ∘ _⁻¹) y∈))
      (x ≟ y)
  sub-rem {x} {c} (wf-con wa)          x∈ u wr =
    wf-con (sub-rem-s wa x∈ u wr)

  sub-rem-s : ∀ {x c ts}
            → All (wf-tm c) ts
            → x ∈ c
            → ∀ u → wf-tm (rem x c) u
            → All (wf-tm (rem x c)) ((x ≔ u) $↦[] ts)
  sub-rem-s {ts = []}     []       x∈ u wr = []
  sub-rem-s {ts = t ∷ ts} (w ∷ wa) x∈ u wr =
    sub-rem w x∈ u wr ∷ sub-rem-s wa x∈ u wr

mutual
  sub-ar : ∀ {x u a t}
         → wa-tm a t
         → wa-tm a u
         → wa-tm a ((x ≔ u) $↦ t)
  sub-ar {x} {u} {a} (wa-var {x = y}) wu =
    Dec.elim
      {C = λ q → wa-tm a (if ⌊ q ⌋ then u else (`` y))}
      (λ _ → wu)
      (λ _ → wa-var)
      (x ≟ y)
  sub-ar         {a} (wa-con e w)     wu =
    wa-con (e ∙ $↦[]-length ⁻¹) (sub-ar-s w wu)

  sub-ar-s : ∀ {x u a ts}
           → All (wa-tm a) ts
           → wa-tm a u
           → All (wa-tm a) ((x ≔ u) $↦[] ts)
  sub-ar-s {ts = []}     []       wu = []
  sub-ar-s {ts = x ∷ ts} (w ∷ wa) wu =
    sub-ar w wu ∷ sub-ar-s wa wu

mutual
  thin-$↦ : ∀ {xs f t} → thin xs f $↦ t ＝ f $↦ t
  thin-$↦      {t = `` x}     = refl
  thin-$↦ {xs} {t = con s ts} = ap (con s) (thin-$↦[] {xs = xs} {ts = ts})

  thin-$↦[] : ∀ {xs f ts} → thin xs f $↦[] ts ＝ f $↦[] ts
  thin-$↦[]      {ts = []}     = refl
  thin-$↦[] {xs} {ts = t ∷ ts} =
    ap² {C = λ x xs → List Term} _∷_ (thin-$↦ {xs = xs} {t = t}) (thin-$↦[] {xs = xs} {ts = ts})

thin-[] : ∀ {f} → thin [] f ＝ f
thin-[] = sub-ext refl refl

thin-∪∷ : ∀ {xs ys f} → thin xs (thin ys f) ＝ thin (xs ∪∷ ys) f
thin-∪∷ {xs} = sub-ext refl (∪∷-assoc xs)

thin-id : ∀ {f} → thin (f .dom) f ＝ f
thin-id = sub-ext refl ∪∷-idem

thin-◇-l : ∀ {xs f g} → thin xs f ◇ g ＝ thin xs (f ◇ g)
thin-◇-l {xs} {f} {g} =
  sub-ext
    (fun-ext λ x → thin-$↦ {xs = xs} {f = f} {t = g .fun x})
    (  ∪∷-assoc {y = xs} (g . dom)
     ∙ ap (_∪∷ f .dom) (∪∷-comm {x = g .dom})
     ∙ ∪∷-assoc xs ⁻¹)

thin-◇-r : ∀ {xs f g} → f ◇ thin xs g ＝ thin xs (f ◇ g)
thin-◇-r {xs} = sub-ext refl (∪∷-assoc xs ⁻¹)

-- substitution on contexts

_$↦C_ : Sub → Ctx1 → Ctx1
_$↦C_ f = map λ where (s , l , r) → s , map (f $↦_) l , map (f $↦_) r

+:-subst : ∀ {f : Sub} {ps : Ctx1} {t}
         → (f $↦ (ps +: t)) ＝ (f $↦C ps) +: (f $↦ t)
+:-subst     {ps = []}                   = refl
+:-subst {f} {ps = (s , l , r) ∷ ps} {t} =
  ap (con s)
     (  $↦[]-map {ts = l ++ (ps +: t) ∷ r}
      ∙ map-++ (f $↦_) l ((ps +: t) ∷ r)
      ∙ ap (λ q → map (f $↦_) l ++ q ∷ mapₗ (f $↦_) r) (+:-subst {ps = ps}))

-- well-formed substitutions

-- TODO decompose into well-formedness and acyclicity
Wf-subst : Varctx → Sub → 𝒰
Wf-subst v s =
  {x : Id} → x ∈ s .dom → x ∈ v × wf-tm (minus v (s .dom)) (s $ x)

wf-idsub : ∀ {c} → Wf-subst c id↦
wf-idsub = false! ⦃ Refl-x∉ₛ[] ⦄ -- why

wf-sub-≔ : ∀ {x t v}
         → x ∈ v
         → wf-tm (rem x v) t
         → Wf-subst v (x ≔ t)
wf-sub-≔ {x} {t} {v} x∈ wt {x = y} xi =
  Recomputable-×
    Recomputable-∈ₛ (wf-tm-recomp {t = if x == y then t else `` y})
    .recompute $
    (erase
      (elim! {P = λ _ → (y ∈ₛ v) ×ₜ wf-tm (minus v (x ∷ [])) (if x == y then t else (`` y))}
             [ (λ e →   (subst (_∈ v) (e ⁻¹) x∈)
                      , (given-yes (e ⁻¹)
                          return (λ q → wf-tm (minus v (x ∷ [])) (if ⌊ q ⌋ then t else (`` y)))
                          then subst (λ q → wf-tm q t) (ap (rem x)
                                 (  minus-[]-r {s = v} ⁻¹)
                                  ∙ minus-∷-r {x = x} {s = v} {r = []} ⁻¹) wt))
             , false! ]ᵤ
             (∈ₛ⇉ xi .erased)))

mutual
  substs-remove : ∀ {c : Varctx} {s t}
                → Wf-subst c s → wf-tm c t
                → wf-tm (minus c (s. dom)) (s $↦ t)
  substs-remove {c} {s} ws (wf-var {x} x∈) with x ∈? (s .dom)
  ... | yes xi = ws xi .snd
  ... | no nxi = subst (wf-tm (minus c (dom s))) (s .cof nxi ⁻¹)
                       (wf-var (∈-minus x∈ nxi))
  substs-remove         ws (wf-con wa) = wf-con (substs-remove-s ws wa)

  substs-remove-s : ∀ {c s ts}
                  → Wf-subst c s
                  → All (wf-tm c) ts
                  → All (wf-tm (minus c (s .dom))) (s $↦[] ts)
  substs-remove-s {ts = []}     ws []       = []
  substs-remove-s {ts = x ∷ ts} ws (w ∷ wa) =
    (substs-remove ws w) ∷ (substs-remove-s ws wa)

wf-sub-◇ : ∀ {c s1 s2}
          → Wf-subst c s1 → Wf-subst (minus c (s1 .dom)) s2
          → Wf-subst c (s2 ◇ s1)
wf-sub-◇ {c} {s1} {s2} ws1 ws2 {x} xx with x ∈? s1 .dom
... | yes xi1 =
     ws1 xi1 .fst
  , (subst (λ q → wf-tm q (s2 $↦ (s1 # x))) (minus-minus {v = c} {s₁ = s1 .dom} {s₂ = s2 .dom}) $
     substs-remove {s = s2} ws2 (ws1 xi1 .snd))
... | no nxi1 =
  Recomputable-×
    Recomputable-∈ₛ (wf-tm-recomp {t = s2 $↦ (s1 $ x)})
      .recompute
        (erase
           (elim! {P = λ _ → (x ∈ₛ c) × wf-tm (minus c (s1 .dom ∪∷ s2 .dom)) (s2 $↦ (s1 $ x))}
               [ (λ x∈s₁ → absurd (nxi1 x∈s₁))
               , (λ x∈s₂ → let (x∈m , wm) = ws2 x∈s₂ in
                              minus-⊆ {ys = s1 .dom} x∈m
                            , (subst (λ q → wf-tm (minus c (s1 .dom ∪∷ s2 .dom)) (s2 $↦ q)) (s1 .cof nxi1 ⁻¹) $
                               subst (λ q → wf-tm q (s2 $ x)) minus-minus $
                               wm))
               ]ᵤ
               (∈ₛ-∪∷→ {s₁ = s1 .dom} xx .erased)))

--- substitution on lists

_$↦L_ : Sub → List Constr → List Constr
_$↦L_ s = map (bimap (s $↦_) (s $↦_))

wf-constr-list-remove : ∀ {c v t}
                      → v ∈ c → ¬ occurs v t → wf-tm c t
                      → ∀ {l} → wf-constr-list c l
                      → wf-constr-list (rem v c) ((v ≔ t) $↦L l)
wf-constr-list-remove {t} vi noc w =
  all→map ∘ all-map
     λ where {x = l , r} (wl , wr) →
                let wrem = occurs-wf-tm w noc in
                  (sub-rem wl vi t wrem)
                , (sub-rem wr vi t wrem)

wa-constr-list-≔ : ∀ {a v t}
                 → wa-tm a t
                 → ∀ {l} → wa-constr-list a l
                 → wa-constr-list a ((v ≔ t) $↦L l)
wa-constr-list-≔ w =
  all→map ∘ all-map
      λ where {x = l , r} (wl , wr) → (sub-ar wl w) , (sub-ar wr w)

-- substitution properties

↦𝒫 : 𝒰₁
↦𝒫 = Sub → 𝒰

-- emptiness
↦𝒫∅ : ↦𝒫 → 𝒰
↦𝒫∅ p = ∀ s → ¬ p s

-- equivalence
↦𝒫≃ : ↦𝒫 → ↦𝒫 → 𝒰
↦𝒫≃ p q = ∀ s → p s ≃ q s

↦𝒫∅≃ : ∀ {p q : ↦𝒫} → ↦𝒫≃ p q → ↦𝒫∅ p ≃ ↦𝒫∅ q
↦𝒫∅≃ {p} {q} eq =
  prop-extₑ! (λ np f qf → np f (eq f ⁻¹ $ qf)) (λ nq f pf → nq f (eq f $ pf))

-- product
↦𝒫× : ↦𝒫 → ↦𝒫 → ↦𝒫
↦𝒫× p q s = p s × q s

-- extension
↦𝒫◇ : ↦𝒫 → Sub → ↦𝒫
↦𝒫◇ p f g = p (g ◇ f)

↦𝒫◇≃ : {p q : ↦𝒫} {f : Sub} → ↦𝒫≃ p q → ↦𝒫≃ (↦𝒫◇ p f) (↦𝒫◇ q f)
↦𝒫◇≃ {f} eq g = eq (g ◇ f)

↦𝒫◇-id≃ : {p : ↦𝒫} → ↦𝒫≃ (↦𝒫◇ p id↦) p
↦𝒫◇-id≃ {p} s = =→≃ (ap p ◇-id-r)

-- stability under thinning
↦thin : ↦𝒫 → 𝒰
↦thin p = ∀ f w → p f → p (thin w f)

thin↦ : ↦𝒫 → 𝒰
thin↦ p = ∀ f w → p (thin w f) → p f

-- thinned "order"
-- these are actually categories, not orders
-- to get propositionality one should truncate

_≤↦_ : Sub → Sub → 𝒰
f ≤↦ g =
   Σ[ h ꞉ Sub ] Σ[ xs ꞉ LFSet Id ] (h ◇ g ＝ thin xs f)

≤↦-refl : ∀ {f} → f ≤↦ f
≤↦-refl {f} = id↦ , [] , ◇-id-l ∙ thin-[] ⁻¹

≤↦-trans : ∀ {f g h : Sub}
          → f ≤↦ g → g ≤↦ h → f ≤↦ h
≤↦-trans {f} {g} {h} (fg , wfg , efg) (gh ,  wgh , ehg) =
  ( fg ◇ gh
  , wgh ∪∷ wfg
  , (  ◇-assoc {h = h}
     ∙ ap (fg ◇_) ehg
     ∙ thin-◇-r {xs = wgh} {f = fg} {g = g}
     ∙ ap (thin wgh) efg
     ∙ thin-∪∷ {xs = wgh} {ys = wfg} {f = f}
     )
  )

≤↦-id : {f : Sub} → f ≤↦ id↦
≤↦-id {f} = f , [] , ◇-id-r ∙ thin-[] ⁻¹

≤↦-thin : ∀ {f w} → f ≤↦ thin w f
≤↦-thin {f} {w} = id↦ , w , ◇-id-l

≤↦-◇-r : ∀ {f g h : Sub}
        → f ≤↦ g → (f ◇ h) ≤↦ (g ◇ h)
≤↦-◇-r {f} {h} (fg , wfg , efg) =
  ( fg
  , wfg
  , (◇-assoc {h = h} ⁻¹
     ∙ ap (_◇ h) efg
     ∙ thin-◇-l {xs = wfg} {f = f} {g = h})
  )

-- maximal substitution satisfying a property
Max↦ : ↦𝒫 → ↦𝒫
Max↦ p f = p f × (∀ f′ → p f′ → f′ ≤↦ f)

Max↦≃ : ∀ {p q : ↦𝒫} → ↦𝒫≃ p q → ↦𝒫≃ (Max↦ p) (Max↦ q)
Max↦≃ eq f = ×-ap (eq f) (Π-cod-≃ λ f′ → Π-dom-≃ (eq f′ ⁻¹))

-- downwards closure
DCl : ↦𝒫 → 𝒰
DCl p = ∀ f g → f ≤↦ g → p g → p f

optimist-lemma : ∀ {p q : ↦𝒫} {a f g}
               → DCl p
               → Max↦ (↦𝒫◇ p a) f
               → ↦thin q
               → Max↦ (↦𝒫◇ q (f ◇ a)) g
               → Max↦ (↦𝒫◇ (↦𝒫× p q) a) (g ◇ f)
optimist-lemma {q} {a} {f} {g} dc (pfa , pmax) tq (qgfa , qmax) =
   (  (dc ((g ◇ f) ◇ a) (f ◇ a) (g , [] , ◇-assoc {h = a} ⁻¹ ∙ thin-[] ⁻¹) pfa)
    , subst q (◇-assoc {h = a} ⁻¹) qgfa)
  , λ f′ →
    λ where (pfa , qfa) →
              (let (j , w , ea) = pmax f′ pfa in
               ≤↦-trans {f = f′} {g = thin w f′} {h = g ◇ f} (≤↦-thin {f = f′} {w = w}) $
               subst (_≤↦ (g ◇ f)) ea $
               ≤↦-◇-r {f = j} {g = g} {h = f} $
               qmax j $
               subst q (thin-◇-l {xs = w} {g = a} ⁻¹ ∙ ap (_◇ a) (ea ⁻¹) ∙ ◇-assoc {g = f} {h = a}) $
               tq (f′ ◇ a) w qfa)
