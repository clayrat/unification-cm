{-# OPTIONS --safe #-}
module Nominal.Cofinite.Sub where

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
open import LFSet.Membership
open import LFSet.Discrete

open import Nominal.Term
open import Nominal.Cofinite.Base

-- (idempotent) substitution as a cofinitely quantified map
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
_$↦_ : Sub → Term → Term
s $↦ (`` x)    = s $ x
s $↦ (p ⟶ q) = (s $↦ p) ⟶ (s $↦ q)
s $↦ con       = con

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

-- strengthening the domain
restrict : LFSet Id → Sub → Sub
restrict xs s .fun x = if x ∈ₛ? xs then s .fun x else `` x
restrict xs s .dom = filterₛ (_∈ₛ? xs) (s .dom)
restrict xs s .cof {x} x∉ =
  [ (λ sn   →
     given-no the (x ∉ xs) (so→false! sn)
        return (λ q → (if ⌊ q ⌋ then s .fun x else (`` x)) ＝ (`` x))
        then refl)
  , (λ x∉′ → Dec.elim
                {C = λ q → (if ⌊ q ⌋ then s .fun x else (`` x)) ＝ (`` x)}
                (λ _ → s .cof x∉′)
                (λ _ → refl)
                (x ∈? xs) )
  ]ᵤ (filter-∉ x∉)

-- range
range : Sub → LFSet Id
range s = bindₛ (λ x → vars (s $ x)) (s .dom)

-- interaction lemmas

sub-id : ∀ {t} → id↦ $↦ t ＝ t
sub-id {t = `` x}    = refl
sub-id {t = p ⟶ q} = ap² _⟶_ (sub-id {t = p}) (sub-id {t = q})
sub-id {t = con}     = refl

sub-◇ : ∀ {s1 s2 t} → (s1 ◇ s2) $↦ t ＝ s1 $↦ (s2 $↦ t)
sub-◇ {t = `` x} = refl
sub-◇ {t = p ⟶ q} = ap² _⟶_ (sub-◇ {t = p}) (sub-◇ {t = q})
sub-◇ {t = con} = refl

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

noc-all-id : ∀ {s t}
           → (∀ x → x ∈ s .dom → ¬ occurs x t)
           → (s $↦ t) ＝ t
noc-all-id {s} {t = `` x}    noca =
  s .cof λ x∈ → noca x x∈ refl
noc-all-id     {t = p ⟶ q} noca =
  ap² _⟶_ (noc-all-id λ z z∈ → contra inl (noca z z∈))
            (noc-all-id λ z z∈ → contra inr (noca z z∈))
noc-all-id     {t = con}     noca = refl

-- reverse doesn't seem to hold

sub-occurs : ∀ {v t} u → ¬ occurs v u → u ＝ (v ≔ t) $↦ u
sub-occurs {v} u noc =
  noc-all-id
    (λ x x∈ oc →
      Recomputable-⊥ .recompute $ erase $
        rec! (λ e → noc (subst (λ q → occurs q u) e oc))
          ((∈ₛ∷-∉ᴱ x∈ ∉ₛ[]) .erased)) ⁻¹

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
sub-rem (wf-arr wp wq)       x∈ u wr = wf-arr (sub-rem wp x∈ u wr) (sub-rem wq x∈ u wr)
sub-rem  wf-con              x∈ u wr = wf-con

thin-$↦ : ∀ {xs f t} → thin xs f $↦ t ＝ f $↦ t
thin-$↦      {t = `` x} = refl
thin-$↦ {xs} {t = p ⟶ q} = ap² _⟶_ (thin-$↦ {xs = xs} {t = p}) (thin-$↦ {xs = xs} {t = q})
thin-$↦      {t = con} = refl

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

restrict-$↦ : ∀ {f t xs}
            → vars t ⊆ xs
            → restrict xs f $↦ t ＝ f $↦ t
restrict-$↦ {f} {t = `` x}    sub =
  ap (λ q → (if q then (f $ x) else (`` x)))
     (so≃is-true $ true→so! (sub (hereₛ refl)))
restrict-$↦ {t = p ⟶ q} {xs} sub =
  ap² _⟶_ (restrict-$↦ {t = p} {xs = xs} λ {x} → sub {x} ∘ ∈ₛ-∪∷←l)
            (restrict-$↦ {t = q} {xs = xs} λ {x} → sub {x} ∘ ∈ₛ-∪∷←r {s₁ = vars p})
restrict-$↦ {t = con}         _   = refl

vars-eq : ∀ {s s′ t}
        → ({x : Id} → x ∈ vars t → (s $ x) ＝ (s′ $ x))
        → (s $↦ t) ＝ (s′ $↦ t)
vars-eq {s} {s′} {t = `` x}   eq = eq (hereₛ refl)
vars-eq {s} {s′} {t = p ⟶ q} eq =
  ap² _⟶_
    (vars-eq {t = p} (eq ∘ ∈ₛ-∪∷←l))
    (vars-eq {t = q} (eq ∘ ∈ₛ-∪∷←r {s₁ = vars p}))
vars-eq {s} {s′} {t = con}    eq = refl

range-eq : ∀ {s s′ t}
         → ({x : Id} → x ∈ range t → (s $ x) ＝ (s′ $ x))
         → ({x : Id} → x ∉ dom t → (s $ x) ＝ (s′ $ x))
         → thin (dom s′) (s ◇ t) ＝ thin (dom s) (s′ ◇ t)
range-eq {s} {s′} {t} er end =
  sub-ext
    (fun-ext λ q → Dec.elim
                     {C = λ _ → (s $↦ fun t q) ＝ (s′ $↦ fun t q)}
                     (λ q∈ → vars-eq {t = t $ q} (er ∘ ∈-bind q∈))
                     (λ q∉ → ap (s $↦_) (t .cof q∉) ∙ end q∉ ∙ ap (s′ $↦_) (t .cof q∉ ⁻¹))
                     (q ∈? dom t))
    (  ap (dom s′ ∪∷_) (∪∷-comm {x = t .dom})
     ∙ ∪∷-assoc {y = s .dom} (dom s′)
     ∙ ap (_∪∷ dom t) (∪∷-comm {x = s′ .dom})
     ∙ ∪∷-assoc {y = s′ .dom} (dom s) ⁻¹
     ∙ ap (dom s ∪∷_) (∪∷-comm {x = s′ .dom}))

-- substitution on contexts

_$↦C_ : Sub → Ctx1 → Ctx1
_$↦C_ f = map (⊎.dmap (f $↦_) (f $↦_))

+:-subst : ∀ {f : Sub} {ps : Ctx1} {t}
         → (f $↦ (ps +: t)) ＝ (f $↦C ps) +: (f $↦ t)
+:-subst     {ps = []}         = refl
+:-subst {f} {ps = inl r ∷ ps} = ap (_⟶ (f $↦ r)) (+:-subst {ps = ps})
+:-subst {f} {ps = inr l ∷ ps} = ap ((f $↦ l) ⟶_) (+:-subst {ps = ps})

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

-- well-formed substitutions

-- TODO decompose into well-formedness and acyclicity
Wf-subst : Varctx → ↦𝒫
Wf-subst v s =
  {x : Id} → x ∈ s .dom → x ∈ v × wf-tm (minus v (s .dom)) (s $ x)

wf-idsub : ∀ {c} → Wf-subst c id↦
wf-idsub = false! ⦃ Refl-x∉ₛ[] ⦄ -- why

wf-sub-≔ : ∀ {x t v}
         → x ∈ v
         → wf-tm (rem x v) t
         → Wf-subst v (x ≔ t)
wf-sub-≔ {x} {t} {v} x∈ wt {x = y} y∈ =
  let e = ∈ₛ∷-∉ y∈ ∉ₛ[] in
    subst (_∈ v) (e ⁻¹) x∈
  , given-yes (e ⁻¹)
      return (λ q → wf-tm (minus v (x ∷ [])) (if ⌊ q ⌋ then t else (`` y)))
      then subst (λ q → wf-tm q t) (ap (rem x)
             (  minus-[]-r {s = v} ⁻¹)
              ∙ minus-∷-r {x = x} {s = v} {r = []} ⁻¹) wt

substs-remove : ∀ {c : Varctx} {s t}
              → Wf-subst c s → wf-tm c t
              → wf-tm (minus c (s .dom)) (s $↦ t)
substs-remove {c} {s} ws (wf-var {x} x∈) with x ∈? (s .dom)
... | yes xi = ws xi .snd
... | no nxi = subst (wf-tm (minus c (dom s))) (s .cof nxi ⁻¹)
                     (wf-var (∈-minus x∈ nxi))
substs-remove         ws (wf-arr wp wq) = wf-arr (substs-remove ws wp) (substs-remove ws wq)
substs-remove         ws  wf-con        = wf-con

wf-sub-◇ : ∀ {c s1 s2}
          → Wf-subst c s1 → Wf-subst (minus c (s1 .dom)) s2
          → Wf-subst c (s2 ◇ s1)
wf-sub-◇ {c} {s1} {s2} ws1 ws2 {x} x∈∪∷ with x ∈? s1 .dom
... | yes xi1 =
     ws1 xi1 .fst
  , (subst (λ q → wf-tm q (s2 $↦ (s1 # x))) (minus-minus {v = c} {s₁ = s1 .dom} {s₂ = s2 .dom}) $
     substs-remove {s = s2} ws2 (ws1 xi1 .snd))
... | no nxi1 =
  let (x∈m , wm) = ws2 (∈ₛ∪∷-∉ x∈∪∷ nxi1) in
    minus-⊆ {ys = s1 .dom} x∈m
  , (subst (λ q → wf-tm (minus c (s1 .dom ∪∷ s2 .dom)) (s2 $↦ q)) (s1 .cof nxi1 ⁻¹) $
     subst (λ q → wf-tm q (s2 $ x)) minus-minus $
     wm)

-- WF substitutions are idempotent

wf-sub-same : ∀ {c s} {x : Id}
            → Wf-subst c s
            → (s $↦ (s $ x)) ＝ (s $ x)
wf-sub-same {s} {x} w with x ∈? (s .dom)
... | yes xi = noc-all-id (wf-tm-minus-occurs (w xi .snd) .fst)
... | no nxi = ap (s $↦_) (s .cof nxi)

wf-sub-idem : ∀ {c s}
            → Wf-subst c s
            → s ◇ s ＝ s
wf-sub-idem {s} w =
  sub-ext
    (fun-ext λ x → wf-sub-same {s = s} {x = x} w)
    ∪∷-idem

-- "order" on terms

_≤t_ : Term → Term → 𝒰
t ≤t s =
   Σ[ f ꞉ Sub ] (f $↦ s ＝ t)

≤t-refl : ∀ {t} → t ≤t t
≤t-refl = id↦ , sub-id

≤t-trans : ∀ {t s q}
          → t ≤t s → s ≤t q → t ≤t q
≤t-trans {q} (f , fe) (g , ge) =
    (f ◇ g)
  , sub-◇ {t = q} ∙ ap (f $↦_) ge ∙ fe

-- thinned "order" on substitutions
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
