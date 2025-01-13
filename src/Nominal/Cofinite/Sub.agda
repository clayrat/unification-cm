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
open import Data.Sum

open import LFSet
open import LFSet.Mem

open import Nominal.Ty
open import Nominal.Cofinite.Base

-- substitution as a cofinitely quantified map

record Sub : 𝒰 where
  constructor is-sub
  field
    fun : Id → Ty
    dom : LFSet Id
    cof : ∀ {x} → x ∉ dom → fun x ＝ `` x

open Sub public

unquoteDecl Sub-Iso = declare-record-iso Sub-Iso (quote Sub)
unquoteDecl H-Level-Sub = declare-record-hlevel 2 H-Level-Sub (quote Sub)

instance
  Funlike-Sub : Funlike ur Sub Id (λ _ → Ty)
  Funlike-Sub ._#_ = fun

sub-ext : {s₁ s₂ : Sub} → s₁ .fun ＝ s₂ .fun → s₁ .dom ＝ s₂ .dom → s₁ ＝ s₂
sub-ext {s₁ = is-sub f₁ d₁ c₁} {s₂ = is-sub f₂ d₂ c₂} ef ed =
  ap² (is-sub $²_)
      (×-path ef ed)
      (to-pathᴾ ((∀-is-of-hlevel 1 λ x → Π-is-of-hlevel 1 λ x∉ → hlevel 1) _ c₂))

id↦ : Sub
id↦ .fun = ``_
id↦ .dom = []
id↦ .cof _  = refl

_$↦_ : Sub → Ty → Ty
s $↦ (`` x)    = s $ x
s $↦ (p ⟶ q) = (s $↦ p) ⟶ (s $↦ q)
s $↦ con       = con

_◇_ : Sub → Sub → Sub
(g ◇ f) .fun = g $↦_ ∘ f #_
(g ◇ f) .dom = f .dom ∪∷ g .dom
(g ◇ f) .cof x∉ =
  let (x∉f , x∉g) = ∉ₛ-∪∷ {xs = f .dom} x∉ in
   ap (g $↦_) (f .cof x∉f) ∙ g .cof  x∉g

_≔_ : Id → Ty → Sub
(v ≔ t) .fun x = if v == x then t else `` x
(v ≔ t) .dom = v ∷ []
(v ≔ t) .cof {x} x∉ =
  given-no ∉ₛ-uncons x∉ .fst ∘ _⁻¹
    return (λ q → (if ⌊ q ⌋ then t else (`` x)) ＝ (`` x))
    then refl

sub-occurs : ∀ {v t} u → ¬ occurs v u → u ＝ (v ≔ t) $↦ u
sub-occurs {t} (`` x)    noc =
  given-no noc
    return (λ q → (`` x) ＝ (if ⌊ q ⌋ then t else (`` x)))
    then refl
sub-occurs     (p ⟶ q) noc = ap² _⟶_ (sub-occurs p (contra inl noc)) (sub-occurs q (contra inr noc))
sub-occurs      con      noc = refl

thin : LFSet Id → Sub → Sub
thin xs s .fun = s .fun
thin xs s .dom = xs ∪∷ s .dom
thin xs s .cof x∉ = s .cof (∉ₛ-∪∷ {xs = xs} x∉ .snd)

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

opaque
  unfolding rem
  sub-rem : ∀ {x c} t
            → wf-ty c t
            → x ∈ c
            → ∀ u → wf-ty (rem x c) u
            → wf-ty (rem x c) ((x ≔ u) $↦ t)
  sub-rem {x} {c} (`` y)    w x∈ u wr =
    Dec.elim
      {C = λ q → wf-ty (rem x c) (if ⌊ q ⌋ then u else (`` y))}
      (λ _ → wr)
      (λ ¬p → LFSet.Mem.∈-filter {s = c} (not-so (contra so→true! ¬p)) w
      )
      (x ≟ y)
  sub-rem {x} {c} (p ⟶ q) (wp , wq) x∈ u wr =
    sub-rem p wp x∈ u wr , sub-rem q wq x∈ u wr
  sub-rem {x} {c}  con      w x∈ u wr = tt

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

sub-same : ∀ {x t} → (x ≔ t) $↦ (`` x) ＝ t
sub-same {x} {t} =
  given-yes (the (x ＝ x) refl)
     return (λ q → (if ⌊ q ⌋ then t else (`` x)) ＝ t)
     then refl

-- well-formed substitutions

Wf-subst : Varctx → Sub → 𝒰
Wf-subst v s =
  {x : Id} → x ∈ s .dom → x ∈ v × wf-ty (minus v (s .dom)) (s $ x)

wf-idsub : ∀ {c} → Wf-subst c id↦
wf-idsub = false! ⦃ Refl-x∉ₛ[] ⦄ -- why

wf-sub-≔ : ∀ {x t v}
         → x ∈ v
         → wf-ty (rem x v) t
         → Wf-subst v (x ≔ t)
wf-sub-≔ {x} {t} {v} x∈ wt {x = y} xi =
  Recomputable-×
    Recomputable-∈ₛ (wf-ty-recomp {t = if x == y then t else `` y})
    .recompute $
    (erase (
       ∥-∥₁.elim {P = λ _ → (y ∈ₛ v) ×ₜ wf-ty (minus v (x ∷ [])) (if x == y then t else (`` y))}
           -- wf-ty should be data
           (λ q → ×-is-of-hlevel 1 hlevel!
                       (wf-ty-prop {v = minus v (x ∷ [])}
                                   {t = if x == y then t else `` y}))
           [ (λ e →   (subst (_∈ v) (e ⁻¹) x∈)
                    , (given-yes (e ⁻¹)
                        return (λ q → wf-ty (minus v (x ∷ [])) (if ⌊ q ⌋ then t else (`` y)))
                        then subst (λ q → wf-ty q t) (ap (rem x)
                               (  minus-[]-r {s = v} ⁻¹)
                                ∙ minus-∷-r {x = x} {s = v} {r = []} ⁻¹) wt))
           , false! ]ᵤ
           (∈ₛ⇉ xi .erased)))

substs-remove : ∀ {c : Varctx} {s} t
                 → Wf-subst c s → wf-ty c t → wf-ty (minus c (dom s)) (s $↦ t)
substs-remove {c} {s} (`` x)   ws  wt with x ∈? (s .dom)
... | yes xi = ws xi .snd
... | no nxi = subst (wf-ty (minus c (dom s))) (s .cof nxi ⁻¹)
                     (∈-minus wt nxi)
substs-remove         (p ⟶ q)  ws      (wp , wq) = substs-remove p ws wp , substs-remove q ws wq
substs-remove          con      _        wt        = tt

wf-sub-◇ : ∀ {c s1 s2} → Wf-subst c s1 → Wf-subst (minus c (dom s1)) s2 → Wf-subst c (s2 ◇ s1)
wf-sub-◇ {c} {s1} {s2} ws1 ws2 {x} xx with x ∈? s1 .dom
... | yes xi1 =
     ws1 xi1 .fst
  , (subst (λ q → wf-ty q (s2 $↦ (s1 # x))) (minus-minus {v = c} {s₁ = s1 .dom} {s₂ = s2 .dom}) $
     substs-remove {s = s2} (s1 $ x) ws2 (ws1 xi1 .snd))
... | no nxi1 =
  Recomputable-×
    Recomputable-∈ₛ (wf-ty-recomp {t = s2 $↦ (s1 $ x)})
      .recompute
        (erase
           (∥-∥₁.elim {P = λ _ → (x ∈ₛ c) ×ₜ wf-ty (minus c (s1 .dom ∪∷ s2 .dom)) (s2 $↦ (s1 $ x))}
               (λ _ → ×-is-of-hlevel 1 hlevel!
                       (wf-ty-prop {v = minus c (s1 .dom ∪∷ s2 .dom)}
                                   {t = s2 $↦ (s1 $ x)}))
               [ (λ x∈s₁ → absurd (nxi1 x∈s₁))
               , (λ x∈s₂ → let (x∈m , wm) = ws2 x∈s₂ in
                              minus-⊆ {ys = s1 .dom} x∈m
                            , (subst (λ q → wf-ty (minus c (s1 .dom ∪∷ s2 .dom)) (s2 $↦ q)) (s1 .cof nxi1 ⁻¹) $
                               subst (λ q → wf-ty q (s2 $ x)) minus-minus $
                               wm))
               ]ᵤ
               (∈ₛ-∪∷→ {s₁ = s1 .dom} xx .erased)))

--- list

subs : Sub → List Constr → List Constr
subs s = map (bimap (s $↦_) (s $↦_))

wf-constr-list-remove : ∀ {c v t}
                      → v ∈ c → ¬ occurs v t → wf-ty c t
                      → ∀ {l} → wf-constr-list c l
                      → wf-constr-list (rem v c) (subs (v ≔ t) l)
wf-constr-list-remove {t} vi noc w =
    all→map ∘ all-map
     λ where {x = l , r} (wl , wr) →
                let wrem = occurs-wf-ty t w noc in
                  (sub-rem l wl vi t wrem)
                , (sub-rem r wr vi t wrem)

-- substitution properties

↦𝒫 : 𝒰₁
↦𝒫 = Sub → 𝒰

↦𝒫∅ : ↦𝒫 → 𝒰
↦𝒫∅ p = ∀ s → ¬ p s

↦𝒫≃ : ↦𝒫 → ↦𝒫 → 𝒰
↦𝒫≃ p q = ∀ s → p s ≃ q s

↦𝒫∅≃ : ∀ {p q : ↦𝒫} → ↦𝒫≃ p q → ↦𝒫∅ p ≃ ↦𝒫∅ q
↦𝒫∅≃ {p} {q} eq =
  prop-extₑ! (λ np f qf → np f (eq f ⁻¹ $ qf)) (λ nq f pf → nq f (eq f $ pf))

↦𝒫× : ↦𝒫 → ↦𝒫 → ↦𝒫
↦𝒫× p q s = p s × q s

↦𝒫◇ : ↦𝒫 → Sub → ↦𝒫
↦𝒫◇ p f g = p (g ◇ f)

↦𝒫◇≃ : {p q : ↦𝒫} {f : Sub} → ↦𝒫≃ p q → ↦𝒫≃ (↦𝒫◇ p f) (↦𝒫◇ q f)
↦𝒫◇≃ {f} eq g = eq (g ◇ f)

↦𝒫◇-id≃ : {p : ↦𝒫} → ↦𝒫≃ (↦𝒫◇ p id↦) p
↦𝒫◇-id≃ {p} s = =→≃ (ap p ◇-id-r)

-- indexed substitution properties

↦𝒫i : Varctx → 𝒰₁
↦𝒫i v = (s : Sub) → s .dom ⊆ v → 𝒰

↦𝒫i∅ : ∀ {v} → ↦𝒫i v → 𝒰
↦𝒫i∅ {v} p = ∀ s (s⊆ : s .dom ⊆ v) → ¬ (p s s⊆)

-- erased thinned "order"
-- these things conceptually are categories, not orders

_≤↦_ : Sub → Sub → 𝒰
f ≤↦ g =
   Erased (Σ[ h ꞉ Sub ] Σ[ xs ꞉ LFSet Id ] (h ◇ g ＝ thin xs f))
   -- should be fibre₁ probably, to get propositionality

≤↦-refl : ∀ {f} → f ≤↦ f
≤↦-refl {f} = erase (id↦ , [] , ◇-id-l ∙ thin-[] ⁻¹)

≤↦-thin : ∀ {f w} → f ≤↦ thin w f
≤↦-thin {f} {w} = erase (id↦ , w , ◇-id-l)

≤↦-trans : ∀ {f g h : Sub}
          → f ≤↦ g → g ≤↦ h → f ≤↦ h
≤↦-trans {f} {g} {h} (erase (fg , wfg , efg)) (erase (gh ,  wgh , ehg)) =
  erase ( fg ◇ gh
        , wgh ∪∷ wfg
        , (  ◇-assoc {h = h}
           ∙ ap (fg ◇_) ehg
           ∙ thin-◇-r {xs = wgh} {f = fg} {g = g}
           ∙ ap (thin wgh) efg
           ∙ thin-∪∷ {xs = wgh} {ys = wfg} {f = f}
           )
        )

≤↦-id : {f : Sub} → f ≤↦ id↦
≤↦-id {f} = erase (f , [] , ◇-id-r ∙ thin-[] ⁻¹)

≤↦-◇-r : ∀ {f g h : Sub}
        → f ≤↦ g → (f ◇ h) ≤↦ (g ◇ h)
≤↦-◇-r {f} {h} (erase (fg , wfg , efg)) =
  erase ( fg
        , wfg
        , (◇-assoc {h = h} ⁻¹
           ∙ ap (_◇ h) efg
           ∙ thin-◇-l {xs = wfg} {f = f} {g = h})
        )

-- thin-stable

↦thin : ↦𝒫 → 𝒰
↦thin p = ∀ f w → p f → p (thin w f)

thin↦ : ↦𝒫 → 𝒰
thin↦ p = ∀ f w → p (thin w f) → p f

-- maximal substitution satisfying a property
Max↦ : ↦𝒫 → ↦𝒫
Max↦ p f = p f × (∀ f′ → p f′ → f′ ≤↦ f)

Max↦≃ : ∀ {p q : ↦𝒫} → ↦𝒫≃ p q → ↦𝒫≃ (Max↦ p) (Max↦ q)
Max↦≃ eq f = ×-ap (eq f) (Π-cod-≃ λ f′ → Π-dom-≃ (eq f′ ⁻¹))

DCl : ↦𝒫 → 𝒰
DCl p = ∀ f g → f ≤↦ g → p g → p f

-- TODO unused
failure-propagation-lemma1 : ∀ {p q : ↦𝒫} {a : Sub}
                           → ↦𝒫∅ (↦𝒫◇ p a)
                           → ↦𝒫∅ (↦𝒫◇ (↦𝒫× p q) a)
failure-propagation-lemma1 np g pq = np g (pq .fst)

failure-propagation-lemma2 : ∀ {p q : ↦𝒫} {a f : Sub}
                           → Max↦ (↦𝒫◇ p a) f
                           → ↦thin q
                           → ↦𝒫∅ (↦𝒫◇ q (f ◇ a))
                           → ↦𝒫∅ (↦𝒫◇ (↦𝒫× p q) a)
failure-propagation-lemma2 {q} {a} (paf , pmax) tq np g pq =
  Recomputable-⊥ .recompute $ erase
    let (s , w , e) = pmax g (pq .fst) .erased in
    np s (subst q (◇-assoc {h = a}) $
          subst (λ qq → q (qq ◇ a)) (e ⁻¹) $
          subst q (thin-◇-l {xs = w} {g = a} ⁻¹) $
          tq (g ◇ a) w (pq .snd))

optimist-lemma : ∀ {p q : ↦𝒫} {a f g : Sub}
               → DCl p → Max↦ (↦𝒫◇ p a) f
               → ↦thin q
               → Max↦ (↦𝒫◇ q (f ◇ a)) g
               → Max↦ (↦𝒫◇ (↦𝒫× p q) a) (g ◇ f)
optimist-lemma {q} {a} {f} {g} dc (pfa , pmax) tq (qgfa , qmax) =
   (  (dc ((g ◇ f) ◇ a) (f ◇ a) (erase (g , [] , ◇-assoc {h = a} ⁻¹ ∙ thin-[] ⁻¹)) pfa)
    , subst q (◇-assoc {h = a} ⁻¹) qgfa)
  , λ f′ → λ where (pfa , qfa) →
                      Recomputable-Erased .recompute $ erase
                        (let (j , w , ea) = pmax f′ pfa .erased in
                         ≤↦-trans {f = f′} {g = thin w f′} {h = g ◇ f} (≤↦-thin {f = f′} {w = w}) $
                         subst (_≤↦ (g ◇ f)) ea $
                         ≤↦-◇-r {f = j} {g = g} {h = f} $
                         qmax j $
                         subst q (thin-◇-l {xs = w} {g = a} ⁻¹ ∙ ap (_◇ a) (ea ⁻¹) ∙ ◇-assoc {g = f} {h = a}) $
                         tq (f′ ◇ a) w qfa)
