{-# OPTIONS --safe #-}
module Ribeiro.Unify where

open import Prelude
open import Meta.Effect

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.List as List
open import Data.List.Correspondences.Unary.Any
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Binary.OPE
open import Data.List.Operations.Properties

open import Data.Sum
open import Data.Plus
open import Data.AF
open import Data.Acc
open import Order.Constructions.Lex

-- ids

Id : 𝒰
Id = ℕ

-- types

data Ty : 𝒰 where
  ``_  : Id → Ty
  _⟶_ : Ty → Ty → Ty
  con  : Ty

module Ty-code where

  Code : Ty → Ty → 𝒰
  Code (`` x)      (`` y)     = x ＝ y
  Code (p₁ ⟶ q₁) (p₂ ⟶ q₂) = Code p₁ p₂ × Code q₁ q₂
  Code con         con        = ⊤
  Code _           _          = ⊥

  code-refl : (t : Ty) → Code t t
  code-refl (`` x)   = refl
  code-refl (p ⟶ q) = code-refl p , code-refl q
  code-refl con      = tt

  encode : ∀ {t₁ t₂} → t₁ ＝ t₂ → Code t₁ t₂
  encode {t₁} e = subst (Code t₁) e (code-refl t₁)

  decode : ∀ {t₁ t₂} → Code t₁ t₂ → t₁ ＝ t₂
  decode {t₁ = `` x}      {t₂ = `` y}      c        = ap ``_ c
  decode {t₁ = p₁ ⟶ q₁} {t₂ = p₂ ⟶ q₂} (c₁ , c₂) = ap² _⟶_ (decode c₁) (decode c₂)
  decode {t₁ = con}       {t₂ = con}       c        = refl

``-inj : {x y : ℕ} → `` x ＝ `` y → x ＝ y
``-inj = Ty-code.encode

⟶-inj : ∀ {p₁ q₁ p₂ q₂} → p₁ ⟶ q₁ ＝ p₂ ⟶ q₂ → (p₁ ＝ p₂) × (q₁ ＝ q₂)
⟶-inj e =
  let (c₁ , c₂) = Ty-code.encode e in
  Ty-code.decode c₁ , Ty-code.decode c₂

``≠⟶ : ∀ {x p q} → `` x ≠ p ⟶ q
``≠⟶ = Ty-code.encode

``≠con : ∀ {x} → `` x ≠ con
``≠con = Ty-code.encode

⟶≠con : ∀ {p q} → p ⟶ q ≠ con
⟶≠con = Ty-code.encode

_==ty_ : Ty → Ty → Bool
(`` x)      ==ty (`` y)     = x == y
(p₁ ⟶ q₁) ==ty (p₂ ⟶ q₂) = p₁ ==ty p₂ and q₁ ==ty q₂
con         ==ty con        = true
_           ==ty _          = false

ty-eq-reflects : ∀ {x} {y} → Reflects (x ＝ y) (x ==ty y)
ty-eq-reflects {x = `` x}      {y = `` y}     =
  Reflects.dmap (ap ``_) (contra ``-inj) Reflects-ℕ-Path
ty-eq-reflects {x = `` _}      {y = _ ⟶ _}  = ofⁿ ``≠⟶
ty-eq-reflects {x = `` _}      {y = con}      = ofⁿ ``≠con
ty-eq-reflects {x = _ ⟶ _}   {y = `` _}     = ofⁿ (``≠⟶ ∘ _⁻¹)
ty-eq-reflects {x = p₁ ⟶ q₁} {y = p₂ ⟶ q₂} =
  Reflects.dmap
    (λ where (e₁ , e₂) → ap² _⟶_ e₁ e₂)
    (contra ⟶-inj)
    (Reflects-× ⦃ rp = ty-eq-reflects ⦄ ⦃ rq = ty-eq-reflects ⦄)
ty-eq-reflects {x = _ ⟶ _}   {y = con}      = ofⁿ ⟶≠con
ty-eq-reflects {x = con}       {y = `` _}     = ofⁿ (``≠con ∘ _⁻¹)
ty-eq-reflects {x = con}       {y = _ ⟶ _}  = ofⁿ (⟶≠con ∘ _⁻¹)
ty-eq-reflects {x = con}       {y = con}      = ofʸ refl

instance
  Ty-is-discrete : is-discrete Ty
  Ty-is-discrete {x} {y} .does = x ==ty y
  Ty-is-discrete .proof = ty-eq-reflects

ty-size : Ty → ℕ
ty-size (p ⟶ q) = suc (ty-size p + ty-size q)
ty-size _        = 1

0<ty-size : ∀ {t} → 0 < ty-size t
0<ty-size {t = `` _}    = z<s
0<ty-size {t = _ ⟶ _} = z<s
0<ty-size {t = con}     = z<s

-- occurs check

occurs : Id → Ty → 𝒰
occurs v (`` x)    = v ＝ x
occurs v (p ⟶ q) = occurs v p ⊎ occurs v q
occurs v con       = ⊥

occurs? : Id → Ty → Bool
occurs? v (`` x)    = v == x
occurs? v (p ⟶ q) = occurs? v p or occurs? v q
occurs? v con       = false

occurs-reflects : ∀ {v} {t}
                → Reflects (occurs v t) (occurs? v t)
occurs-reflects {t = `` x}    = Reflects-ℕ-Path
occurs-reflects {t = p ⟶ q} =
  Reflects-⊎ ⦃ rp = occurs-reflects {t = p} ⦄ ⦃ rq = occurs-reflects {t = q} ⦄
occurs-reflects {t = con}     = ofⁿ id

occurs-dec : ∀ {v t} → Dec (occurs v t)
occurs-dec {v} {t} .does  = occurs? v t
occurs-dec {v} {t} .proof = occurs-reflects {v} {t}

-- constraints

Constr : 𝒰
Constr = Ty × Ty

constr-size : Constr → ℕ
constr-size (p , q) = ty-size p + ty-size q

list-measure : List Constr → ℕ
list-measure = List.rec 0 λ c → constr-size c +_

-- context of type vars

Varctx : 𝒰
Varctx = List Id

member-end : ∀ {d} {x : Id} → x ∈ (d ∷r x)
member-end = any-∷r-last refl

member-id : ∀ {d1 d2} {x : Id} → x ∈ (d1 ++ x ∷ d2)
member-id = any-++-r (here refl)

rem : Id → Varctx → Varctx
rem v = filter (not ∘ _=? v)

remove-length-∉ : ∀ {c v} → v ∉ c → length (rem v c) ＝ length c
remove-length-∉ {c} {v} vn =
  ap length $ filter-all $
  true→so! ⦃ Reflects-all {xs = c} {P = _≠ v} λ x → Reflects-¬ ⦃ rp = Reflects-ℕ-Path ⦄ ⦄
    (¬Any→All¬ (contra (any-map _⁻¹) vn))

remove-length-∈ : ∀ {c v} → v ∈ c → length (rem v c) < length c
remove-length-∈ {c} {v} vi =
  subst (_< length c) (length-filter (λ x → not (x =? _)) c ⁻¹) $
  count<length (λ z → not (z == _)) c $
  any-map (λ {x} e → subst So (not-invol (x == v) ⁻¹) (true→so! (e ⁻¹))) vi

remove-comm : ∀ {x y c}
            → rem x (rem y c) ＝ rem y (rem x c)
remove-comm {c} = filter-comm {xs = c}

remove-dist : ∀ {x c1 c2} → rem x (c1 ++ c2) ＝ rem x c1 ++ rem x c2
remove-dist {c1} = filter-++ c1

minus : Varctx → List Id → Varctx
minus c = List.rec c rem

minus-remove : ∀ {c1} c2 {x} → minus (rem x c1) c2 ＝ rem x (minus c1 c2)
minus-remove      []           = refl
minus-remove {c1} (c ∷ c2) {x} =
    ap (rem c) (minus-remove c2)
  ∙ remove-comm {x = c} {y = x} {c = minus c1 c2}

-- well-formedness

wf-ty : Varctx → Ty → 𝒰
wf-ty c (`` x)    = x ∈ c
wf-ty c (p ⟶ q) = wf-ty c p × wf-ty c q
wf-ty c con       = ⊤

wf-constr-list : Varctx → List Constr → 𝒰
wf-constr-list c l = All (λ x → wf-ty c (x .fst) × wf-ty c (x .snd)) l

wf-ty-end : ∀ {a c} t → wf-ty c t → wf-ty (c ∷r a) t
wf-ty-end (`` x)    w         = any-∷r-init w
wf-ty-end (p ⟶ q) (wp , wq) = wf-ty-end p wp , wf-ty-end q wq
wf-ty-end con       w         = tt

wf-ty-weaken : ∀ {c1} c2 t → wf-ty c1 t → wf-ty (c1 ++ c2) t
wf-ty-weaken {c1} []       t w = subst (λ q → wf-ty q t) (++-id-r c1 ⁻¹) w
wf-ty-weaken {c1} (c ∷ c2) t w =
  subst (λ q → wf-ty q t) (++-snoc c1 c2 c) $
  wf-ty-weaken {c1 = c1 ∷r c} c2 t (wf-ty-end t w)

wf-constr-weaken : ∀ {d cs}
                 → wf-constr-list d cs
                 → ∀ d′ → wf-constr-list (d ++ d′) cs
wf-constr-weaken wcl d′ =
  all-map (λ {x} (w1 , w2) → wf-ty-weaken d′ (x .fst) w1 , wf-ty-weaken d′ (x .snd) w2) wcl

wf-constr-weaken-∷r : ∀ {d cs}
                    → wf-constr-list d cs
                   → ∀ {c} → wf-constr-list (d ∷r c) cs
wf-constr-weaken-∷r {d} {cs} wcl {c} =
  subst (λ q → wf-constr-list q cs) (snoc-append d ⁻¹) $
  wf-constr-weaken wcl (c ∷ [])

wf-ty-remove-weak : ∀ {x c} t → wf-ty (rem x c) t → wf-ty c t
wf-ty-remove-weak (`` x)    w         = ope→subset filter-OPE w
wf-ty-remove-weak (p ⟶ q) (wp , wq) = wf-ty-remove-weak p wp , wf-ty-remove-weak q wq
wf-ty-remove-weak con       w         = tt

wf-ty-minus-weaken : ∀ {c1} c2 {t} → wf-ty (minus c1 c2) t → wf-ty c1 t
wf-ty-minus-weaken []                w = w
wf-ty-minus-weaken {c1} (c ∷ c2) {t} w =
  wf-ty-minus-weaken c2 {t = t} $ wf-ty-remove-weak t w

occurs-wf-ty : ∀ {v c} t → wf-ty c t → ¬ occurs v t → wf-ty (rem v c) t
occurs-wf-ty (`` x)    w         noc =
  ∈-filter (not-so (contra (_⁻¹ ∘ so→true!) noc)) w
occurs-wf-ty (p ⟶ q) (wp , wq) noc =
  occurs-wf-ty p wp (contra inl noc) , occurs-wf-ty q wq (contra inr noc)
occurs-wf-ty  con      w         noc = tt

-- set of constraints

Constrs : 𝒰
Constrs = Varctx × List Constr

-- substitution

sub : Ty → Id → Ty → Ty
sub t1 x (`` y)    = if x =? y then t1 else `` y
sub t1 x (p ⟶ q) = sub t1 x p ⟶ sub t1 x q
sub t1 x con       = con

sub-occurs : ∀ {t v} u → ¬ occurs v u → u ＝ sub t v u
sub-occurs {t} (`` x)    noc =
  given-no noc
    return (λ q → (`` x) ＝ (if ⌊ q ⌋ then t else (`` x)))
    then refl
sub-occurs     (p ⟶ q) noc =
  ap² _⟶_ (sub-occurs p (contra inl noc)) (sub-occurs q (contra inr noc))
sub-occurs      con      noc = refl

subst-rem : ∀ {x c} t
          → wf-ty c t → x ∈ c
          → ∀ u → wf-ty (rem x c) u → wf-ty (rem x c) (sub u x t)
subst-rem {x} {c} (`` y)    w         xin u wr =
  Dec.elim
    {C = λ q → wf-ty (rem x c) (if ⌊ q ⌋ then u else (`` y))}
    (λ _ → wr)
    (λ ¬p → ∈-filter (not-so (contra (_⁻¹ ∘ so→true!) ¬p)) w)
    (x ≟ y)
subst-rem        (p ⟶ q) (wp , wq) xin u wr =
  subst-rem p wp xin u wr , subst-rem q wq xin u wr
subst-rem         con      w         xin u wr = tt

Substitution : 𝒰
Substitution = List (Id × Ty)

dom : Substitution → List Id
dom = map fst

wf-subst : Varctx → Substitution → 𝒰
wf-subst c []            = ⊤
wf-subst c ((v , t) ∷ s) = v ∈ c × wf-ty (rem v c) t × wf-subst (rem v c) s

apply-subst : Substitution → Ty → Ty
apply-subst s t = fold-l (λ t′ (v , q) → sub q v t′) t s

substs-remove : ∀ {c t} s → wf-subst c s → wf-ty c t → wf-ty (minus c (dom s)) (apply-subst s t)
substs-remove          []             _             w = w
substs-remove {c} {t} ((i , t1) ∷ s) (ic , wt , ws) w =
  subst (λ q → wf-ty q (apply-subst s (sub t1 i t))) (minus-remove (dom s)) $
  substs-remove {c = rem i c} {t = sub t1 i t} s ws (subst-rem t w ic t1 wt)

minus-app : ∀ {c} s {v t} → minus c (dom (s ∷r (v , t))) ＝ rem v (minus c (dom s))
minus-app {c} s =
    ap (minus c) (map-∷r {xs = s})
  ∙ rec-∷r {xs = dom s}
  ∙ minus-remove (dom s)

apply-subst-id : ∀ {t} → apply-subst [] t ＝ t
apply-subst-id = refl

apply-subst-con : ∀ {s} → apply-subst s con ＝ con
apply-subst-con {s = []}    = refl
apply-subst-con {s = x ∷ s} = apply-subst-con {s = s}

apply-subst-app : ∀ {p q s} → apply-subst s (p ⟶ q) ＝ apply-subst s p ⟶ apply-subst s q
apply-subst-app {s = []}          = refl
apply-subst-app {s = (i , t) ∷ s} = apply-subst-app {s = s}

apply-subst-end : ∀ {s v t t′} → apply-subst (s ∷r (v , t)) t′ ＝ sub t v (apply-subst s t′)
apply-subst-end {s} {v} {t} {t′} = foldl-∷r t′ (λ t′ (v , q) → sub q v t′) s (v , t)

apply-subst-append : ∀ {s1 s2 t} → apply-subst (s1 ++ s2) t ＝ apply-subst s2 (apply-subst s1 t)
apply-subst-append {s1} {s2} {t} = foldl-++ t (λ t′ (v , q) → sub q v t′) s1 s2

apply-subst-idem : ∀ {d s t} → wf-ty (minus d (dom s)) t → apply-subst s t ＝ t
apply-subst-idem     {s = []}          {t = `` v}    wt       = refl
apply-subst-idem {d} {s = (i , t) ∷ s} {t = `` v}    wt       =
  Dec.elim
    {C = λ q → apply-subst s (if ⌊ q ⌋ then t else (`` v)) ＝ (`` v)}
    (λ evx → absurd ((so-not $ fst $ filter-∈ {xs = minus d (dom s)} wt) (true→so! (evx ⁻¹))))
    (λ _ → apply-subst-idem {d = d} {s = s} (filter-∈ wt .snd))
    (i ≟ v)
apply-subst-idem     {s}               {t = p ⟶ q} (wp , wq) =
    apply-subst-app {s = s}
  ∙ ap² _⟶_ (apply-subst-idem {s = s} wp) (apply-subst-idem {s = s} wq)
apply-subst-idem     {s}               {t = con}     wt        =
  apply-subst-con {s}

gen-only-add : ∀ {s c1 c2}
             → (∀ {t1 t2} → (t1 , t2) ∈ (c2 ++ c1) → apply-subst s t1 ＝ apply-subst s t2)
             → ∀ {t1 t2} → (t1 , t2) ∈ c1 → apply-subst s t1 ＝ apply-subst s t2
gen-only-add          {c2 = []}           h mem = h mem
gen-only-add {s} {c1} {c2 = (l , r) ∷ c2} h mem =
  gen-only-add {s = s} {c1 = c1} {c2 = c2} (h ∘ there) mem

wf-subst-last : ∀ {x t c} s
              → wf-subst c s
              → x ∈ minus c (dom s)
              → wf-ty (rem x (minus c (dom s))) t
              → wf-subst c (s ∷r (x , t))
wf-subst-last             []             ws             xi w = xi , w , tt
wf-subst-last {x} {t} {c} ((v , t′) ∷ s) (vi , wr , ws) xi w =
    vi , wr
  , wf-subst-last {c = rem v c} s ws
     (subst (x ∈_) (minus-remove (dom s) ⁻¹) xi)
     (subst (λ q → wf-ty (rem x q) t) (minus-remove (dom s) ⁻¹) w)

wf-subst-append : ∀ {c s1} s2 → wf-subst c s1 → wf-subst (minus c (dom s1)) s2 → wf-subst c (s1 ++ s2)
wf-subst-append {c} {s1} []             w1 w2             = subst (wf-subst c) (++-id-r s1 ⁻¹) w1
wf-subst-append {c} {s1} ((v , t) ∷ s2) w1 (ci , wt , w2) =
  subst (wf-subst c) (ap (_++ s2) (snoc-append s1) ∙ ++-assoc s1 ((v , t) ∷ []) s2) $
  wf-subst-append {c = c} {s1 = s1 ∷r (v , t)} s2
    (wf-subst-last s1 w1 ci wt)
    (subst (λ q → wf-subst q s2) (minus-app s1 ⁻¹) w2)

app-subst-eq : ∀ {l l′ r r′ s}
             → apply-subst s l ＝ apply-subst s l′
             → apply-subst s r ＝ apply-subst s r′
             → apply-subst s (l ⟶ r) ＝ apply-subst s (l′ ⟶ r′)
app-subst-eq {s} eql eqr =
    apply-subst-app {s = s}
  ∙ ap² _⟶_ eql eqr
  ∙ apply-subst-app {s = s} ⁻¹

unapp-subst-eq : ∀ {l l′ r r′ s}
               → apply-subst s (l ⟶ r) ＝ apply-subst s (l′ ⟶ r′)
               → (apply-subst s l ＝ apply-subst s l′) × (apply-subst s r ＝ apply-subst s r′)
unapp-subst-eq {s} eq =
  ⟶-inj (apply-subst-app {s = s} ⁻¹ ∙ eq ∙ apply-subst-app {s = s})

ext-subst-var-ty : ∀ {s s′}
                 → (∀ {v} → apply-subst s (`` v) ＝ apply-subst s′ (`` v))
                 → ∀ t → apply-subst s t ＝ apply-subst s′ t
ext-subst-var-ty          ex (`` x)    = ex
ext-subst-var-ty {s} {s′} ex (p ⟶ q) =
    apply-subst-app {p = p} {q = q} {s = s}
  ∙ ap² _⟶_ (ext-subst-var-ty {s = s} {s′ = s′} ex p) (ext-subst-var-ty {s = s} {s′ = s′} ex q)
  ∙ apply-subst-app {p = p} {q = q} {s = s′} ⁻¹
ext-subst-var-ty {s} {s′} ex con       =
  apply-subst-con {s = s} ∙ apply-subst-con {s = s′} ⁻¹

apply-subst-constrs : Substitution → List Constr → List Constr
apply-subst-constrs s = map λ (x , y) → apply-subst s x , apply-subst s y

wf-constr-list-remove : ∀ {c v t}
                      → v ∈ c → ¬ occurs v t → wf-ty c t
                      → ∀ {l} → wf-constr-list c l
                      → wf-constr-list (rem v c) (apply-subst-constrs ((v , t) ∷ []) l)
wf-constr-list-remove {t} vi noc w =
  all→map ∘
  all-map
    λ {x} (wl , wr) →
        let wrem = occurs-wf-ty t w noc in
        subst-rem (x .fst) wl vi t wrem , subst-rem (x .snd) wr vi t wrem

-- constraint order

_<C_ : Constrs → Constrs → 𝒰
_<C_ = ×-lex (λ v₁ v₂ → length v₁ < length v₂) (λ c₁ c₂ → list-measure c₁ < list-measure c₂)

_≤C_ : Constrs → Constrs → 𝒰
(v₁ , c₁) ≤C (v₂ , c₂) = (length v₁ ≤ length v₂) × (list-measure c₁ ≤ list-measure c₂)

≤C-af : AF _≤C_
≤C-af = af-× (af-comap length af-≤) (af-comap list-measure af-≤)

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

varctxt-lt-constraints-varl : ∀ {c v t l}
                            → v ∈ c
                            → (rem v c , apply-subst-constrs ((v , t) ∷ []) l) <C (c , (t , `` v) ∷ l)
varctxt-lt-constraints-varl vi = inl (remove-length-∈ vi)

varctxt-lt-constraints-varr : ∀ {c v t l}
                            → v ∈ c
                            → (rem v c , apply-subst-constrs ((v , t) ∷ []) l) <C (c , (`` v , t) ∷ l)
varctxt-lt-constraints-varr vi = inl (remove-length-∈ vi)

-- unifier

unifier : List Constr → Substitution → 𝒰
unifier cs s = All (λ (l , r) → apply-subst s l ＝ apply-subst s r) cs

unifier-append : ∀ {v t s} l
               → unifier (apply-subst-constrs ((v , t) ∷ []) l) s
               → unifier l ((v , t) ∷ s)
unifier-append     []                   u  = []
unifier-append {s} ((tl , tr) ∷ l) (e ∷ u) = e ∷ unifier-append {s = s} l u

unify-ty : ∀ {v t' s} t
         → apply-subst s (`` v) ＝ apply-subst s t'
         → apply-subst s t ＝ apply-subst s (sub t' v t)
unify-ty {v} {t'} {s} (`` x)    ea =
  Dec.elim
    {C = λ q → apply-subst s (`` x) ＝ apply-subst s (if ⌊ q ⌋ then t' else (`` x))}
    (λ evx → ap (apply-subst s ∘ ``_) (evx ⁻¹)  ∙ ea)
    (λ _ → refl)
    (v ≟ x)
unify-ty         {s} (p ⟶ q) ea =
  app-subst-eq {s = s} (unify-ty {s = s} p ea) (unify-ty {s = s} q ea)
unify-ty              con      ea = refl

unifier-subst : ∀ {v t s} l
              → apply-subst s (`` v) ＝ apply-subst s t
              → unifier l s
              → unifier (apply-subst-constrs ((v , t) ∷ []) l) s
unifier-subst     []              ea       u  = []
unifier-subst {s} ((tl , tr) ∷ l) ea (et ∷ u) =
  unify-ty {s = s} tl ea ⁻¹ ∙ et ∙ unify-ty {s = s} tr ea ∷ unifier-subst {s = s} l ea u

-- failure

data UnifyFailure : List Constr → 𝒰 where
  occ-fail-l : ∀ {v t lc}
             → occurs v t → UnifyFailure ((`` v , t) ∷ lc)
  occ-fail-r : ∀ {v t lc}
             → occurs v t → UnifyFailure ((t , `` v) ∷ lc)
  con-app    : ∀ {l r lc}
             → UnifyFailure ((con , l ⟶ r) ∷ lc)
  app-con    : ∀ {l r lc}
             → UnifyFailure ((l ⟶ r , con) ∷ lc)
  -- seems unused ?
  -- app-left   : ∀ {l l' r r' lc}
  --            → UnifyFailure ((l , l') ∷ lc) → UnifyFailure ((l ⟶ r , l' ⟶ r') ∷ lc)
  app-right  : ∀ {l l' r r' lc}
             → UnifyFailure ((l , l') ∷ (r , r') ∷ lc) → UnifyFailure ((l ⟶ r , l' ⟶ r') ∷ lc)
  constr-rec : ∀ {t t' l}
             → UnifyFailure l → UnifyFailure ((t , t') ∷ l)
  subs-rec   : ∀ {t t' s l}
             → UnifyFailure (apply-subst-constrs s l) → UnifyFailure ((t , t') ∷ l)

-- main algorithm

unify-type : Constrs → 𝒰
unify-type (ctx , lc) =
  wf-constr-list ctx lc →
  (Σ[ s ꞉ Substitution ]
     (unifier lc s × wf-subst ctx s
      × (∀ {s′} → unifier lc s′
          → Σ[ s″ ꞉ Substitution ]
            (∀ {v} → apply-subst s′ (`` v) ＝ apply-subst (s ++ s″) (`` v)))) )
  ⊎ UnifyFailure lc

unify-body : (l : Constrs)
           → (ih : (l' : Constrs) → l' <C l → unify-type l')
           → unify-type l
unify-body (ctx , [])             ih _   = inl ([] , [] , tt , λ {s′} _ → s′ , refl)
unify-body (ctx , (tl , tr) ∷ lc) ih wcl with tl ≟ tr
unify-body (ctx , (tl , tr) ∷ lc) ih wcl | yes e with ih (ctx , lc)
                                                         (lt-list-constr-lt-constraints {t = tl} {t′ = tr} {l = lc})
                                                         (all-tail wcl)
unify-body (ctx , (tl , tr) ∷ lc) ih wcl | yes e | inl (s , us , ws , sprf) =
  inl (s , ap (apply-subst s) e ∷ us , ws , λ {s′} → sprf {s′} ∘ all-tail)
unify-body (ctx , (tl , tr) ∷ lc) ih wcl | yes e | inr uf = inr (constr-rec uf)
unify-body (ctx , (`` v      , tr)        ∷ lc) ih wcl | no ne with occurs-dec {v} {t = tr}
unify-body (ctx , (`` v      , tr)        ∷ lc) ih wcl | no ne | yes oc = inr (occ-fail-l oc)
unify-body (ctx , (`` v      , tr)        ∷ lc) ih wcl | no ne | no noc with ih (rem v ctx , apply-subst-constrs ((v , tr) ∷ []) lc)
                                                                                (varctxt-lt-constraints-varr {t = tr} {l = lc} (all-head wcl .fst))
                                                                                (wf-constr-list-remove (all-head wcl .fst) noc (all-head wcl .snd) (all-tail wcl))
unify-body (ctx , (`` v      , tr)        ∷ lc) ih wcl | no ne | no noc | inl (s , us , ws , sprf) =
  inl ( (v , tr) ∷ s
      , unifier-append {s = s} ((`` v , tr) ∷ lc)
          (ap (apply-subst s) (given-yes (the (v ＝ v) refl)
                                 return (λ q → (if ⌊ q ⌋ then tr else (`` v)) ＝ sub tr v tr)
                                 then sub-occurs tr noc)
           ∷ us)
      , (all-head wcl .fst , occurs-wf-ty tr (all-head wcl .snd) noc , ws)
      , λ {s′} u′ → let (ah , at) = all-uncons u′
                        (s″ , prf) = sprf {s′ = s′} (unifier-subst {s = s′} lc ah at)
                      in
                    s″ , λ {v = v′} →
                           unify-ty {v = v} {s = s′} (`` v′) ah
                         ∙ ext-subst-var-ty {s = s′} {s′ = s ++ s″} prf (sub tr v (`` v′)))
unify-body (ctx , (`` v      , tr)        ∷ lc) ih wcl | no ne | no noc | inr uf = inr (subs-rec {s = (v , tr) ∷ []} uf)
unify-body (ctx , (pl ⟶ ql , pr ⟶ qr)  ∷ lc) ih wcl | no ne with ih (ctx , (pl , pr) ∷ (ql , qr) ∷ lc)
                                                                       (app-lt-constraints {l = pl} {l′ = pr} {r = ql} {r′ = qr} {lc = lc})
                                                                       (  (all-head wcl .fst .fst , all-head wcl .snd .fst)
                                                                        ∷ (all-head wcl .fst .snd , all-head wcl .snd .snd)
                                                                        ∷ all-tail wcl)
unify-body (ctx , (pl ⟶ ql , pr ⟶ qr)  ∷ lc) ih wcl | no ne | inl (s , us , ws , sprf) =
  inl ( s
      , app-subst-eq {s = s} (all-head us) (all-head $ all-tail us) ∷ all-tail (all-tail us)
      , ws
      , λ {s′} u′ → sprf {s′ = s′} (let (a1 , a2) = unapp-subst-eq {s = s′} (all-head u′) in
                                    a1 ∷ a2 ∷ all-tail u′))
unify-body (ctx , (pl ⟶ ql , pr ⟶ qr)  ∷ lc) ih wcl | no ne | inr uf = inr (app-right uf)
unify-body (ctx , (pl ⟶ ql , con)       ∷ lc) ih wcl | no ne = inr app-con
unify-body (ctx , (con       , pr ⟶ qr) ∷ lc) ih wcl | no ne = inr con-app
unify-body (ctx , (con       , con)       ∷ lc) ih wcl | no ne = absurd (ne refl)
unify-body (ctx , (tl        , `` v)      ∷ lc) ih wcl | no ne with occurs-dec {v} {t = tl}
unify-body (ctx , (tl        , `` v)      ∷ lc) ih wcl | no ne | yes oc = inr (occ-fail-r oc)
unify-body (ctx , (tl        , `` v)      ∷ lc) ih wcl | no ne | no noc with ih (rem v ctx , apply-subst-constrs ((v , tl) ∷ []) lc)
                                                                                (varctxt-lt-constraints-varl {t = tl} {l = lc} (all-head wcl .snd))
                                                                                (wf-constr-list-remove (all-head wcl .snd) noc (all-head wcl .fst) (all-tail wcl))
unify-body (ctx , (tl        , `` v)      ∷ lc) ih wcl | no ne | no noc | inl (s , us , ws , sprf) =
  inl ( (v , tl) ∷ s
      , unifier-append {s = s} ((tl , `` v) ∷ lc)
           (ap (apply-subst s) (given-yes (the (v ＝ v) refl)
                                 return (λ q → sub tl v tl ＝ (if ⌊ q ⌋ then tl else (`` v)))
                                 then (sub-occurs tl noc ⁻¹)) ∷ us)
      , (all-head wcl .snd , occurs-wf-ty tl (all-head wcl .fst) noc , ws)
      , λ {s′} u′ → let (ah , at) = all-uncons u′
                        (s″ , prf) = sprf {s′ = s′} (unifier-subst {s = s′} lc (ah ⁻¹) at)
                      in
                    s″ , λ {v = v′} →
                           unify-ty {v = v} {s = s′} (`` v′) (ah ⁻¹)
                         ∙ ext-subst-var-ty {s = s′} {s′ = s ++ s″} prf (sub tl v (`` v′)))
unify-body (ctx , (tl        , `` v)      ∷ lc) ih wcl | no ne | no noc | inr uf = inr (subs-rec {s = (v , tl) ∷ []} uf)

unify : (l : Constrs) → unify-type l
unify = to-induction <C-wf unify-type unify-body
