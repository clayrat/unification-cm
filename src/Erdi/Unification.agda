{-# OPTIONS --safe #-}
module Erdi.Unification where

open import Prelude
open import Meta.Effect

open import Data.Reflects
open import Data.Fin.Inductive
open import Data.Maybe as Maybe
open import Data.Maybe.Correspondences.Unary.Partial
open import Data.Star
open import Data.Sum as Sum
open import Data.List
open import Data.List.Operations.Properties

open import Erdi.Ty

-- renaming
_↦_ : ℕ → ℕ → 𝒰
m ↦ n = Var m → Var n

-- substitution
_⇝_ : ℕ → ℕ → 𝒰
m ⇝ n = Var m → Ty n

-- morphism(?)
_⇉_ : ℕ → ℕ → 𝒰
m ⇉ n = Ty m → Ty n

rename : {m n : ℕ} → (m ↦ n) → (m ⇝ n)
rename = ``_ ∘_

substitute : {m n : ℕ} → (m ⇝ n) → (m ⇉ n)
substitute s (`` i)    = s i
substitute _ con       = con
substitute s (t ⟶ u) = (substitute s t) ⟶ (substitute s u)

-- TODO comp+refl notation

⇝id : ∀ {m} → m ⇝ m
⇝id = ``_

_◇_ : ∀ {l m n} → (m ⇝ n) → (l ⇝ m) → (l ⇝ n)
f ◇ g = substitute f ∘ g

substitute-id : {m : ℕ} (t : Ty m) → substitute ⇝id t ＝ t
substitute-id (`` x)    = refl
substitute-id (p ⟶ q) = ap² _⟶_ (substitute-id p) (substitute-id q)
substitute-id  con      = refl

substitute-comp : {l m n : ℕ} {f : m ⇝ n} {g : l ⇝ m} (t : Ty l)
                → substitute (f ◇ g) t ＝ substitute f (substitute g t)
substitute-comp (`` x)    = refl
substitute-comp (p ⟶ q) = ap² _⟶_ (substitute-comp p) (substitute-comp q)
substitute-comp con       = refl

substitute-rename : {l m n : ℕ} {f : m ⇝ n} {r : l ↦ m}
                  → f ◇ rename r ＝ f ∘ r
substitute-rename = fun-ext λ f → refl

◇-id-l : ∀ {m n} {f : m ⇝ n} → (⇝id ◇ f) ＝ f
◇-id-l {f} = fun-ext (substitute-id ∘ f)

◇-id-r : ∀ {m n} {f : m ⇝ n} → (f ◇ ⇝id) ＝ f
◇-id-r = refl

◇-assoc : ∀ {m n k p} {f : k ⇝ p} {g : n ⇝ k} {h : m ⇝ n}
         → (f ◇ g) ◇ h ＝ f ◇ (g ◇ h)
◇-assoc {h} = fun-ext (substitute-comp ∘ h)

-- thinning

thin : {n : ℕ} → Fin (suc n) → Fin n → Fin (suc n)
thin              fzero    y       = fsuc y
thin {n = suc n} (fsuc x)  fzero   = fzero
thin {n = suc n} (fsuc x) (fsuc y) = fsuc (thin x y)

thin-inj : ∀ {n} x {y z} → thin {n} x y ＝ thin x z → y ＝ z
thin-inj {n = suc n}  fzero                             e = fsuc-inj e
thin-inj {n = suc n} (fsuc x) {y = fzero}  {z = fzero}  _ = refl
thin-inj {n = suc n} (fsuc x) {y = fzero}  {z = fsuc _} e = false! e
thin-inj {n = suc n} (fsuc x) {y = fsuc _} {z = fzero}  e = false! e
thin-inj {n = suc n} (fsuc x) {y = fsuc y} {z = fsuc z} e = ap fsuc (thin-inj x (fsuc-inj e))

thin-nofix : ∀ {n} x {y} → thin {n} x y ≠ x
thin-nofix              fzero                e = false! e
thin-nofix {n = suc n} (fsuc x) {y = fzero}  e = false! e
thin-nofix {n = suc n} (fsuc x) {y = fsuc y} e = thin-nofix x (fsuc-inj e)

-- thickening

thick : {n : ℕ} → Fin (suc n) → Fin (suc n) → Maybe (Fin n)
thick              fzero    fzero   = nothing
thick              fzero   (fsuc y) = just y
thick {n = suc n} (fsuc x)  fzero   = just fzero
thick {n = suc n} (fsuc x) (fsuc y) = fsuc <$> thick x y

thick-spec : {n : ℕ} (x y : Fin (suc n)) → Maybe (Fin n) → 𝒰
thick-spec x y m = Part (y ＝ x) (λ y′ → y ＝ thin x y′) m

thick-thin : ∀ {n} x y → thick-spec x y (thick {n} x y)
thick-thin              fzero    fzero   = nothingP refl
thick-thin              fzero   (fsuc y) = justP refl
thick-thin {n = suc n} (fsuc x)  fzero   = justP refl
thick-thin {n = suc n} (fsuc x) (fsuc y) =
  Part-map (ap fsuc) (ap fsuc) (thick-thin x y)

thick-nofix : ∀ {n} x → thick {n} x x ＝ nothing
thick-nofix              fzero   = refl
thick-nofix {n = suc n} (fsuc x) = ap (map fsuc) (thick-nofix x)

thick-inv : ∀ {n} x y → thick {n} x (thin x y) ＝ just y
thick-inv              fzero    y       = refl
thick-inv {n = suc n} (fsuc x)  fzero   = refl
thick-inv {n = suc n} (fsuc x) (fsuc y) = ap (map fsuc) (thick-inv x y)

check : ∀ {n} → Var (suc n) → Ty (suc n) → Maybe (Ty n)
check x (`` y)    = ``_ <$> thick x y
check x (p ⟶ q) = _⟶_ <$> check x p <*> check x q
check x  con      = just con

infix 5 _≔_
_≔_ : {n : ℕ} → Var (suc n) → Ty n →  (suc n ⇝ n)
(x ≔ t) y = Maybe.rec t ``_ (thick x y)

for-thin : ∀ {n} {t : Ty n} {x y} → (x ≔ t) (thin x y) ＝ `` y
for-thin {t} {x} {y} = ap (Maybe.rec t ``_) (thick-inv x y)

for-same : ∀ {n} {t : Ty n} {x} → (x ≔ t) x ＝ t
for-same {t} {x} = ap (Maybe.rec t ``_) (thick-nofix x)

-- chain of substitutions

data _//_ : ℕ → ℕ → 𝒰 where
  _／_ : ∀ {m} → Ty m → Var (suc m) → suc m // m

_⇝⋆_ : ℕ → ℕ → 𝒰
m ⇝⋆ n = Star _//_ m n

-- collapse the chain into a mathematical substitution
sub : ∀ {m n} → m ⇝⋆ n → m ⇝ n
sub = star-foldr {S = _⇝_} ⇝id
        (λ where (t′ ／ v) yz → yz ◇ (v ≔ t′))

sub-refl : ∀ {m} → sub {m} refl ＝ ⇝id
sub-refl = transport-refl ``_

sub-sng : ∀ {m x t} → sub {n = m} (star-sng (t ／ x)) ＝ (x ≔ t)
sub-sng {x} {t} = ap (_◇ (x ≔ t)) sub-refl ∙ ◇-id-l

_⇝⋆□ : ℕ → 𝒰
m ⇝⋆□ = Σ[ n ꞉ ℕ ] (m ⇝⋆ n)

_／_◅?_ : ∀ {m} → Ty m → Var (suc m) → m ⇝⋆□ → suc m ⇝⋆□
t′ ／ x ◅? (n , σ) = n , (t′ ／ x) ◅ σ

-- unification

flex-flex : ∀ {m} → Var m → Var m → m ⇝⋆□
flex-flex {m = suc m} x y =
  Maybe.rec
    (suc m , ε refl)
    (λ y′ → m , star-sng ((`` y′) ／ x))
    (thick x y)

flex-rigid : ∀ {m} → Var m → Ty m → Maybe (m ⇝⋆□)
flex-rigid {m = suc m} x t =
  map (λ t′ → m , star-sng (t′ ／ x)) (check x t)

amgu : ∀ {m} → Ty m → Ty m → m ⇝⋆□ → Maybe (m ⇝⋆□)
amgu  con         con        acc                            = just acc
amgu  con        (pt ⟶ qt)  acc                            = nothing
amgu (ps ⟶ qs)  con         acc                            = nothing
amgu (ps ⟶ qs) (pt ⟶ qt)  acc                            = amgu ps pt acc >>= amgu qs qt
amgu (`` xs)     (`` xt)    (n , ε e)                       = just (flex-flex xs xt)
amgu (`` xs)      t         (n , ε e)                       = flex-rigid xs t
amgu  s          (`` xt)    (n , ε e)                       = flex-rigid xt s
amgu  s           t         (n , _◅_ {x = suc y} (r ／ z) σ) = -- omitting the match on x triggers a termination error
  map (r ／ z ◅?_) $
  amgu (substitute (z ≔ r) s) (substitute (z ≔ r) t) (n , σ)

mgu : ∀ {m} → Ty m → Ty m → Maybe (m ⇝⋆□)
mgu {m} s t = amgu s t (m , ε refl)

-- substitution properties

⇝P : ℕ → 𝒰₁
⇝P m = ∀ {n} → m ⇝ n → 𝒰

⇝P∅ : ∀ {m} → ⇝P m → 𝒰
⇝P∅ {m} p = ∀ {n} (f : m ⇝ n) → ¬ p f

⇝P× : ∀ {m} → ⇝P m → ⇝P m → ⇝P m
⇝P× p q f = p f × q f

⇝P◇ : ∀ {m n} → ⇝P m → m ⇝ n → ⇝P n
⇝P◇ {m} {n} p f {n = k} g = p (g ◇ f)

-- unifier

unifies : ∀ {m} → Ty m → Ty m → ⇝P m
unifies s t f = substitute f s ＝ substitute f t

unifies-comm : ∀ {m n} {s t : Ty m} {f : m ⇝ n}
             → unifies s t f ≃ unifies t s f
unifies-comm {s} {t} = prop-extₑ! _⁻¹ _⁻¹

unifies-fork : ∀ {m n} {s₁ t₁ s₂ t₂ : Ty m} {f : m ⇝ n}
             → unifies (s₁ ⟶ s₂) (t₁ ⟶ t₂) f ≃ unifies s₁ t₁ f × unifies s₂ t₂ f
unifies-fork {s₁} {t₁} {s₂} {t₂} =
  prop-extₑ! ⟶-inj λ (x , y) → ap² _⟶_ x y

unifies-comp : ∀ {m n k q} {s t : Ty m} {f : n ⇝ k} {g : m ⇝ n} {h : k ⇝ q}
             → ⇝P◇ (unifies s t) (f ◇ g) h ≃ ⇝P◇ (unifies (substitute g s) (substitute g t)) f h
unifies-comp {s} {t} {g} =
  prop-extₑ!
    (λ e → substitute-comp s ⁻¹ ∙ subst (unifies s t) (◇-assoc {h = g} ⁻¹) e ∙ substitute-comp t)
    λ e → subst (unifies s t) (◇-assoc {h = g}) (substitute-comp s ∙ e ∙ substitute-comp t ⁻¹)

-- substitution order

_≤⇝_ : ∀ {m n k} → m ⇝ n → m ⇝ k → 𝒰
f ≤⇝ g = fibre (_◇ g) f

≤⇝-refl : ∀ {m n} {f : m ⇝ n} → f ≤⇝ f
≤⇝-refl = ⇝id , ◇-id-l

≤⇝-trans : ∀ {m n k p} {f : m ⇝ n} {g : m ⇝ k} {h : m ⇝ p}
          → f ≤⇝ g → g ≤⇝ h → f ≤⇝ h
≤⇝-trans {h} (fg , efg) (gh , ehg) = fg ◇ gh , ◇-assoc {h = h} ∙ ap (fg ◇_) ehg ∙ efg

≤⇝-id : ∀ {m n} {f : m ⇝ n} → f ≤⇝ ⇝id
≤⇝-id {f} = f , ◇-id-r

≤⇝-◇-r : ∀ {m n k p} {f : n ⇝ k} {g : n ⇝ p} {h : m ⇝ n}
        → f ≤⇝ g → (f ◇ h) ≤⇝ (g ◇ h)
≤⇝-◇-r {h} (fg , efg) = fg , ◇-assoc {h = h} ⁻¹ ∙ ap (_◇ h) efg

-- maximal substitution satisfying a property
Max⇝ : ∀ {m} → ⇝P m → ⇝P m
Max⇝ {m} p {n} f = p f × (∀ {k} (f′ : m ⇝ k) → p f′ → f′ ≤⇝ f)

DCl : ∀ {m} → ⇝P m → 𝒰
DCl {m} p = ∀ {n k} (f : m ⇝ n) (g : m ⇝ k) → f ≤⇝ g → p g → p f

DCl-unifies : ∀ {m} {s t : Ty m} → DCl (unifies s t)
DCl-unifies {s} {t} f g (h , e) u =
  subst (unifies s t) e $
  substitute-comp s ∙ ap (substitute h) u ∙ substitute-comp t ⁻¹

optimist-lemma : ∀ {m n k l} {p q : ⇝P m} {a : m ⇝ n} {f : n ⇝ k} {g : k ⇝ l}
               → DCl p → Max⇝ (⇝P◇ p a) f → Max⇝ (⇝P◇ q (f ◇ a)) g
               → Max⇝ (⇝P◇ (⇝P× p q) a) (g ◇ f)
optimist-lemma {q} {a} {f} {g} dc (pfa , pmax) (qgfa , qmax) =
  ( dc ((g ◇ f) ◇ a) (f ◇ a) (g , ◇-assoc {h = a} ⁻¹) pfa
  , subst q (◇-assoc {h = a} ⁻¹) qgfa)
  , λ f′ → λ where (pfa , qfa) →
                      let (j , ea) = pmax f′ pfa in
                      subst (_≤⇝ (g ◇ f)) ea $
                      ≤⇝-◇-r {h = f} $
                      qmax j $
                      subst q (ap (_◇ a) (ea ⁻¹) ∙ ◇-assoc {h = a}) qfa

failure-propagation-lemma1 : ∀ {m n} {p q : ⇝P m} {a : m ⇝ n}
                           → ⇝P∅ (⇝P◇ p a) → ⇝P∅ (⇝P◇ (⇝P× p q) a)
failure-propagation-lemma1 np g pq = np g (pq .fst)

failure-propagation-lemma2 : ∀ {m n k} {p q : ⇝P m} {a : m ⇝ n} {f : n ⇝ k}
                           → Max⇝ (⇝P◇ p a) f → ⇝P∅ (⇝P◇ q (f ◇ a))
                           → ⇝P∅ (⇝P◇ (⇝P× p q) a)
failure-propagation-lemma2 {q} {a} {f} (paf , pmax) np g pq =
  let (s , e) = pmax g (pq .fst) in
  np s $ subst q (◇-assoc {h = a}) $ subst (λ qq → q (qq ◇ a)) (e ⁻¹) (pq .snd)

-- simple unification problem

trivial-problem-lemma : ∀ {m n} {t : Ty m} {f : m ⇝ n}
                      → Max⇝ (⇝P◇ (unifies t t) f) ⇝id
trivial-problem-lemma = refl , λ f′ _ → ≤⇝-id

variable-elim-lemma : ∀ {m} {x : Var (suc m)} {t : Ty m}
                    → Max⇝ (unifies (`` x) (substitute (rename (thin x)) t)) (x ≔ t)
variable-elim-lemma {x} {t} =
    for-same {x = x} ∙ substitute-id t ⁻¹ ∙ ap (λ q → substitute q t) (fun-ext λ y → for-thin {x = x} ⁻¹) ∙ substitute-comp t
  , λ f′ u → (f′ ∘ thin x)
  , fun-ext λ y →
      Maybe.elim
        (λ q → thick x y ＝ q → thick-spec x y q → (((f′ ∘ thin x) ◇ (x ≔ t)) y) ＝ f′ y)
        (λ et p →   ap (λ q → substitute (f′ ∘ thin x) (Maybe.rec t ``_ q)) et ∙ substitute-comp t ∙ u ⁻¹ ∙ ap f′ (Part-nothing p ⁻¹))
        (λ j et p → ap (λ q → substitute (f′ ∘ thin x) (Maybe.rec t ``_ q)) et ∙ ap f′ (Part-just p ⁻¹))
        (thick x y) refl (thick-thin x y)

Step : ℕ → 𝒰
Step n = Ty n ⊎ Ty n

-- one-hole context
Ctx1 : ℕ → 𝒰
Ctx1 n = List (Step n)

-- plugging the hole
_+:_ : ∀ {n} → Ctx1 n → Ty n → Ty n
[]           +: t = t
(inl r ∷ ps) +: t = (ps +: t) ⟶ r
(inr l ∷ ps) +: t = l ⟶ (ps +: t)

+:-++ : ∀ {n} {ps qs : Ctx1 n} {t} → (ps ++ qs) +: t ＝ ps +: (qs +: t)
+:-++ {ps = []}         = refl
+:-++ {ps = inl r ∷ ps} = ap (_⟶ r) (+:-++ {ps = ps})
+:-++ {ps = inr l ∷ ps} = ap (l ⟶_) (+:-++ {ps = ps})

substitute-steps : {m n : ℕ} → (m ⇝ n) → Ctx1 m → Ctx1 n
substitute-steps f = map (Sum.dmap (substitute f) (substitute f))

+:-subst : ∀ {m n} {f : m ⇝ n} {ps : Ctx1 m} {t}
         → substitute f (ps +: t) ＝ substitute-steps f ps +: substitute f t
+:-subst     {ps = []}         = refl
+:-subst {f} {ps = inl r ∷ ps} = ap (_⟶ substitute f r) (+:-subst {ps = ps})
+:-subst {f} {ps = inr l ∷ ps} = ap (substitute f l ⟶_) (+:-subst {ps = ps})

check-spec : {n : ℕ} → Var (suc n) → Ty (suc n) → Maybe (Ty n) → 𝒰
check-spec {n} x t m =
  Part (Σ[ ps ꞉ List (Step (suc n)) ] (t ＝ ps +: (`` x)))
       (λ t′ → t ＝ substitute (rename (thin x)) t′) m

check-correct : ∀ {n} x t → check-spec x t (check {n} x t)
check-correct x (`` y)    =
  Part-map
    (λ e → [] , ap ``_ e)
    (λ e → ap ``_ e)
    (thick-thin x y)
check-correct x (p ⟶ q) =
  Part-map2
    (λ where (psq , eq) → inl q ∷ psq , ap (_⟶ q) eq)
    (λ where (psp , ep) → inr p ∷ psp , ap (p ⟶_) ep)
    (λ ep eq → ap² _⟶_ ep eq)
    (check-correct x p)
    (check-correct x q)
check-correct x con       = justP refl

no-cycle-lemma : ∀ {n} {ps : Ctx1 n} {t} → ps +: t ＝ t → ps ＝ []
no-cycle-lemma {ps = []}                       e = refl
no-cycle-lemma {ps = inl r ∷ ps} {t = `` x}    e = ⊥.absurd (``≠⟶ (e ⁻¹))
no-cycle-lemma {ps = inr l ∷ ps} {t = `` x}    e = ⊥.absurd (``≠⟶ (e ⁻¹))
no-cycle-lemma {ps = inl r ∷ ps} {t = p ⟶ q} e =
  let (ep , _) = ⟶-inj e in
  false! (no-cycle-lemma {ps = ps ∷r inl q} {t = p}
          (ap (_+: p) (snoc-append ps) ∙ +:-++ {ps = ps}  ∙ ep))
no-cycle-lemma {ps = inr l ∷ ps} {t = p ⟶ q} e =
  let (_ , eq) = ⟶-inj e in
  false! (no-cycle-lemma {ps = ps ∷r inr p} {t = q}
          (ap (_+: q) (snoc-append ps) ∙ +:-++ {ps = ps}  ∙ eq))
no-cycle-lemma {ps = inl r ∷ ps} {t = con}     e = ⊥.absurd (⟶≠con e)
no-cycle-lemma {ps = inr l ∷ ps} {t = con}     e = ⊥.absurd (⟶≠con e)

no-unify-+var : ∀ {m} {x : Var m} {p ps}
             → ⇝P∅ (unifies (`` x) ((p ∷ ps) +: (`` x)))
no-unify-+var {p} {ps} f u =
  false! $ no-cycle-lemma ((u ∙ +:-subst {f = f} {ps = p ∷ ps}) ⁻¹)

amgu-spec : ∀ {m} → Ty m → Ty m → m ⇝⋆□ → Maybe (m ⇝⋆□) → 𝒰
amgu-spec {m} s t (l , ρ) ms =
  Part (⇝P∅ (⇝P◇ (unifies s t) (sub ρ)))
       (λ where (n , σ) → Σ[ τ ꞉ l ⇝⋆ n ] (σ ＝ ρ ∙ τ) × Max⇝ (⇝P◇ (unifies s t) (sub ρ)) (sub τ))
       ms

flex-flex-correct : ∀ {m} {x y : Var m}
                  → Max⇝ (unifies (`` x) (`` y)) (sub (flex-flex x y .snd))
flex-flex-correct {m = suc m} {x} {y} =
  Maybe.elim
     (λ q → thick-spec x y q
          → Max⇝ (unifies (`` x) (`` y))
                  (sub ((Maybe.rec {B = suc m ⇝⋆□}
                                  (suc m , ε refl)
                                  (λ y′ → m , star-sng ((`` y′) ／ x)) q) .snd)))
     (λ p → subst (Max⇝ (unifies (`` x) (`` y))) (sub-refl ⁻¹) $
               subst (λ q → Max⇝ (unifies (`` x) (`` q)) ⇝id) (Part-nothing p ⁻¹) $
               trivial-problem-lemma {t = `` x} {f = ⇝id})
     (λ j p → subst (Max⇝ (unifies (`` x) (`` y))) (sub-sng {x = x} ⁻¹) $
                 subst (λ q → Max⇝ (unifies (`` x) (`` q)) (x ≔ (`` j))) (Part-just p ⁻¹) $
                 variable-elim-lemma)
     (thick x y) (thick-thin x y)

