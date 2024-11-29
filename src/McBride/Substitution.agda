{-# OPTIONS --safe #-}
module McBride.Substitution where

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

open import McBride.Ty

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

-- thinning

thin : {n : ℕ} → Fin (suc n) → Fin n → Fin (suc n)
thin              fzero    y       = fsuc y
thin {n = suc n} (fsuc x)  fzero   = fzero
thin {n = suc n} (fsuc x) (fsuc y) = fsuc (thin x y)

-- thickening

thick : {n : ℕ} → Fin (suc n) → Fin (suc n) → Maybe (Fin n)
thick              fzero    fzero   = nothing
thick              fzero   (fsuc y) = just y
thick {n = suc n} (fsuc x)  fzero   = just fzero
thick {n = suc n} (fsuc x) (fsuc y) = fsuc <$> thick x y

-- singleton substitution

infix 5 _≔_
_≔_ : {n : ℕ} → Var (suc n) → Ty n → (suc n ⇝ n)
(x ≔ t) y = Maybe.rec t ``_ (thick x y)

-- thinning properties

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

-- thickening properties

thick-spec : {n : ℕ} (x y : Fin (suc n)) → Maybe (Fin n) → 𝒰
thick-spec x y m = Part (y ＝ x) (λ y′ → y ＝ thin x y′) m

thick-correct : ∀ {n} x y → thick-spec x y (thick {n} x y)
thick-correct              fzero    fzero   = nothingP refl
thick-correct              fzero   (fsuc y) = justP refl
thick-correct {n = suc n} (fsuc x)  fzero   = justP refl
thick-correct {n = suc n} (fsuc x) (fsuc y) =
  Part-map (ap fsuc) (ap fsuc) (thick-correct x y)

thick-nofix : ∀ {n} x → thick {n} x x ＝ nothing
thick-nofix              fzero   = refl
thick-nofix {n = suc n} (fsuc x) = ap (map fsuc) (thick-nofix x)

thick-inv : ∀ {n} x y → thick {n} x (thin x y) ＝ just y
thick-inv              fzero    y       = refl
thick-inv {n = suc n} (fsuc x)  fzero   = refl
thick-inv {n = suc n} (fsuc x) (fsuc y) = ap (map fsuc) (thick-inv x y)

-- basic properties

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

-- for properties

for-thin : ∀ {n} {t : Ty n} {x y} → (x ≔ t) (thin x y) ＝ `` y
for-thin {t} {x} {y} = ap (Maybe.rec t ``_) (thick-inv x y)

for-same : ∀ {n} {t : Ty n} {x} → (x ≔ t) x ＝ t
for-same {t} {x} = ap (Maybe.rec t ``_) (thick-nofix x)

-- substitution properties

⇝P : ℕ → 𝒰₁
⇝P m = ∀ {n} → m ⇝ n → 𝒰

⇝P∅ : ∀ {m} → ⇝P m → 𝒰
⇝P∅ {m} p = ∀ {n} (f : m ⇝ n) → ¬ p f

⇝P≃ : ∀ {m} → ⇝P m → ⇝P m → 𝒰
⇝P≃ {m} p q = ∀ {n} (f : m ⇝ n) → p f ≃ q f

⇝P∅≃ : ∀ {m} {p q : ⇝P m} → ⇝P≃ p q → ⇝P∅ p ≃ ⇝P∅ q
⇝P∅≃ {p} {q} eq =
  prop-extₑ! (λ np f qf → np f (eq f ⁻¹ $ qf)) (λ nq f pf → nq f (eq f $ pf))

⇝P× : ∀ {m} → ⇝P m → ⇝P m → ⇝P m
⇝P× p q f = p f × q f

⇝P◇ : ∀ {m n} → ⇝P m → m ⇝ n → ⇝P n
⇝P◇ {m} {n} p f {n = k} g = p (g ◇ f)

⇝P◇≃ : ∀ {m n} {p q : ⇝P m} {f : m ⇝ n} → ⇝P≃ p q → ⇝P≃ (⇝P◇ p f) (⇝P◇ q f)
⇝P◇≃ {f} eq g = eq (g ◇ f)

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

Max⇝≃ : ∀ {m} {p q : ⇝P m} → ⇝P≃ p q → ⇝P≃ (Max⇝ p) (Max⇝ q)
Max⇝≃ eq f = ×-ap (eq f) (∀-cod-≃ λ x → Π-cod-≃ λ f′ → Π-dom-≃ (eq f′ ⁻¹))

DCl : ∀ {m} → ⇝P m → 𝒰
DCl {m} p = ∀ {n k} (f : m ⇝ n) (g : m ⇝ k) → f ≤⇝ g → p g → p f

failure-propagation-lemma1 : ∀ {m n} {p q : ⇝P m} {a : m ⇝ n}
                           → ⇝P∅ (⇝P◇ p a) → ⇝P∅ (⇝P◇ (⇝P× p q) a)
failure-propagation-lemma1 np g pq = np g (pq .fst)

failure-propagation-lemma2 : ∀ {m n k} {p q : ⇝P m} {a : m ⇝ n} {f : n ⇝ k}
                           → Max⇝ (⇝P◇ p a) f → ⇝P∅ (⇝P◇ q (f ◇ a))
                           → ⇝P∅ (⇝P◇ (⇝P× p q) a)
failure-propagation-lemma2 {q} {a} {f} (paf , pmax) np g pq =
  let (s , e) = pmax g (pq .fst) in
  np s $ subst q (◇-assoc {h = a}) $ subst (λ qq → q (qq ◇ a)) (e ⁻¹) (pq .snd)

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
