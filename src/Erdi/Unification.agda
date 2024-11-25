{-# OPTIONS --safe --no-exact-split #-}
module Erdi.Unification where

open import Prelude
open import Meta.Effect

open import Data.Reflects
open import Data.Fin.Inductive
open import Data.Maybe as Maybe
open import Data.Maybe.Correspondences.Unary.Partial
open import Data.Star

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

-- _⇝=_ : ∀ {m n} → m ⇝ n → m ⇝ n → 𝒰
-- _⇝=_ {m} p q = ∀ (f : Fin m) → p f ＝ q f

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

thick-inv : ∀ {n} x y → thick {n} x (thin x y) ＝ just y
thick-inv              fzero    y       = refl
thick-inv {n = suc n} (fsuc x)  fzero   = refl
thick-inv {n = suc n} (fsuc x) (fsuc y) = ap (map fsuc) (thick-inv x y)


check : ∀ {n} → Var (suc n) → Ty (suc n) → Maybe (Ty n)
check x (`` y)    = ``_ <$> thick x y
check x (p ⟶ q) = _⟶_ <$> check x p <*> check x q
check x  con      = just con

infix 5 _≔_
_≔_ : {n : ℕ} → Ty n → Var (suc n) → (suc n ⇝ n)
(t ≔ x) y = Maybe.rec t ``_ (thick x y)

for-thin : ∀ {n} {t : Ty n} {x y} → (t ≔ x) (thin x y) ＝ `` y
for-thin {t} {x} {y} = ap (Maybe.rec t ``_) (thick-inv x y)

-- for-unify : ∀ {n} x (t : Term (suc n)) {t′ : Term n} → check x t ≡ just t′
--           → substitute (t′ for x) t ≡ (t′ for x) x

-- AList

data _//_ : ℕ → ℕ → 𝒰 where
  _/_ : ∀ {m} → Ty m → Var (suc m) → suc m // m

_⇝⋆_ : ℕ → ℕ → 𝒰
m ⇝⋆ n = Star _//_ m n

sub : ∀ {m n} → m ⇝⋆ n → m ⇝ n
sub = star-foldr {S = _⇝_} ⇝id
        (λ where (t′ / v) yz → yz ◇ (t′ ≔ v))

_⇝⋆□ : ℕ → 𝒰
m ⇝⋆□ = Σ[ n ꞉ ℕ ] (m ⇝⋆ n)

_/_◅?_ : ∀ {m} (t′ : Ty m) (x : Var (suc m)) → m ⇝⋆□ → suc m ⇝⋆□
t′ / x ◅? (n , σ) = n , (t′ / x) ◅ σ

-- unification

flex-flex : ∀ {m} → Var m → Var m → m ⇝⋆□
flex-flex {m = suc m} x y =
  Maybe.rec
    (suc m , ε refl)
    (λ y′ → m , star-sng ((`` y′) / x))
    (thick x y)

flex-rigid : ∀ {m} → Var m → Ty m → Maybe (m ⇝⋆□)
flex-rigid {m = suc m} x t =
  map (λ t′ → m , star-sng (t′ / x)) (check x t)

amgu : ∀ {m} → Ty m → Ty m → m ⇝⋆□ → Maybe (m ⇝⋆□)
amgu  con         con        acc                            = just acc
amgu  con        (pt ⟶ qt)  acc                            = nothing
amgu (ps ⟶ qs)  con         acc                            = nothing
amgu (ps ⟶ qs) (pt ⟶ qt)  acc                            = amgu ps pt acc >>= amgu qs qt
amgu (`` xs)     (`` xt)    (n , ε e)                       = just (flex-flex xs xt)
amgu (`` xs)      t         (n , ε e)                       = flex-rigid xs t
amgu  s          (`` xt)    (n , ε e)                       = flex-rigid xt s
amgu  s           t         (n , _◅_ {x = suc y} (r / z) σ) = -- omitting the match on x triggers a termination error
  map (r / z ◅?_) $
  amgu (substitute (r ≔ z) s) (substitute (r ≔ z) t) (n , σ)

mgu : ∀ {m} → Ty m → Ty m → Maybe (m ⇝⋆□)
mgu {m} s t = amgu s t (m , ε refl)
