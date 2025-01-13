{-# OPTIONS --safe #-}
module LFSet where

open import Prelude
open import Meta.Effect

open import Data.Empty hiding (_≠_ ; elim ; rec)
open import Data.Dec as Dec hiding (elim ; rec)
open import Data.Reflects as Reflects
open import Data.Bool as Bool hiding (elim ; rec)
open import Data.Sum
open import Data.Nat hiding (elim ; rec)
open import Data.Nat.Two

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′

-- listed finite (sub)sets
-- from https://github.com/nad/equality/blob/master/src/Finite-subset/Listed.agda

infixr 5 _∷_

data LFSet (A : 𝒰 ℓ) : 𝒰 ℓ where
  []    : LFSet A
  _∷_   : A → LFSet A → LFSet A
  drop  : ∀ {x xs} → x ∷ x ∷ xs ＝ x ∷ xs
  swap  : ∀ {x y xs} → x ∷ y ∷ xs ＝ y ∷ x ∷ xs
  trunc : is-set (LFSet A)

instance opaque
  H-Level-LFSet : ∀ {n} → ⦃ n ≥ʰ 2 ⦄ → H-Level n (LFSet A)
  H-Level-LFSet ⦃ s≤ʰs (s≤ʰs _) ⦄ = hlevel-basic-instance 2 trunc
  {-# OVERLAPPING H-Level-LFSet #-}

-- eliminators

record Elim {A : 𝒰 ℓ} (P : LFSet A → 𝒰 ℓ′) : 𝒰 (ℓ ⊔ ℓ′) where
  no-eta-equality
  field
    []ʳ     : P []
    ∷ʳ      : ∀ x {xs} → P xs → P (x ∷ xs)
    dropʳ   : ∀ x {xs} (p : P xs) →
              ＜ ∷ʳ x (∷ʳ x p) ／ (λ i → P (drop {x = x} {xs = xs} i)) ＼ ∷ʳ x p ＞
    swapʳ   : ∀ x y {xs} (p : P xs) →
              ＜ ∷ʳ x (∷ʳ y p) ／ (λ i → P (swap {x = x} {y = y} {xs = xs} i)) ＼ ∷ʳ y (∷ʳ x p) ＞
    truncʳ : ∀ x → is-set (P x)

open Elim public

elim : {P : LFSet A → 𝒰 ℓ′} → Elim P → (xs : LFSet A) → P xs
elim {A} {P} e = go
  where
  module E = Elim e
  go : (xs : LFSet A) → P xs
  go [] = E.[]ʳ
  go (x ∷ xs) = E.∷ʳ x (go xs)
  go (drop {x} {xs} i) = E.dropʳ x (go xs) i
  go (swap {x} {y} {xs} i) = E.swapʳ x y (go xs) i
  go (trunc x x′ e₁ e₂ i j) =
    hetero-UIP E.truncʳ (trunc x x′ e₁ e₂) (λ k → go (e₁ k)) (λ k → go (e₂ k)) i j

record Rec (A : 𝒰 ℓ) (B : 𝒰 ℓ′) : 𝒰 (ℓ ⊔ ℓ′) where
  no-eta-equality
  field
    []ʳ    : B
    ∷ʳ     : A → LFSet A → B → B
    dropʳ  : ∀ x y p →
              ∷ʳ x (x ∷ y) (∷ʳ x y p) ＝ ∷ʳ x y p
    swapʳ  : ∀ x y z p →
              ∷ʳ x (y ∷ z) (∷ʳ y z p) ＝ ∷ʳ y (x ∷ z) (∷ʳ x z p)
    truncʳ : is-set B

open Rec public

rec : Rec A B → LFSet A → B
rec {B} r = elim go
  where
  module R = Rec r

  go : Elim (λ _ → B)
  go .[]ʳ = R.[]ʳ
  go .∷ʳ x {xs} = R.∷ʳ x xs
  go .dropʳ x {xs} = R.dropʳ x xs
  go .swapʳ x y {xs} = R.swapʳ x y xs
  go .truncʳ _ = R.truncʳ

record Elim-prop {A : 𝒰 ℓ} (P : LFSet A → 𝒰 ℓ′) : 𝒰 (ℓ ⊔ ℓ′) where
  no-eta-equality
  field
    []ʳ    : P []
    ∷ʳ     : ∀ x {xs} → P xs → P (x ∷ xs)
    truncʳ : ∀ x → is-prop (P x)

open Elim-prop public

elim-prop : {P : LFSet A → 𝒰 ℓ′} → Elim-prop P → (x : LFSet A) → P x
elim-prop {P} e = elim e′
  where
  module E = Elim-prop e

  e′ : Elim P
  e′ .[]ʳ = E.[]ʳ
  e′ .∷ʳ = E.∷ʳ
  e′ .dropʳ x p = to-pathᴾ (E.truncʳ (drop i1) _ (∷ʳ e′ x p))
  e′ .swapʳ x y p = to-pathᴾ (E.truncʳ (swap i1) _ (∷ʳ e′ y (∷ʳ e′ x p)))
  e′ .truncʳ x = is-of-hlevel-suc 1 $ E.truncʳ x

-- empty?

empty? : LFSet A → Bool
empty? = rec go
  where
  go : Rec A Bool
  go .[]ʳ = true
  go .∷ʳ _ _ _ = false
  go .dropʳ x y p = refl
  go .swapʳ x y z p = refl
  go .truncʳ = hlevel!

-- singleton

sng : A → LFSet A
sng x = x ∷ []

-- union

infixr 5 _∪∷_

_∪∷_ : LFSet A → LFSet A → LFSet A
[]                    ∪∷ ys = ys
(x ∷ xs)              ∪∷ ys = x ∷ (xs ∪∷ ys)
drop {x} {xs} i       ∪∷ ys =
  drop {x = x} {xs = xs ∪∷ ys} i
swap {x} {y} {xs} i   ∪∷ ys =
  swap {x = x} {y = y} {xs = xs ∪∷ ys } i
trunc xs zs e₁ e₂ i j ∪∷ ys =
  trunc (xs ∪∷ ys) (zs ∪∷ ys) (λ k → e₁ k ∪∷ ys) (λ k → e₂ k ∪∷ ys) i j

∪∷-id-r : (x : LFSet A) → x ∪∷ [] ＝ x
∪∷-id-r = elim-prop go
  where
  go : Elim-prop λ q → q ∪∷ [] ＝ q
  go .[]ʳ = refl
  go .∷ʳ x e = ap (x ∷_) e
  go .truncʳ x = hlevel!

∪∷-assoc : ∀ {y z} (x : LFSet A) → x ∪∷ (y ∪∷ z) ＝ (x ∪∷ y) ∪∷ z
∪∷-assoc {y} {z} = elim-prop go
  where
  go : Elim-prop λ q → q ∪∷ y ∪∷ z ＝ (q ∪∷ y) ∪∷ z
  go .[]ʳ = refl
  go .∷ʳ x e = ap (x ∷_) e
  go .truncʳ x = hlevel!

∪∷-swap : {z : A} {s r : LFSet A}
         → z ∷ s ∪∷ r ＝ s ∪∷ z ∷ r
∪∷-swap {z} {s} {r} = elim-prop go s
  where
  go : Elim-prop λ q → z ∷ q ∪∷ r ＝ q ∪∷ z ∷ r
  go .[]ʳ = refl
  go .∷ʳ x {xs} ih = swap ∙ ap (x ∷_) ih
  go .truncʳ = hlevel!

∪∷-comm : {x y : LFSet A} → x ∪∷ y ＝ y ∪∷ x
∪∷-comm {x} {y} = elim-prop go x
  where
  go : Elim-prop λ q → q ∪∷ y ＝ y ∪∷ q
  go .[]ʳ = ∪∷-id-r y ⁻¹
  go .∷ʳ x {xs} ih = ap (x ∷_) ih ∙ ∪∷-swap {s = y} {r = xs}
  go .truncʳ = hlevel!

∪∷-idem : {x : LFSet A} → x ∪∷ x ＝ x
∪∷-idem {x} = elim-prop go x
  where
  go : Elim-prop λ q → q ∪∷ q ＝ q
  go .[]ʳ = refl
  go .∷ʳ x {xs} ih = ap (x ∷_) (∪∷-swap {s = xs} ⁻¹) ∙ drop ∙ ap (x ∷_) ih
  go .truncʳ = hlevel!

-- filter

opaque
  filterₛ : (A → Bool) → LFSet A → LFSet A
  filterₛ {A} p = rec go
    where
    go : Rec A (LFSet A)
    go .[]ʳ = []
    go .∷ʳ x _ r = if p x then x ∷ r else r
    go .dropʳ x xs r with p x --TODO use elim?
    ... | false = refl
    ... | true = drop
    go .swapʳ x y xs r with p x
    ... | false = refl
    ... | true with p y
    ... | false = refl
    ... | true = swap
    go .truncʳ = trunc

  filter-idem : ∀ {s} {p : A → Bool}
              → filterₛ p (filterₛ p s) ＝ filterₛ p s
  filter-idem {s} {p} = elim-prop go s
    where
    go : Elim-prop λ q → filterₛ p (filterₛ p q) ＝ filterₛ p q
    go .[]ʳ = refl
    go .∷ʳ x {xs} ih with p x | recall p x
    ... | false | _ = ih
    ... | true | ⟪ eq ⟫ =
       subst (λ q → (if q then x ∷ filterₛ p (filterₛ p xs) else filterₛ p (filterₛ p xs)) ＝ x ∷ filterₛ p xs)
             (eq ⁻¹)
             (ap (x ∷_) ih)
    go .truncʳ x = hlevel!

  filter-comm : ∀ {s} {p q : A → Bool}
              → filterₛ p (filterₛ q s) ＝ filterₛ q (filterₛ p s)
  filter-comm {s} {p} {q} = elim-prop go s
    where
    go : Elim-prop λ z → filterₛ p (filterₛ q z) ＝ filterₛ q (filterₛ p z)
    go .[]ʳ = refl
    go .∷ʳ x {xs} ih with q x | recall q x
    go .∷ʳ x {xs} ih | false | eq with p x
    go .∷ʳ x {xs} ih | false | _ | false = ih
    go .∷ʳ x {xs} ih | false | ⟪ eq ⟫ | true =
       subst (λ z → filterₛ p (filterₛ q xs) ＝ (if z then x ∷ filterₛ q (filterₛ p xs) else filterₛ q (filterₛ p xs)))
             (eq ⁻¹)
             ih
    go .∷ʳ x {xs} ih | true | eq with p x
    go .∷ʳ x {xs} ih | true | _ | false = ih
    go .∷ʳ x {xs} ih | true | ⟪ eq ⟫ | true =
       subst (λ z → x ∷ filterₛ p (filterₛ q xs) ＝ (if z then x ∷ filterₛ q (filterₛ p xs) else filterₛ q (filterₛ p xs)))
             (eq ⁻¹)
             (ap (x ∷_) ih)
    go .truncʳ x = hlevel!

  filter-and : ∀ {s} {p q : A → Bool}
             → filterₛ (λ z → p z and q z) s ＝ filterₛ p (filterₛ q s)
  filter-and {s} {p} {q} = elim-prop go s
    where
    go : Elim-prop λ z → filterₛ (λ w → p w and q w) z ＝ filterₛ p (filterₛ q z)
    go .[]ʳ = refl
    go .∷ʳ x {xs} ih with q x
    ... | false = if-false (subst (So ∘ not) (and-absorb-r (p x) ⁻¹) oh) ∙ ih
    ... | true = ap² (λ a b → if a then x ∷ b else b) (and-id-r (p x)) ih
    go .truncʳ = hlevel!

opaque
  unfolding filterₛ
  rem : ⦃ is-discrete A ⦄ → A → LFSet A → LFSet A
  rem x = filterₛ (not ∘ x =?_)

