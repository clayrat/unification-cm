{-# OPTIONS --safe #-}
module LFSet where

open import Prelude
open import Meta.Effect

open import Data.Empty hiding (_≠_ ; elim ; rec)
open import Data.Dec as Dec hiding (elim ; rec)
open import Data.Reflects as Reflects
open import Data.Bool as Bool hiding (elim ; rec)
open import Data.Sum hiding (elim)
open import Data.Nat hiding (elim ; rec)
open import Data.Nat.Order.Base
open import Data.Nat.Two
open import Data.List as List hiding (elim ; rec ; empty? ; drop)
open import Data.Maybe as Maybe hiding (elim ; rec)
open import Data.Vec.Inductive as Vec hiding (elim ; rec)
                                      renaming (_∷_ to _∷ᵥ_ ; replicate to replicateᵥ)

open import Order.Base
open import Order.Diagram.Bottom
open import Order.Diagram.Top
open import Order.Diagram.Join
open import Order.Diagram.Meet
open import Order.Semilattice.Join
open import Order.Semilattice.Meet

private variable
  ℓ ℓ′ ℓ″ : Level
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
    is-set→squareᴾ
      (λ i₁ j₁ → E.truncʳ (trunc x x′ e₁ e₂ i₁ j₁))
      refl
      (λ k → go (e₁ k))
      (λ k → go (e₂ k))
      refl
      i j

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

record Elim-prop2 {A : 𝒰 ℓ} {B : 𝒰 ℓ′} (P : LFSet A → LFSet B → 𝒰 ℓ″) : 𝒰 (ℓ ⊔ ℓ′ ⊔ ℓ″) where
  no-eta-equality
  field
    [][]ʳ    : P [] []
    []∷ʳ     : ∀ y {ys} → P [] ys → P [] (y ∷ ys)
    ∷[]ʳ     : ∀ x {xs} → P xs [] → P (x ∷ xs) []
    ∷∷ʳ      : ∀ x y {xs} {ys} → P (x ∷ xs) ys → (∀ ys → P xs ys) → P (x ∷ xs) (y ∷ ys) -- is this correct
    truncʳ   : ∀ x y → is-prop (P x y)

open Elim-prop2 public

elim-prop2 : {P : LFSet A → LFSet B → 𝒰 ℓ″} → Elim-prop2 P
           → (xs : LFSet A) → (ys : LFSet B) → P xs ys
elim-prop2 {A} {B} {P} e xs ys = elim {P = λ xs → ∀ ys → P xs ys} e′ xs ys
  where
  module E = Elim-prop2 e

  e′ : Elim λ xs → ∀ ys → P xs ys
  e′ .[]ʳ = elim e″
    where
    e″ : Elim (P [])
    e″ .[]ʳ = E.[][]ʳ
    e″ .∷ʳ y {xs = ys} pys = E.[]∷ʳ y pys
    e″ .dropʳ y p = to-pathᴾ (E.truncʳ [] (drop i1) _ (∷ʳ e″ y p))
    e″ .swapʳ x y p = to-pathᴾ (E.truncʳ [] (swap i1) _ (∷ʳ e″ y (∷ʳ e″ x p)))
    e″ .truncʳ ys = is-of-hlevel-suc 1 $ E.truncʳ [] ys
  e′ .∷ʳ x {xs} p ys = elim e″ ys
    where
    e″ : Elim (P (x ∷ xs))
    e″ .[]ʳ = E.∷[]ʳ x (p [])
    e″ .∷ʳ y {xs = ys} pys = E.∷∷ʳ x y pys p -- ?
    e″ .dropʳ y p = to-pathᴾ (E.truncʳ (x ∷ xs) (drop i1) _ (∷ʳ e″ y p))
    e″ .swapʳ y z p = to-pathᴾ (E.truncʳ (x ∷ xs) (swap i1) _ (∷ʳ e″ z (∷ʳ e″ y p)))
    e″ .truncʳ ys = is-of-hlevel-suc 1 $ E.truncʳ (x ∷ xs) ys
  e′ .dropʳ x p = to-pathᴾ (fun-ext λ ys → E.truncʳ (drop i1) ys _ (∷ʳ e′ x p ys))
  e′ .swapʳ x y p = to-pathᴾ (fun-ext λ ys → E.truncʳ (swap i1) ys _ (∷ʳ e′ y (∷ʳ e′ x p) ys))
  e′ .truncʳ xs = Π-is-of-hlevel 2 λ ys → is-of-hlevel-suc 1 $ E.truncʳ xs ys

-- empty?

-- TODO should this be opaque?
empty? : LFSet A → Bool
empty? = rec go
  where
  go : Rec A Bool
  go .[]ʳ = true
  go .∷ʳ _ _ _ = false
  go .dropʳ x y p = refl
  go .swapʳ x y z p = refl
  go .truncʳ = hlevel!

∷≠[] : {x : A} {xs : LFSet A}
     → x ∷ xs ≠ []
∷≠[] = false! ∘ ap empty?

Reflects-empty? : {s : LFSet A} → Reflects (s ＝ []) (empty? s)
Reflects-empty? {A} {s} = elim-prop go s
  where
  go : Elim-prop {A = A} λ q → Reflects (q ＝ []) (empty? q)
  go .[]ʳ = ofʸ refl
  go .∷ʳ _ _ = ofⁿ ∷≠[]
  go .truncʳ xs = hlevel!

-- singleton

sng : A → LFSet A
sng x = x ∷ []

-- union

infixr 5 _∪∷_

-- TODO use rec
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

∪∷-assoc : ∀ {y z} (x : LFSet A) → x ∪∷ y ∪∷ z ＝ (x ∪∷ y) ∪∷ z
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

∪∷-assoc-comm : ∀ (x : LFSet A) {y z} → (x ∪∷ y) ∪∷ z ＝ (x ∪∷ z) ∪∷ y
∪∷-assoc-comm x {y} {z} =
    ∪∷-assoc {y = y} x ⁻¹
  ∙ ap (x ∪∷_) (∪∷-comm {x = y})
  ∙ ∪∷-assoc {y = z} x

∪∷-comm-assoc : ∀ (x : LFSet A) {y z} → x ∪∷ y ∪∷ z ＝ y ∪∷ x ∪∷ z
∪∷-comm-assoc x {y} {z} =
    ∪∷-assoc {y = y} x
  ∙ ap (_∪∷ z) (∪∷-comm {x = x})
  ∙ ∪∷-assoc {y = x} y ⁻¹

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

  filter-[] : {p : A → Bool} → filterₛ p [] ＝ []
  filter-[] = refl

  filter-∷ : {p : A → Bool} {x : A} {xs : LFSet A}
           → filterₛ p (x ∷ xs) ＝ (if p x then x ∷ filterₛ p xs else filterₛ p xs)
  filter-∷ = refl

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

  filter-or : ∀ {s} {p q : A → Bool}
             → filterₛ (λ z → p z or q z) s ＝ filterₛ p s ∪∷ filterₛ (λ z → not (p z) and q z) s
  filter-or {s} {p} {q} = elim-prop go s
    where
    go : Elim-prop λ z → filterₛ (λ w → p w or q w) z ＝ filterₛ p z ∪∷ filterₛ (λ w → not (p w) and q w) z
    go .[]ʳ = refl
    go .∷ʳ x {xs} ih with p x
    go .∷ʳ x {xs} ih | false with q x
    go .∷ʳ x {xs} ih | false | false = ih
    go .∷ʳ x {xs} ih | false | true = ap (x ∷_) ih ∙ ∪∷-swap {s = filterₛ p xs}
    go .∷ʳ x {xs} ih | true = ap (x ∷_) ih
    go .truncʳ = hlevel!

  filter-∪∷ : ∀ {xs ys} {p : A → Bool}
             → filterₛ p (xs ∪∷ ys) ＝ filterₛ p xs ∪∷ filterₛ p ys
  filter-∪∷ {xs} {ys} {p} = elim-prop go xs
    where
    go : Elim-prop λ q → filterₛ p (q ∪∷ ys) ＝ filterₛ p q ∪∷ filterₛ p ys
    go .[]ʳ = refl
    go .∷ʳ x {xs} ih with p x
    go .∷ʳ x {xs} ih | false = ih
    go .∷ʳ x {xs} ih | true  = ap (x ∷_) ih
    go .truncʳ = hlevel!

  filter-compl : ∀ {s} {p : A → Bool}
                 → filterₛ p s ∪∷ filterₛ (not ∘ p) s ＝ s
  filter-compl {s} {p} = elim-prop go s
    where
    go : Elim-prop λ q → filterₛ p q ∪∷ filterₛ (not ∘ p) q ＝ q
    go .[]ʳ = refl
    go .∷ʳ x {xs} ih with p x
    go .∷ʳ x {xs} ih | false = ∪∷-swap {z = x} {s = filterₛ p xs} ⁻¹ ∙ ap (x ∷_) ih
    go .∷ʳ x {xs} ih | true  = ap (x ∷_) ih
    go .truncʳ _ = hlevel!

opaque
  allₛ : (A → Bool) → LFSet A → Bool
  allₛ {A} p = rec go
    where
      go : Rec A Bool
      go .[]ʳ = true
      go .∷ʳ x _ b = p x and b
      go .dropʳ x xs b = and-assoc (p x) (p x) b ⁻¹ ∙ ap (_and b) (and-idem (p x))
      go .swapʳ x y xs b = and-assoc (p x) (p y) b ⁻¹ ∙ ap (_and b) (and-comm (p x) (p y)) ∙ and-assoc (p y) (p x) b
      go .truncʳ = hlevel!

  allₛ-[] : {p : A → Bool} → allₛ p [] ＝ true
  allₛ-[] = refl

  allₛ-∷ : {p : A → Bool} {x : A} {xs : LFSet A}
         → allₛ p (x ∷ xs) ＝ p x and allₛ p xs
  allₛ-∷ = refl

  allₛ-sng : {p : A → Bool} {x : A}
           → allₛ p (sng x) ＝ p x
  allₛ-sng = and-id-r _

  allₛ-∪∷ : {p : A → Bool} {xs ys : LFSet A}
          → allₛ p (xs ∪∷ ys) ＝ allₛ p xs and allₛ p ys
  allₛ-∪∷ {p} {xs} {ys} = elim-prop go xs
     where
     go : Elim-prop λ q → allₛ p (q ∪∷ ys) ＝ allₛ p q and allₛ p ys
     go .[]ʳ = refl
     go .∷ʳ x {xs} ih = ap (p x and_) ih ∙ and-assoc (p x) _ _ ⁻¹
     go .truncʳ = hlevel!

opaque
  anyₛ : (A → Bool) → LFSet A → Bool
  anyₛ {A} p = rec go
    where
      go : Rec A Bool
      go .[]ʳ = false
      go .∷ʳ x _ b = p x or b
      go .dropʳ x xs b = or-assoc (p x) (p x) b ⁻¹ ∙ ap (_or b) (or-idem (p x))
      go .swapʳ x y xs b = or-assoc (p x) (p y) b ⁻¹ ∙ ap (_or b) (or-comm (p x) (p y)) ∙ or-assoc (p y) (p x) b
      go .truncʳ = hlevel!

  anyₛ-[] : {p : A → Bool} → anyₛ p [] ＝ false
  anyₛ-[] = refl

  anyₛ-∷ : {p : A → Bool} {x : A} {xs : LFSet A}
         → anyₛ p (x ∷ xs) ＝ p x or anyₛ p xs
  anyₛ-∷ = refl

  anyₛ-sng : {p : A → Bool} {x : A}
           → anyₛ p (sng x) ＝ p x
  anyₛ-sng = or-id-r _

  anyₛ-∪∷ : {p : A → Bool} {xs ys : LFSet A}
          → anyₛ p (xs ∪∷ ys) ＝ anyₛ p xs or anyₛ p ys
  anyₛ-∪∷ {p} {xs} {ys} = elim-prop go xs
     where
     go : Elim-prop λ q → anyₛ p (q ∪∷ ys) ＝ anyₛ p q or anyₛ p ys
     go .[]ʳ = refl
     go .∷ʳ x {xs} ih = ap (p x or_) ih ∙ or-assoc (p x) _ _ ⁻¹
     go .truncʳ = hlevel!

opaque
  mapₛ : (A → B) → LFSet A → LFSet B
  mapₛ {A} {B} f = rec go
    where
      go : Rec A (LFSet B)
      go .[]ʳ = []
      go .∷ʳ x _ ys = f x ∷ ys
      go .dropʳ x xs ys = drop
      go .swapʳ x y xs ys = swap
      go .truncʳ = hlevel!

  mapₛ-[] : {f : A → B} → mapₛ f [] ＝ []
  mapₛ-[] = refl

  mapₛ-∷ : {f : A → B} {x : A} {xs : LFSet A}
         → mapₛ f (x ∷ xs) ＝ f x ∷ mapₛ f xs
  mapₛ-∷ = refl

  mapₛ-sng : {f : A → B} {x : A}
           → mapₛ f (sng x) ＝ sng (f x)
  mapₛ-sng = refl

  mapₛ-∪∷ : {f : A → B} {xs ys : LFSet A}
          → mapₛ f (xs ∪∷ ys) ＝ mapₛ f xs ∪∷ mapₛ f ys
  mapₛ-∪∷ {f} {xs} {ys} = elim-prop go xs
     where
       go : Elim-prop λ q → mapₛ f (q ∪∷ ys) ＝ mapₛ f q ∪∷ mapₛ f ys
       go .[]ʳ = refl
       go .∷ʳ x {xs} ih = ap (f x ∷_) ih
       go .truncʳ = hlevel!

opaque
  apₛ : LFSet (A → B) → LFSet A → LFSet B
  apₛ {A} {B} = rec go
    where
      go : Rec (A → B) (LFSet A → LFSet B)
      go .[]ʳ _ = []
      go .∷ʳ f fs r as = mapₛ f as ∪∷ r as
      go .dropʳ f fs r = fun-ext λ as → ∪∷-assoc {y = mapₛ f as} (mapₛ f as) ∙ ap (_∪∷ r as) (∪∷-idem {x = mapₛ f as})
      go .swapʳ f g fs r = fun-ext λ as → ∪∷-assoc {y = mapₛ g as} (mapₛ f as) ∙ ap (_∪∷ r as) (∪∷-comm {x = mapₛ f as}) ∙ ∪∷-assoc {y = mapₛ f as} (mapₛ g as) ⁻¹
      go .truncʳ = hlevel!

  apₛ-[]-l : {s : LFSet A} → apₛ {B = B} [] s ＝ []
  apₛ-[]-l = refl

-- TODO
-- apₛ-[]-r : {f : LFSet (A → B)} → apₛ f [] ＝ []

opaque
  bindₛ : (A → LFSet B) → LFSet A → LFSet B
  bindₛ {A} {B} f = rec go
    where
      go : Rec A (LFSet B)
      go .[]ʳ = []
      go .∷ʳ x _ ys = f x ∪∷ ys
      go .dropʳ x xs ys = ∪∷-assoc (f x) ∙ ap (_∪∷ ys) (∪∷-idem {x = f x})
      go .swapʳ x y xs ys = ∪∷-assoc {y = f y} (f x) ∙ ap (_∪∷ ys) (∪∷-comm {x = f x}) ∙ ∪∷-assoc (f y) ⁻¹
      go .truncʳ = hlevel!

  bindₛ-[] : {f : A → LFSet B} → bindₛ f [] ＝ []
  bindₛ-[] = refl

  bindₛ-∷ : {f : A → LFSet B} {x : A} {xs : LFSet A}
         → bindₛ f (x ∷ xs) ＝ f x ∪∷ bindₛ f xs
  bindₛ-∷ = refl

  bindₛ-sng : {f : A → LFSet B} {x : A}
           → bindₛ f (sng x) ＝ f x
  bindₛ-sng {f} {x} = ∪∷-id-r (f x)

  bindₛ-∪∷ : {f : A → LFSet B} {xs ys : LFSet A}
          → bindₛ f (xs ∪∷ ys) ＝ bindₛ f xs ∪∷ bindₛ f ys
  bindₛ-∪∷ {f} {xs} {ys} = elim-prop go xs
    where
      go : Elim-prop λ q → bindₛ f (q ∪∷ ys) ＝ bindₛ f q ∪∷ bindₛ f ys
      go .[]ʳ = refl
      go .∷ʳ x {xs} ih = ap (f x ∪∷_) ih ∙ ∪∷-assoc (f x)
      go .truncʳ = hlevel!

opaque
  joinₛ : {o ℓ : Level} {A : Poset o ℓ} {js : is-join-semilattice A}
        → LFSet (Poset.Ob A) → Poset.Ob A
  joinₛ {A} {js} = rec go
    where
      open is-join-semilattice js
      go : Rec (Poset.Ob A) (Poset.Ob A)
      go .[]ʳ = ⊥
      go .∷ʳ x xs r = x ∪ r
      go .dropʳ x y r = ∪-assoc ∙ ap (_∪ r) ∪-idem
      go .swapʳ x y xs r = ∪-assoc ∙ ap (_∪ r) ∪-comm ∙ ∪-assoc ⁻¹
      go .truncʳ = Poset.ob-is-set A

  joinₛ-[] : {o ℓ : Level} {A : Poset o ℓ} {js : is-join-semilattice A}
            (open is-join-semilattice js)   -- wut
          → joinₛ {js = js} [] ＝ ⊥
  joinₛ-[] = refl

  joinₛ-∷ : {o ℓ : Level} {A : Poset o ℓ} {js : is-join-semilattice A}
            (open is-join-semilattice js)   -- wut
            {x : Poset.Ob A} {xs : LFSet (Poset.Ob A)}
          → joinₛ {js = js} (x ∷ xs) ＝ x ∪ joinₛ {js = js} xs
  joinₛ-∷ = refl

  joinₛ-sng : {o ℓ : Level} {A : Poset o ℓ} {js : is-join-semilattice A}
              (open is-join-semilattice js)   -- wut
              {x : Poset.Ob A}
            → joinₛ {js = js} (sng x) ＝ x
  joinₛ-sng {js} = ∪-id-r ⦃ b = has-bottom ⦄
    where
      open is-join-semilattice js

  joinₛ-∪∷ : {o ℓ : Level} {A : Poset o ℓ} {js : is-join-semilattice A}
             (open is-join-semilattice js)   -- wut
             {xs ys : LFSet (Poset.Ob A)}
           → joinₛ {js = js} (xs ∪∷ ys) ＝ joinₛ {js = js} xs ∪ joinₛ {js = js} ys
  joinₛ-∪∷ {js} {xs} {ys} = elim-prop go xs
    where
      open is-join-semilattice js
      go : Elim-prop λ q → joinₛ {js = js} (q ∪∷ ys) ＝ joinₛ {js = js} q ∪ joinₛ {js = js} ys
      go .[]ʳ = ∪-id-l ⦃ b = has-bottom ⦄ ⁻¹
      go .∷ʳ x {xs} ih = ap (x ∪_) ih ∙ ∪-assoc
      go .truncʳ = hlevel!

opaque
  meetₛ : {o ℓ : Level} {A : Poset o ℓ} {ms : is-meet-semilattice A}
        → LFSet (Poset.Ob A) → Poset.Ob A
  meetₛ {A} {ms} = rec go
    where
      open is-meet-semilattice ms
      go : Rec (Poset.Ob A) (Poset.Ob A)
      go .[]ʳ = ⊤
      go .∷ʳ x xs r = x ∩ r
      go .dropʳ x y r = ∩-assoc ∙ ap (_∩ r) ∩-idem
      go .swapʳ x y xs r = ∩-assoc ∙ ap (_∩ r) ∩-comm ∙ ∩-assoc ⁻¹
      go .truncʳ = Poset.ob-is-set A

  meetₛ-[] : {o ℓ : Level} {A : Poset o ℓ} {ms : is-meet-semilattice A}
            (open is-meet-semilattice ms)   -- wut
          → meetₛ {ms = ms} [] ＝ ⊤
  meetₛ-[] = refl

  meetₛ-∷ : {o ℓ : Level} {A : Poset o ℓ} {ms : is-meet-semilattice A}
            (open is-meet-semilattice ms)   -- wut
            {x : Poset.Ob A} {xs : LFSet (Poset.Ob A)}
          → meetₛ {ms = ms} (x ∷ xs) ＝ x ∩ meetₛ {ms = ms} xs
  meetₛ-∷ = refl

  meetₛ-sng : {o ℓ : Level} {A : Poset o ℓ} {ms : is-meet-semilattice A}
              (open is-meet-semilattice ms)   -- wut
              {x : Poset.Ob A}
            → meetₛ {ms = ms} (sng x) ＝ x
  meetₛ-sng {ms} = ∩-id-r ⦃ t = has-top ⦄
    where
      open is-meet-semilattice ms

  meetₛ-∪∷ : {o ℓ : Level} {A : Poset o ℓ} {ms : is-meet-semilattice A}
             (open is-meet-semilattice ms)   -- wut
             {xs ys : LFSet (Poset.Ob A)}
           → meetₛ {ms = ms} (xs ∪∷ ys) ＝ meetₛ {ms = ms} xs ∩ meetₛ {ms = ms} ys
  meetₛ-∪∷ {ms} {xs} {ys} = elim-prop go xs
    where
      open is-meet-semilattice ms
      go : Elim-prop λ q → meetₛ {ms = ms} (q ∪∷ ys) ＝ meetₛ {ms = ms} q ∩ meetₛ {ms = ms} ys
      go .[]ʳ = ∩-id-l ⦃ t = has-top ⦄ ⁻¹
      go .∷ʳ x {xs} ih = ap (x ∩_) ih ∙ ∩-assoc
      go .truncʳ = hlevel!

-- TODO foldable?

-- maybe interaction

from-maybe : Maybe A → LFSet A
from-maybe = Maybe.rec [] sng

-- list interaction

from-list : List A → LFSet A
from-list = List.rec [] _∷_

opaque
  unfolding mapₛ
  from-list-map : {A : 𝒰 ℓ} {B : 𝒰 ℓ′} {f : A → B} {xs : List A}
                → mapₛ f (from-list xs) ＝ from-list (map f xs)
  from-list-map     {xs = []} = refl
  from-list-map {f} {xs = x ∷ xs} = ap (f x ∷_) (from-list-map {xs = xs})

∷-from-list-replicate : ∀ {n} {x : A}
                      → x ∷ from-list (replicate n x) ＝ sng x
∷-from-list-replicate {n = zero}  = refl
∷-from-list-replicate {n = suc n} = drop ∙ ∷-from-list-replicate {n = n}

from-list-replicate-0< : ∀ {n} {x : A}
                       → 0 < n
                       → from-list (replicate n x) ＝ sng x
from-list-replicate-0< {n = zero}  zl = false! zl
from-list-replicate-0< {n = suc n} _  = ∷-from-list-replicate {n = n}

-- vector interaction

from-vec : ∀ {n} → Vec A n → LFSet A
from-vec = Vec.rec [] _∷_

∷-from-vec-replicate : ∀ {n} {x : A}
                      → x ∷ from-vec (Vec.replicate n x) ＝ sng x
∷-from-vec-replicate {n = zero}  = refl
∷-from-vec-replicate {n = suc n} = drop ∙ ∷-from-vec-replicate {n = n}

from-vec-replicate-0< : ∀ {n} {x : A}
                  → 0 < n
                  → from-vec (Vec.replicate n x) ＝ sng x
from-vec-replicate-0< {n = zero}  zl = false! zl
from-vec-replicate-0< {n = suc n} _  = ∷-from-vec-replicate {n = n}

