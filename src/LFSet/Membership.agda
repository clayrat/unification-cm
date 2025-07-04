{-# OPTIONS --safe #-}
module LFSet.Membership where

open import Prelude
open import Foundations.Sigma
open import Meta.Effect

open import Data.Empty hiding (_≠_ ; elim ; rec)
open import Data.Dec as Dec hiding (elim ; rec)
open import Data.Reflects as Reflects
open import Data.Bool as Bool hiding (elim ; rec)
open import Data.Sum as Sum
open import Data.Nat hiding (elim ; rec)
open import Data.Nat.Order.Base
open import Data.Nat.Two

open import Data.Maybe hiding (rec)
open import Data.Maybe.Correspondences.Unary.Any renaming (here to hereₘ)
open import Data.List hiding ([] ; rec ; drop)
open import Data.List.Correspondences.Unary.Any
open import Data.List.Membership

open import Data.Vec.Inductive hiding ([] ; rec)

open import Order.Base
open import Order.Semilattice.Join
open import Order.Semilattice.Meet

open import LFSet

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′

-- membership

@0 ∈ₛ-LFSet : A → LFSet A → Prop (level-of-type A)
∈ₛ-LFSet {A} x = rec go
  where
  go : Rec A (Prop (level-of-type A))
  go .[]ʳ = el! ⊥
  go .∷ʳ y z x∈z = el! ((x ＝ y) ⊎₁ x∈z .n-Type.carrier)
  go .dropʳ y z p =
    n-path $ ua $
      ∥-∥₁.⊎₁-assoc ⁻¹
    ∙ ∥-∥₁.⊎₁-ap-l ∥-∥₁.⊎₁-idem
    ∙ ∥-∥₁.⊎₁-trunc-l ⁻¹
  go .swapʳ y z u p =
    n-path $ ua $
      ∥-∥₁.⊎₁-assoc ⁻¹
    ∙ ∥-∥₁.⊎₁-ap-l ∥-∥₁.⊎₁-comm
    ∙ ∥-∥₁.⊎₁-assoc
  go .truncʳ = n-Type-is-of-hlevel 1

-- Agda boilerplate

private module dummy-∈ₛ where

  infix 4 _∈ₛ_

  record _∈ₛ_
    {A : 𝒰 ℓ} (x : A) (y : LFSet A) : 𝒰 ℓ where
    constructor box
    field
      unbox : Erased ((∈ₛ-LFSet x y) .n-Type.carrier)

open dummy-∈ₛ public using (_∈ₛ_) hiding (module _∈ₛ_)

∈ₛ⇉ : {x : A} {xs : LFSet A} → x ∈ₛ xs → Erased ((∈ₛ-LFSet x xs) .n-Type.carrier)
∈ₛ⇉ = dummy-∈ₛ._∈ₛ_.unbox

⇉∈ₛ : {x : A} {xs : LFSet A} → Erased ((∈ₛ-LFSet x xs) .n-Type.carrier) → x ∈ₛ xs
⇉∈ₛ = dummy-∈ₛ.box

∈ₛ≃ : {x : A} {xs : LFSet A} → (x ∈ₛ xs) ≃ Erased ((∈ₛ-LFSet x xs) .n-Type.carrier)
∈ₛ≃ =
  ≅→≃ $ make-iso ∈ₛ⇉ ⇉∈ₛ $
  make-inverses (fun-ext λ x → refl) (fun-ext λ x → refl)

Recomputable-∈ₛ : {x : A} {xs : LFSet A} → Recomputable (x ∈ₛ xs)
Recomputable-∈ₛ .recompute e =
  ⇉∈ₛ (erase ((∈ₛ⇉ (e .erased)) .erased))

∈ₛ-prop : {x : A} {xs : LFSet A} → is-prop (x ∈ₛ xs)
∈ₛ-prop {x} {xs} =
  ≃→is-of-hlevel 1 ∈ₛ≃ $
  erased-is-of-hlevel 1 ((∈ₛ-LFSet x xs) .n-Type.carrier-is-tr)

instance
  Membership-LFSet : {A : 𝒰 ℓ} → Membership A (LFSet A) ℓ
  Membership-LFSet ._∈_ = _∈ₛ_

  H-Level-∈ₛ : ∀ {n} {x} {xs : LFSet A} → ⦃ n ≥ʰ 1 ⦄ → H-Level n (x ∈ₛ xs)
  H-Level-∈ₛ {n} {xs} ⦃ s≤ʰs _ ⦄ = hlevel-prop-instance (∈ₛ-prop {xs = xs})
  {-# OVERLAPPING H-Level-∈ₛ #-}

hereₛ : {z x : A} {xs : LFSet A} → z ＝ x → z ∈ₛ x ∷ xs
hereₛ e = ⇉∈ₛ $ erase ∣ inl e ∣₁

thereₛ : {z x : A} {xs : LFSet A} → z ∈ₛ xs → z ∈ₛ x ∷ xs
thereₛ z∈ = ⇉∈ₛ $ erase ∣ inr ((∈ₛ⇉ z∈) .erased) ∣₁

∉ₛ[] : {x : A} → x ∉ []
∉ₛ[] x with ∈ₛ⇉ x
... | ()

instance
  Refl-x∉ₛ[] : {x : A} → Reflects (x ∈ₛ []) false
  Refl-x∉ₛ[] = ofⁿ ∉ₛ[]

{-
-- TODO useless ?
unconsₛ : {z x : A} {xs : LFSet A}
         {B : 𝒰 ℓ′}
       → (is-prop B)
       → (z ＝ x → B)
       → (z ∈ₛ xs → B)
       → z ∈ₛ (x ∷ xs)
       → Erased B
unconsₛ {z} {x} {xs} {B} bp f g z∈∷ =
  erase
    (∥-∥₁.elim {A = (z ＝ x) ⊎ₜ (∈ₛ-LFSet z xs) .n-Type.carrier}
      {P = λ _ → B}
      (λ _ → bp)
      [ f , (λ z∈ → g (⇉∈ₛ (erase z∈))) ]ᵤ
      (∈ₛ⇉ z∈∷ .erased))
-}

∈ₛ∷-≠ : {z x : A} {xs : LFSet A} → z ≠ x → z ∈ₛ (x ∷ xs) → z ∈ₛ xs
∈ₛ∷-≠ z≠x z∈∷ =
  ⇉∈ₛ $ erase
    (rec! [ (λ e → absurd (z≠x e)) , id ]ᵤ ((∈ₛ⇉ z∈∷) .erased))

∈ₛ∷-∉ᴱ : {z x : A} {xs : LFSet A} → z ∈ₛ (x ∷ xs) → z ∉ xs → Erased ∥ z ＝ x ∥₁
∈ₛ∷-∉ᴱ z∈∷ z∉ =
  erase (rec! [ ∣_∣₁
              , (λ z∈ → absurd (z∉ (⇉∈ₛ (erase z∈)))) ]ᵤ ((∈ₛ⇉ z∈∷) .erased))

∉ₛ-∷ : {z x : A} {xs : LFSet A} → z ≠ x → z ∉ xs → z ∉ (x ∷ xs)
∉ₛ-∷ z≠x z∉xs z∈∷ =
  Recomputable-⊥ .recompute $ erase $
  rec! [ z≠x , contra (λ q → ⇉∈ₛ $ erase q) z∉xs ]ᵤ ((∈ₛ⇉ z∈∷) .erased)

∉ₛ-uncons : {z x : A} {xs : LFSet A} → z ∉ (x ∷ xs) → (z ≠ x) × z ∉ xs
∉ₛ-uncons z∉∷ = contra hereₛ z∉∷ , contra thereₛ z∉∷

∈ₛ-∷→ᴱ : {z x : A} {xs : LFSet A} → z ∈ₛ (x ∷ xs) → Erased ((z ＝ x) ⊎₁ (z ∈ₛ xs))
∈ₛ-∷→ᴱ z∈∷ =
  erase $
    map (map-r (λ q → ⇉∈ₛ $ erase q)) ((∈ₛ⇉ z∈∷) .erased)

∈ₛ-∷=ᴱ : {z : A} {s : LFSet A}
       → z ∈ₛ s → Erased (z ∷ s ＝ s)
∈ₛ-∷=ᴱ {z} {s} = elim-prop go s
  where
  go : Elim-prop λ q → z ∈ₛ q → Erased (z ∷ q ＝ q)
  go .[]ʳ = false! ⦃ Refl-x∉ₛ[] ⦄ -- why
  go .∷ʳ x {xs} ih z∈ =
    erase
      (rec! [ (λ e → ap (_∷ x ∷ xs) e ∙ drop)
             , (λ z∈′ → swap ∙ ap (x ∷_) (ih z∈′ .erased))
             ]ᵤ (∈ₛ-∷→ᴱ z∈ .erased))
  go .truncʳ _ = hlevel!

∈ₛ-∪∷←l : {z : A} {s₁ s₂ : LFSet A}
        → z ∈ₛ s₁
        → z ∈ₛ (s₁ ∪∷ s₂)
∈ₛ-∪∷←l {z} {s₁} {s₂} = elim-prop go s₁
  where
  go : Elim-prop λ q → z ∈ₛ q → z ∈ₛ (q ∪∷ s₂)
  go .[]ʳ = false! ⦃ Refl-x∉ₛ[] ⦄
  go .∷ʳ x ih z∈∷ =
    Recomputable-∈ₛ .recompute $ erase
      (rec! [ hereₛ  , thereₛ ∘ ih ]ᵤ (∈ₛ-∷→ᴱ z∈∷ .erased))
  go .truncʳ _ = hlevel!

∈ₛ-∪∷←r : {z : A} {s₁ s₂ : LFSet A}
        → z ∈ₛ s₂
        → z ∈ₛ (s₁ ∪∷ s₂)
∈ₛ-∪∷←r {z} {s₁} {s₂} z∈ = elim-prop go s₁
  where
  go : Elim-prop λ q → z ∈ₛ (q ∪∷ s₂)
  go .[]ʳ = z∈
  go .∷ʳ x = thereₛ
  go .truncʳ _ = hlevel!

∈ₛ-∪∷→ᴱ : {z : A} {s₁ s₂ : LFSet A}
        → z ∈ₛ (s₁ ∪∷ s₂) → Erased ((z ∈ₛ s₁) ⊎₁ (z ∈ₛ s₂))
∈ₛ-∪∷→ᴱ {z} {s₁} {s₂} = elim-prop go s₁
  where
  go : Elim-prop λ q → z ∈ₛ (q ∪∷ s₂) → Erased ((z ∈ₛ q) ⊎₁ (z ∈ₛ s₂))
  go .[]ʳ z∈s₂ = erase ∣ inr z∈s₂ ∣₁
  go .∷ʳ x {xs} ih z∈∷ =
    erase
      (rec!
         [ (λ e → ∣ inl (hereₛ e) ∣₁)
         , (λ w → map (map-l thereₛ) (ih (⇉∈ₛ (erase w)) .erased)) ]ᵤ
         (∈ₛ⇉ z∈∷ .erased))
  go .truncʳ _ = hlevel!

∈ₛ∪∷-∉ : {z : A} {xs ys : LFSet A} → z ∈ₛ (xs ∪∷ ys) → z ∉ xs → z ∈ ys
∈ₛ∪∷-∉ {z} {xs} {ys} z∈∪∷ z∉xs =
  ⇉∈ₛ $ erase
    (rec! [ (λ z∈xs → absurd (z∉xs z∈xs))
         , (λ z∈ys → (∈ₛ⇉ z∈ys) .erased) ]ᵤ
         (∈ₛ-∪∷→ᴱ z∈∪∷ .erased))

∪∷-∉ₛ : {z : A} {xs ys : LFSet A}
       → z ∉ xs → z ∉ ys → z ∉ (xs ∪∷ ys)
∪∷-∉ₛ z∉xs z∉ys z∈∪∷ =
  z∉ys (∈ₛ∪∷-∉ z∈∪∷ z∉xs)

∉ₛ-∪∷ : {z : A} {xs ys : LFSet A}
       → z ∉ (xs ∪∷ ys) → (z ∉ xs) × (z ∉ ys)
∉ₛ-∪∷ {z} {xs} {ys} = elim-prop go xs
  where
  go : Elim-prop λ q → z ∉ (q ∪∷ ys) → (z ∉ q) × (z ∉ ys)
  go .[]ʳ z∉ys = ∉ₛ[] , z∉ys
  go .∷ʳ x {xs} ih nin =
    let (ihx , ihy) = ih (nin ∘ thereₛ) in
    ∉ₛ-∷ {xs = xs} (nin ∘ hereₛ) ihx , ihy
  go .truncʳ zs = hlevel!

⊆-∷ : {z : A} {xs ys : LFSet A}
     → xs ⊆ ys → (z ∷ xs) ⊆ (z ∷ ys)
⊆-∷ {z} {ys} sub {x} x∈ =
  ⇉∈ₛ $ erase
    (rec! [ ∣_∣₁ ∘ inl
          , (λ q → ∣ inr (∈ₛ⇉ (sub (⇉∈ₛ (erase q))) .erased) ∣₁) ]ᵤ
          (∈ₛ⇉ x∈ .erased))

⊆-∪∷-l : {xs ys zs : LFSet A}
       → ys ⊆ zs → (xs ∪∷ ys) ⊆ (xs ∪∷ zs)
⊆-∪∷-l {xs} {ys} {zs} yzs = elim-prop go xs
  where
  go : Elim-prop λ q → (q ∪∷ ys) ⊆ (q ∪∷ zs)
  go .[]ʳ      = yzs
  go .∷ʳ x     = ⊆-∷
  go .truncʳ _ = hlevel!

⊆-∪∷-r : {xs ys zs : LFSet A}
       → xs ⊆ ys → (xs ∪∷ zs) ⊆ (ys ∪∷ zs)
⊆-∪∷-r {xs} {ys} {zs} xys {x} =
  subst (x ∈_) (∪∷-comm {x = zs}) ∘
  ⊆-∪∷-l {xs = zs} xys ∘
  subst (x ∈_) (∪∷-comm {x = xs})

⊆-∪=ᴱ : {xs ys : LFSet A}
       → xs ⊆ ys → Erased (xs ∪∷ ys ＝ ys)
⊆-∪=ᴱ {xs} {ys} = elim-prop go xs
  where
  go : Elim-prop λ q → q ⊆ ys → Erased (q ∪∷ ys ＝ ys)
  go .[]ʳ _ = erase refl
  go .∷ʳ x {xs} ih su =
    erase (  ∈ₛ-∷=ᴱ (∈ₛ-∪∷←r {s₁ = xs} (su (hereₛ refl))) .erased
           ∙ ih (su ∘ thereₛ) .erased)
  go .truncʳ x = hlevel!

sng-∈ᴱ : {x z : A} {xs : LFSet A} → x ∈ₛ sng z → Erased ∥ x ＝ z ∥₁
sng-∈ᴱ x∈ = ∈ₛ∷-∉ᴱ x∈ ∉ₛ[]

set-extᴱ : {xs ys : LFSet A} → ((z : A) → z ∈ xs ≃ z ∈ ys) → Erased (xs ＝ ys)
set-extᴱ {xs} {ys} e =
  erase (  ⊆-∪=ᴱ {xs = ys} (λ {x} x∈ys → e x ⁻¹ $ x∈ys) .erased ⁻¹
         ∙ ∪∷-comm {x = ys}
         ∙ ⊆-∪=ᴱ {xs = xs} (λ {x} x∈xs → e x $ x∈xs) .erased)

-- maybe

from-maybe-= : {xm : Maybe A}
               {x : A}
             → x ∈ xm → from-maybe xm ＝ sng x
from-maybe-= {xm = just x} (hereₘ px) = ap sng (px ⁻¹)

∈-maybe : {xm : Maybe A}
          {x : A} → x ∈ xm → x ∈ₛ from-maybe xm
∈-maybe {xm = just x} (hereₘ e) = hereₛ e

maybe-∈ᴱ : {xm : Maybe A}
           {x : A} → x ∈ₛ from-maybe xm → Erased ∥ x ∈ xm ∥₁
maybe-∈ᴱ {xm = just x} x∈ =
  erase $
  rec! (λ e → ∣ hereₘ e ∣₁)
    (∈ₛ∷-∉ᴱ x∈ ∉ₛ[] .erased)

∉-maybe : {xm : Maybe A}
          {x : A} → x ∉ xm → x ∉ from-maybe xm
∉-maybe {xm = nothing} x∉ = ∉ₛ[]
∉-maybe {xm = just x}  x∉ = ∉ₛ-∷ (contra hereₘ x∉) ∉ₛ[]

-- list

∈-list : {xs : List A}
         {x : A} → x ∈ xs → x ∈ₛ from-list xs
∈-list {xs = x ∷ xs} (here px)  = hereₛ px
∈-list {xs = x ∷ xs} (there xi) = thereₛ (∈-list xi)

list-∈ᴱ : {xs : List A}
          {x : A} → x ∈ₛ from-list xs → Erased ∥ x ∈ xs ∥₁
list-∈ᴱ {xs = x ∷ xs} x∈ =
  erase $
  rec!
    [ (λ e → ∣ here e ∣₁)
    , (λ z∈ → map there (list-∈ᴱ {xs = xs} z∈ .erased))
    ]ᵤ
    (∈ₛ-∷→ᴱ x∈ .erased)

∉-list : {xs : List A}
         {x : A} → x ∉ xs → x ∉ from-list xs
∉-list {xs = List.[]} x∉ = ∉ₛ[]
∉-list {xs = x ∷ xs}  x∉ = ∉ₛ-∷ (contra here x∉) (∉-list (contra there x∉))

-- vec

∈-vec : {n : ℕ} {xs : Vec A n}
        {x : A} → x ∈ xs → x ∈ₛ from-vec xs
∈-vec {n = suc n} {xs = x ∷ xs} =
  [ hereₛ
  , thereₛ ∘ ∈-vec {xs = xs}
  ]ᵤ ∘ ∈ᵥ-uncons

opaque
  unfolding filterₛ
  ∈-filterₛ : {p : A → Bool} {s : LFSet A} {z : A}
            → ⌞ p z ⌟ → z ∈ s
            → z ∈ filterₛ p s
  ∈-filterₛ {p} {s} {z} pz = elim-prop go s
    where
    go : Elim-prop λ q → z ∈ q → z ∈ filterₛ p q
    go .[]ʳ = id
    go .∷ʳ x {xs} ih z∈∷ with p x | recall p x
    ... | false | ⟪ eq ⟫ =
      -- TODO need better recomputability theory for these
      ⇉∈ₛ $ erase
        (rec! [ (λ e → false! $ (so≃is-true $ pz) ⁻¹ ∙ ap p e ∙ eq)
              , (λ q → ∈ₛ⇉ (ih (⇉∈ₛ (erase q))) .erased) ]ᵤ
              (∈ₛ⇉ z∈∷ .erased))
    ... | true  | _      =
      ⇉∈ₛ $ erase
        (rec! [ ∣_∣₁ ∘ inl
              , (λ q → ∣ inr (∈ₛ⇉ (ih (⇉∈ₛ (erase q))) .erased) ∣₁) ]ᵤ
              (∈ₛ⇉ z∈∷ .erased))
    go .truncʳ _ = hlevel!

  filter-∈ₛ : {p : A → Bool} {s : LFSet A} {z : A}
            → z ∈ filterₛ p s
            → ⌞ p z ⌟ × z ∈ s
  filter-∈ₛ {p} {s} {z} = elim-prop go s
    where
    go : Elim-prop λ q → z ∈ filterₛ p q → ⌞ p z ⌟ × z ∈ q
    go .[]ʳ = false! ⦃ Refl-x∉ₛ[] ⦄ -- why
    go .∷ʳ x {xs} ih z∈f with p x | recall p x
    ... | false | _ = rec! (λ pz z∈ → pz , thereₛ z∈) (ih z∈f)
    ... | true | ⟪ eq ⟫ =
      Recomputable-× Recomputable-So Recomputable-∈ₛ .recompute $ erase $
          rec! [ (λ e → (so≃is-true ⁻¹ $ ap p e ∙ eq) , (hereₛ e))
               , (λ z∈′ → let (pz , z∈) = ih (⇉∈ₛ (erase z∈′)) in
                           pz , thereₛ z∈)
               ]ᵤ (∈ₛ⇉ z∈f .erased)
    go .truncʳ _ = hlevel!

  ∉-filter : {p : A → Bool} {s : LFSet A} {z : A}
            → ⌞ not (p z) ⌟ ⊎ (z ∉ s)
            → z ∉ filterₛ p s
  ∉-filter {s} o z∈f =
     let (pz , z∈) = filter-∈ₛ {s = s} z∈f in
     [ flip so-not pz , _$ z∈ ]ᵤ o

  filter-∉ : {p : A → Bool} {s : LFSet A} {z : A}
            → z ∉ filterₛ p s
            → ⌞ not (p z) ⌟ ⊎ (z ∉ s)
  filter-∉ {p} {s} {z} z∉f with p z | recall p z
  ... | true  | ⟪ eq ⟫ =
    inr (contra (∈-filterₛ (so≃is-true ⁻¹ $ eq)) z∉f)
  ... | false | _ = inl oh

  filter-all : {p : A → Bool} {s : LFSet A}
             → (∀ {x} → x ∈ s → ⌞ p x ⌟)
             → filterₛ p s ＝ s
  filter-all {p} {s} = elim-prop go s
    where
    go : Elim-prop λ q → (∀ {x} → x ∈ q → ⌞ p x ⌟) → filterₛ p q ＝ q
    go .[]ʳ _ = refl
    go .∷ʳ x {xs} ih a =
      subst (λ q → (if q then x ∷ filterₛ p xs else filterₛ p xs) ＝ x ∷ xs)
            ((so≃is-true $ a (hereₛ refl)) ⁻¹)
            (ap (x ∷_) (ih (a ∘ thereₛ)))
    go .truncʳ _ = hlevel!

  filter-none : {p : A → Bool} {s : LFSet A}
             → (∀ {x} → x ∈ s → ⌞ not (p x) ⌟)
             → filterₛ p s ＝ []
  filter-none {p} {s} = elim-prop go s
    where
    go : Elim-prop λ q → (∀ {x} → x ∈ q → ⌞ not (p x) ⌟) → filterₛ p q ＝ []
    go .[]ʳ _ = refl
    go .∷ʳ x {xs} ih a =
      subst (λ q → (if q then x ∷ filterₛ p xs else filterₛ p xs) ＝ [])
            ((¬so≃is-false $ so-not (a (hereₛ refl))) ⁻¹)
            (ih (a ∘ thereₛ))
    go .truncʳ _ = hlevel!

  none-filter : {p : A → Bool} {s : LFSet A}
             → filterₛ p s ＝ []
             → ∀ {z} → z ∈ s → ⌞ not (p z) ⌟
  none-filter {p} {s} = elim-prop go s
    where
    go : Elim-prop λ q → filterₛ p q ＝ [] → ∀ {z} → z ∈ q → ⌞ not (p z) ⌟
    go .[]ʳ _ = false!
    go .∷ʳ x {xs} ih e z∈ with p x | recall p x
    ... | true  | _      = ⊥.absurd (∷≠[] e)
    ... | false | ⟪ eq ⟫ =
      Recomputable-Dec .recompute $ erase $
      rec!
        [ (λ z=x → not-so (¬so≃is-false ⁻¹ $ ap p z=x ∙ eq))
        , (ih e)
        ]ᵤ
        (∈ₛ-∷→ᴱ z∈ .erased)
    go .truncʳ _ = hlevel!

  filter-⊆ : {p : A → Bool} {s : LFSet A}
           → filterₛ p s ⊆ s
  filter-⊆ x∈ = filter-∈ₛ x∈ .snd

  filter-eq : ∀ {s} {p q : A → Bool}
            → (∀ {x} → x ∈ s → p x ＝ q x) → filterₛ p s ＝ filterₛ q s
  filter-eq {s} {p} {q} = elim-prop go s
    where
    go : Elim-prop λ z → (∀ {x} → x ∈ z → p x ＝ q x) → filterₛ p z ＝ filterₛ q z
    go .[]ʳ _ = refl
    go .∷ʳ x {xs} ih a with p x | recall p x
    ... | false | ⟪ eq ⟫ =
      ih (a ∘ thereₛ) ∙ if-false (not-so (¬so≃is-false ⁻¹ $ (a (hereₛ refl)) ⁻¹ ∙ eq)) ⁻¹
    ... | true  | ⟪ eq ⟫ =
      ap (x ∷_) (ih (a ∘ thereₛ)) ∙ if-true (so≃is-true ⁻¹ $ (a (hereₛ refl)) ⁻¹ ∙ eq) ⁻¹
    go .truncʳ = hlevel!

opaque
  unfolding mapₛ

  map-∈ᴱ : {A : 𝒰 ℓ} {B : 𝒰 ℓ′} -- why
            {f : A → B} {s : LFSet A} {z : B}
          → z ∈ mapₛ f s
          → Erased (∃[ x ꞉ A ] ((x ∈ₛ s) × (z ＝ f x)))
  map-∈ᴱ {A} {B} {f} {s} {z} = elim-prop go s
    where
    go : Elim-prop λ q → z ∈ mapₛ f q → Erased (∃[ x ꞉ A ] ((x ∈ₛ q) × (z ＝ f x)))
    go .[]ʳ = false! ⦃ Refl-x∉ₛ[] ⦄
    go .∷ʳ x {xs} ih x∈∷ =
      erase
        (rec!
              [ (λ z=fx → ∣ x , hereₛ refl , z=fx ∣₁)
              , (λ z∈fxs →
                    map (λ where (q , xq , zeq) → q , thereₛ xq , zeq)
                       (ih z∈fxs .erased)) ]ᵤ
              (∈ₛ-∷→ᴱ  x∈∷ .erased))
    go .truncʳ x = hlevel!

  ∈-mapₛ : {A : 𝒰 ℓ} {B : 𝒰 ℓ′} -- why
            {f : A → B} {s : LFSet A} {y : A}
          → y ∈ s → f y ∈ mapₛ f s
  ∈-mapₛ {f} {s} {y} = elim-prop go s
    where
    go : Elim-prop λ q → y ∈ q → f y ∈ mapₛ f q
    go .[]ʳ = false! ⦃ Refl-x∉ₛ[] ⦄
    go .∷ʳ x {xs} ih y∈∷ =
      Recomputable-∈ₛ .recompute $ erase
        (rec! [ (λ y=x → hereₛ (ap f y=x))
              , thereₛ ∘ ih
              ]ᵤ
           (∈ₛ-∷→ᴱ {x = x} y∈∷ .erased))
    go .truncʳ x = hlevel!

  eq-∈-mapₛ : {A : 𝒰 ℓ} {B : 𝒰 ℓ′}
              {f g : A → B} {s : LFSet A}
            → (∀ {x} → x ∈ s → f x ＝ g x)
            → mapₛ f s ＝ mapₛ g s
  eq-∈-mapₛ {f} {g} {s} = elim-prop go s
    where
    go : Elim-prop λ q → (∀ {x} → x ∈ q → f x ＝ g x) → mapₛ f q ＝ mapₛ g q
    go .[]ʳ _ = refl
    go .∷ʳ x {xs} ih efg =
      ap² {C = λ _ _ → LFSet _} _∷_
        (efg (hereₛ refl)) (ih (efg ∘ thereₛ))
    go .truncʳ x = hlevel!

opaque
  unfolding bindₛ

  bind-∈ᴱ : {A : 𝒰 ℓ} {B : 𝒰 ℓ′} -- why
            {f : A → LFSet B} {s : LFSet A} {z : B}
          → z ∈ bindₛ f s
          → Erased (∃[ x ꞉ A ] ((x ∈ₛ s) × (z ∈ₛ f x)))
  bind-∈ᴱ {A} {B} {f} {s} {z} = elim-prop go s
    where
    go : Elim-prop λ q → z ∈ bindₛ f q → Erased (∃[ x ꞉ A ] ((x ∈ₛ q) × (z ∈ₛ f x)))
    go .[]ʳ = false! ⦃ Refl-x∉ₛ[] ⦄
    go .∷ʳ x {xs} ih x∈∷ =
      erase (rec!
              [ (λ z∈fx → ∣ x , hereₛ refl , z∈fx ∣₁)
              , (λ z∈fxs →
                    map (λ where (q , xq , zq) → q , thereₛ xq , zq)
                       (ih z∈fxs .erased)) ]ᵤ
              (∈ₛ-∪∷→ᴱ {s₁ = f x} x∈∷ .erased))
    go .truncʳ x = hlevel!

  ∈-bind : {A : 𝒰 ℓ} {B : 𝒰 ℓ′} -- why
            {f : A → LFSet B} {s : LFSet A} {z : B} {y : A}
          → y ∈ s → z ∈ f y → z ∈ bindₛ f s
  ∈-bind {f} {s} {z} {y} y∈ z∈ = elim-prop go s y∈
    where
    go : Elim-prop λ q → y ∈ q → z ∈ bindₛ f q
    go .[]ʳ = false! ⦃ Refl-x∉ₛ[] ⦄
    go .∷ʳ x {xs} ih y∈∷ =
      Recomputable-∈ₛ .recompute $ erase
        (rec! [ (λ e → ∈ₛ-∪∷←l {s₁ = f x} (subst (λ q → z ∈ₛ f q) e z∈))
              , ∈ₛ-∪∷←r {s₁ = f x} ∘ ih
              ]ᵤ
           (∈ₛ-∷→ᴱ {x = x} y∈∷ .erased))
    go .truncʳ x = hlevel!

opaque
  unfolding joinₛ

  -- TODO we can also get rid of erasure by requiring decidability on ≤ directly
  joinₛ-∈-≤ᴱ : {o ℓ : Level} {A : Poset o ℓ} {js : is-join-semilattice A}
          → {z : Poset.Ob A} {xs : LFSet (Poset.Ob A)}
          → z ∈ xs → Erased (Poset._≤_ A z (joinₛ {js = js} xs))
  joinₛ-∈-≤ᴱ {A} {js} {z} {xs} = elim-prop go xs
    where
      open Poset A renaming (_≤_ to _≤ₐ_ ; =→≤ to =→≤ₐ)
      open is-join-semilattice js
      go : Elim-prop λ q → z ∈ q → Erased (z ≤ₐ joinₛ {js = js} q)
      go .[]ʳ = false!
      go .∷ʳ x ih z∈∷ =
         erase (rec! (≤⊎→∪ ∘ Sum.dmap =→≤ₐ (erased ∘ ih)) (∈ₛ-∷→ᴱ z∈∷ .erased))
      go .truncʳ = hlevel!

  joinₛ-∈-least : {o ℓ : Level} {A : Poset o ℓ} {js : is-join-semilattice A}
          → {z : Poset.Ob A} {xs : LFSet (Poset.Ob A)}
          → (∀ {x} → x ∈ xs → Poset._≤_ A x z)
          → Poset._≤_ A (joinₛ {js = js} xs) z
  joinₛ-∈-least {A} {js} {z} {xs} = elim-prop go xs
    where
      open Poset A renaming (_≤_ to _≤ₐ_)
      open is-join-semilattice js
      go : Elim-prop λ q → (∀ {x} → x ∈ q → x ≤ₐ z) → joinₛ {js = js} q ≤ₐ z
      go .[]ʳ _ = ¡
      go .∷ʳ x ih u =
        ∪≃≤× ⁻¹ $ u (hereₛ refl) , ih (u ∘ thereₛ)
      go .truncʳ = hlevel!

opaque
  unfolding meetₛ

  meetₛ-∈-≤ᴱ : {o ℓ : Level} {A : Poset o ℓ} {ms : is-meet-semilattice A}
          → {z : Poset.Ob A} {xs : LFSet (Poset.Ob A)}
          → z ∈ xs → Erased (Poset._≤_ A (meetₛ {ms = ms} xs) z)
  meetₛ-∈-≤ᴱ {A} {ms} {z} {xs} = elim-prop go xs
    where
      open Poset A renaming (_≤_ to _≤ₐ_ ; =→≤ to =→≤ₐ)
      open is-meet-semilattice ms
      go : Elim-prop λ q → z ∈ q → Erased (meetₛ {ms = ms} q ≤ₐ z)
      go .[]ʳ = false!
      go .∷ʳ x ih z∈∷ =
         erase (rec! (≤⊎→∩ ∘ Sum.dmap (=→≤ₐ ∘ _⁻¹) (erased ∘ ih)) (∈ₛ-∷→ᴱ z∈∷ .erased))
      go .truncʳ = hlevel!

  meetₛ-∈-greatest : {o ℓ : Level} {A : Poset o ℓ} {ms : is-meet-semilattice A}
          → {z : Poset.Ob A} {xs : LFSet (Poset.Ob A)}
          → (∀ {x} → x ∈ xs → Poset._≤_ A z x)
          → Poset._≤_ A z (meetₛ {ms = ms} xs)
  meetₛ-∈-greatest {A} {ms} {z} {xs} = elim-prop go xs
    where
      open Poset A renaming (_≤_ to _≤ₐ_)
      open is-meet-semilattice ms
      go : Elim-prop λ q → (∀ {x} → x ∈ q → Poset._≤_ A z x) → Poset._≤_ A z (meetₛ {ms = ms} q)
      go .[]ʳ _ = !
      go .∷ʳ x ih l =
         ∩≃≤× ⁻¹ $ l (hereₛ refl) , ih (l ∘ thereₛ)
      go .truncʳ = hlevel!
