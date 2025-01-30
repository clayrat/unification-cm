{-# OPTIONS --safe #-}
module LFSet.Membership where

open import Prelude
open import Foundations.Sigma
open import Meta.Effect

open import Data.Empty hiding (_≠_ ; elim ; rec)
open import Data.Dec as Dec hiding (elim ; rec)
open import Data.Reflects as Reflects
open import Data.Bool as Bool hiding (elim ; rec)
open import Data.Sum
open import Data.Nat hiding (elim ; rec)
open import Data.Nat.Order.Base
open import Data.Nat.Two

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

∈ₛ∷-∉ᴱ : {z x : A} {xs : LFSet A} → z ∈ₛ (x ∷ xs) → z ∉ xs → Erased (∥ z ＝ x ∥₁)
∈ₛ∷-∉ᴱ z∈∷ z∉ =
  erase (rec! [ ∣_∣₁
              , (λ z∈ → absurd (z∉ (⇉∈ₛ (erase z∈)))) ]ᵤ ((∈ₛ⇉ z∈∷) .erased))

∉ₛ-∷ : {z x : A} {xs : LFSet A} → z ≠ x → z ∉ xs → z ∉ (x ∷ xs)
∉ₛ-∷ z≠x z∉xs z∈∷ =
  Recomputable-⊥ .recompute $ erase $
  rec! [ z≠x , contra (λ q → ⇉∈ₛ $ erase q) z∉xs ]ᵤ ((∈ₛ⇉ z∈∷) .erased)

∉ₛ-uncons : {z x : A} {xs : LFSet A} → z ∉ (x ∷ xs) → (z ≠ x) × z ∉ xs
∉ₛ-uncons z∉∷ = contra hereₛ z∉∷ , contra thereₛ z∉∷

∉ₛ[] : {x : A} → x ∉ []
∉ₛ[] x with ∈ₛ⇉ x
... | ()

instance
  Refl-x∉ₛ[] : {x : A} → Reflects (x ∈ₛ []) false
  Refl-x∉ₛ[] = ofⁿ ∉ₛ[]

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
      ((rec! [ (λ e → ap (_∷ x ∷ xs) e ∙ drop)
             , (λ z∈′ → swap ∙ ap (x ∷_) (ih (⇉∈ₛ (erase z∈′)) .erased))
             ]ᵤ (∈ₛ⇉ z∈ .erased)))
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

opaque
  unfolding filterₛ
  ∈-filter : {p : A → Bool} {s : LFSet A} {z : A}
            → ⌞ p z ⌟ → z ∈ s
            → z ∈ filterₛ p s
  ∈-filter {p} {s} {z} pz = elim-prop go s
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
    inr (contra (∈-filter (so≃is-true ⁻¹ $ eq)) z∉f)
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
