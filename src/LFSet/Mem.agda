{-# OPTIONS --safe #-}
module LFSet.Mem where

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

∈ₛ∷-≠ : {z x : A} {xs : LFSet A} → z ≠ x → z ∈ₛ (x ∷ xs) → z ∈ₛ xs
∈ₛ∷-≠ z≠x z∈∷ =
  ⇉∈ₛ $ erase
    (rec! [ (λ e → absurd (z≠x e)) , id ]ᵤ ((∈ₛ⇉ z∈∷) .erased))

∉ₛ-∷ : {z x : A} {xs : LFSet A} → z ≠ x → z ∉ xs → z ∉ (x ∷ xs)
∉ₛ-∷ z≠x z∉xs z∈∷ =
  Recomputable-⊥ .recompute $ erase $
  rec! [ z≠x , contra (λ q → ⇉∈ₛ $ erase q) z∉xs ]ᵤ ((∈ₛ⇉ z∈∷) .erased)

∉ₛ-uncons : {z x : A} {xs : LFSet A} → z ∉ (x ∷ xs) → (z ≠ x) × z ∉ xs
∉ₛ-uncons z∉∷ = contra hereₛ z∉∷ , contra thereₛ z∉∷

∉ₛ[] : {x : A} → x ∉ []
∉ₛ[] x with ∈ₛ⇉ x
... | ()

_∈ₛ?_ : ⦃ is-discrete A ⦄ → A → LFSet A → Bool
_∈ₛ?_ {A} z = rec go
  where
  go : Rec A Bool
  go .[]ʳ = false
  go .∷ʳ x xs b = z =? x or b
  go .dropʳ x y p =
     or-assoc (z =? x) (z =? x) p ⁻¹
   ∙ ap (_or p) (or-idem (z =? x))
  go .swapʳ x y w p =
     or-assoc (z =? x) (z =? y) p ⁻¹
   ∙ ap (_or p) (or-comm (z =? x) (z =? y))
   ∙ or-assoc (z =? y) (z =? x) p
  go .truncʳ = hlevel!

instance
  Reflects-∈ₛ? : ⦃ d : is-discrete A ⦄ {x : A} {xs : LFSet A}
                  → Reflects (x ∈ₛ xs) (x ∈ₛ? xs)
  Reflects-∈ₛ? ⦃ d ⦄ {x} {xs} = elim-prop go xs
    where
    go : Elim-prop λ q → Reflects (x ∈ₛ q) (x ∈ₛ? q)
    go .[]ʳ = ofⁿ ∉ₛ[]
    go .∷ʳ z r = Reflects.dmap [ hereₛ , thereₛ ]ᵤ
                               (λ ne → ∉ₛ-∷ (contra inl ne) (contra inr ne))
                               (Reflects-⊎ ⦃ rp = d .proof ⦄ ⦃ rq = r ⦄)
    go .truncʳ zs = hlevel!

  Dec-∈ₛ
    : ⦃ di : is-discrete A ⦄
    → {a : A} {xs : LFSet A}
    → Dec (a ∈ₛ xs)
  Dec-∈ₛ {a} {xs} .does = a ∈ₛ? xs
  Dec-∈ₛ     {xs} .proof = Reflects-∈ₛ? {xs = xs}
  {-# OVERLAPPING Dec-∈ₛ #-}

  Refl-x∉ₛ[] : {x : A} → Reflects (x ∈ₛ []) false
  Refl-x∉ₛ[] = ofⁿ ∉ₛ[]

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

∈ₛ-∪∷→ : {z : A} {s₁ s₂ : LFSet A}
        → z ∈ₛ (s₁ ∪∷ s₂) → Erased ((z ∈ₛ s₁) ⊎₁ (z ∈ₛ s₂))
∈ₛ-∪∷→ {z} {s₁} {s₂} = elim-prop go s₁
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

∈ₛ?-∪∷ : ⦃ d : is-discrete A ⦄ {z : A} {s₁ s₂ : LFSet A}
        →  z ∈ₛ? (s₁ ∪∷ s₂) ＝ (z ∈ₛ? s₁) or (z ∈ₛ? s₂)
∈ₛ?-∪∷ {z} {s₁} {s₂} = elim-prop go s₁
  where
  go : Elim-prop λ q → z ∈ₛ? (q ∪∷ s₂) ＝ (z ∈ₛ? q) or (z ∈ₛ? s₂)
  go .[]ʳ = refl
  go .∷ʳ x {xs} ih = ap ((z =? x) or_) ih ∙ or-assoc (z =? x) (z ∈ₛ? xs) (z ∈ₛ? s₂) ⁻¹
  go .truncʳ x = hlevel!

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

  filter-∈ : {p : A → Bool} {s : LFSet A} {z : A}
            → z ∈ filterₛ p s
            → ⌞ p z ⌟ × z ∈ s
  filter-∈ {p} {s} {z} = elim-prop go s
    where
    go : Elim-prop λ q → z ∈ filterₛ p q → ⌞ p z ⌟ × z ∈ q
    go .[]ʳ = false! ⦃ Refl-x∉ₛ[] ⦄ -- why
    go .∷ʳ x {xs} ih z∈f with p x | recall p x
    ... | false | _ = rec! (λ pz z∈ → pz , thereₛ z∈) (ih z∈f)
    ... | true | ⟪ eq ⟫ =
      Recomputable-× Recomputable-So Recomputable-∈ₛ .recompute $ erase $
          rec! [ (λ e → (so≃is-true ⁻¹ $ ap p e ∙ eq) , (hereₛ e))
               , (λ z∈′ → let (pz , z∈) = ih (⇉∈ₛ (erase z∈′)) in
                           pz , thereₛ z∈ )
               ]ᵤ (∈ₛ⇉ z∈f .erased)
    go .truncʳ _ = hlevel!

  ∉-filter : {p : A → Bool} {s : LFSet A} {z : A}
            → ⌞ not (p z) ⌟ ⊎ (z ∉ s)
            → z ∉ filterₛ p s
  ∉-filter {s} o z∈f =
     let (pz , z∈) = filter-∈ {s = s} z∈f in
     [ flip so-not pz , _$ z∈ ]ᵤ o

  filter-∉ : ⦃ d : is-discrete A ⦄ {p : A → Bool} {s : LFSet A} {z : A}
            → z ∉ filterₛ p s
            → ⌞ not (p z) ⌟ ⊎ (z ∉ s)
  filter-∉ {p} {s} {z} z∉f =
    -- TODO kinda meh
    so→true! $
    subst So (not-and (p z) (z ∈ₛ? s)) $
    not-so $
    contra (  ∈-filter {p = p} {s = s} $²_
            ∘ second so→true!
            ∘ (and-so-≃ {x = p z} {y = z ∈ₛ? s} $_)) $
    z∉f

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
  filter-⊆ x∈ = filter-∈ x∈ .snd

  filter-∪∷ : {p : A → Bool} {s r : LFSet A}
             → filterₛ p (s ∪∷ r) ＝ filterₛ p s ∪∷ filterₛ p r
  filter-∪∷ {p} {s} {r} = elim-prop go s
    where
    go : Elim-prop λ q → filterₛ p (q ∪∷ r) ＝ filterₛ p q ∪∷ filterₛ p r
    go .[]ʳ = refl
    go .∷ʳ x {xs} ih with p x
    ... | false = ih
    ... | true  = ap (x ∷_) ih
    go .truncʳ = hlevel!

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
  unfolding filterₛ rem
  rem-⊆ : ⦃ d : is-discrete A ⦄ → {x : A} {s : LFSet A}
         → rem ⦃ d ⦄ x s ⊆ s
  rem-⊆ = filter-⊆

opaque
  unfolding filterₛ rem
  -- TODO generalize to filter?
  rem-∉ : ⦃ d : is-discrete A ⦄ {s : LFSet A} {z : A}
         → z ∉ s → rem z s ＝ s
  rem-∉ {s} {z} = elim-prop go s
    where
    go : Elim-prop λ q → z ∉ q → rem z q ＝ q
    go .[]ʳ _ = refl
    go .∷ʳ x {xs} ih z∉∷ =
      let (z≠x , z∉) = ∉ₛ-uncons {xs = xs} z∉∷ in
      given-no z≠x
         return (λ q → (if (not ⌊ q ⌋) then x ∷ rem z xs else rem z xs) ＝ x ∷ xs)
         then ap (x ∷_) (ih z∉)
    go .truncʳ x = hlevel!

  ∉-rem : ⦃ d : is-discrete A ⦄ {s : LFSet A} {x z : A}
         → (z ＝ x) ⊎ (z ∉ s)
         → z ∉ rem x s
  ∉-rem {x} {z} =
    ∉-filter ∘ map-l λ e → subst So (not-invol (x =? z) ⁻¹) (true→so! {P = x ＝ z} (e ⁻¹))

  rem-∈ : ⦃ d : is-discrete A ⦄ {z x : A} {s : LFSet A}
         → z ∈ rem x s → (z ≠ x) × z ∈ s
  rem-∈ = first (λ q → so→false! q ∘ _⁻¹) ∘ filter-∈

  rem-∈-≠ : ⦃ d : is-discrete A ⦄ {z x : A} {s : LFSet A}
           → z ≠ x → z ∈ₛ s → z ∈ₛ rem x s
  rem-∈-≠ z≠x = ∈-filter (false→so! (z≠x ∘ _⁻¹))

-- minus

opaque
  unfolding rem

  minus : ⦃ is-discrete A ⦄ → LFSet A → LFSet A → LFSet A
  minus xs ys = filterₛ (λ x → not (x ∈ₛ? ys)) xs

  minus-[]-r : ⦃ d : is-discrete A ⦄ → {s : LFSet A} → minus s [] ＝ s
  minus-[]-r = filter-all λ _ → oh

  minus-∷-r : ⦃ d : is-discrete A ⦄ {x : A} {s r : LFSet A}
            → minus s (x ∷ r) ＝ rem x (minus s r)
  minus-∷-r {x} {s} {r} =
    filterₛ (λ q → not (q ∈ₛ? (x ∷ r))) s
      =⟨ ap (λ q → filterₛ q s) (fun-ext λ q → ap (λ w → not (w or (q ∈ₛ? r))) (=?-sym {x = q}) ∙ not-or (x =? q) (q ∈ₛ? r)) ⟩
    filterₛ (λ q → not (x =? q) and not (q ∈ₛ? r)) s
      =⟨ filter-and {s = s} ⟩
    filterₛ (not ∘ x =?_) (filterₛ (λ x → not (x ∈ₛ? r)) s)
      ∎

  minus-rem-l : ⦃ d : is-discrete A ⦄ {x : A} {s r : LFSet A}
              → minus (rem x s) r ＝ rem x (minus s r)
  minus-rem-l {x} {s} {r} =
    (filterₛ (λ x → not (x ∈ₛ? r)) (filterₛ (not ∘ x =?_) s))
      =⟨ filter-and {s = s} ⁻¹ ⟩
    filterₛ (λ q → not (q ∈ₛ? r) and not (x =? q)) s
      =⟨ ap (λ q → filterₛ q s) (fun-ext (λ q → and-comm (not (q ∈ₛ? r)) (not (x =? q)))) ⟩
    filterₛ (λ q → not (x =? q) and not (q ∈ₛ? r)) s
      =⟨ filter-and {s = s} ⟩
    filterₛ (not ∘ x =?_) (filterₛ (λ x → not (x ∈ₛ? r)) s)
      ∎

  minus-⊆ : ⦃ d : is-discrete A ⦄ {xs ys : LFSet A}
           → minus xs ys ⊆ xs
  minus-⊆ = filter-⊆

  ∈-minus : ⦃ d : is-discrete A ⦄ {z : A} {xs ys : LFSet A}
           → z ∈ xs
           → z ∉ ys
           → z ∈ minus xs ys
  ∈-minus z∈xs z∉ys = ∈-filter (false→so! z∉ys) z∈xs

  minus-minus : ⦃ d : is-discrete A ⦄ {v s₁ s₂ : LFSet A}
              → minus (minus v s₁) s₂ ＝ minus v (s₁ ∪∷ s₂)
  minus-minus {v} {s₁} {s₂} =
      filter-and {s = v} ⁻¹
    ∙ ap (λ q → filterₛ q v)
         (fun-ext λ z →   not-or (z ∈ₛ? s₂) (z ∈ₛ? s₁) ⁻¹
                        ∙ ap not (  or-comm (z ∈ₛ? s₂) (z ∈ₛ? s₁)
                                  ∙ ∈ₛ?-∪∷ {s₁ = s₁} ⁻¹))

-- size

calc : ⦃ d : is-discrete A ⦄ → A → LFSet A → ℕ
calc x xs = bit (not (x ∈ₛ? xs))

calc-filter= : ⦃ d : is-discrete A ⦄ {p : A → Bool} {x : A} {xs : LFSet A}
             → ⌞ p x ⌟ → calc x (filterₛ p xs) ＝ calc x xs
calc-filter= {p} {x} {xs} px with Dec-∈ₛ {a = x} {xs = filterₛ p xs}
... | yes x∈f =
  ap (bit ∘ not) (  (so≃is-true $ true→so! x∈f)
                 ∙ (so≃is-true $ true→so! $ filter-⊆ x∈f) ⁻¹)
... | no x∉f =
  ap (bit ∘ not) (  (¬so≃is-false $ so-not $ false→so! x∉f)
                  ∙ (¬so≃is-false $ so-not $ false→so! (contra (∈-filter px) x∉f)) ⁻¹)

opaque
  sizeₛ : ⦃ d : is-discrete A ⦄ → LFSet A → ℕ
  sizeₛ {A} ⦃ d ⦄ = rec go
    where
    go : Rec A ℕ
    go .[]ʳ = 0
    go .∷ʳ x xs n = calc x xs + n
    go .dropʳ x xs n =
       given-yes_return_then_
         ⦃ A-pr = hlevel-instance (is-discrete→is-set d x x) ⦄ -- TODO local instance or smth
         refl
         (λ q → (bit (not (⌊ q ⌋ or x ∈ₛ? xs)) + (calc x xs + n) ＝ calc x xs + n))
         refl
    go .swapʳ x y xs n =
      Dec.elim
        {C = λ q → bit (not (⌊ q ⌋ or x ∈ₛ? xs)) + (calc y xs + n) ＝ calc y (x ∷ xs) + (calc x xs + n)}
        (λ x=y → given-yes_return_then_
                     ⦃ A-pr = hlevel-instance (is-discrete→is-set d y x) ⦄
                     (x=y ⁻¹)
                     (λ q → calc y xs + n ＝ bit (not (⌊ q ⌋ or y ∈ₛ? xs)) + (calc x xs + n))
                     (ap (λ q → calc q xs + n) (x=y ⁻¹)))
        (λ x≠y → given-no x≠y ∘ _⁻¹
                    return (λ q → calc x xs + (calc y xs + n) ＝ bit (not (⌊ q ⌋ or y ∈ₛ? xs)) + (calc x xs + n))
                    then +-comm-assoc (calc x xs) (calc y xs) n)
        (x ≟ y)
    go .truncʳ = hlevel!

opaque
  unfolding filterₛ sizeₛ
  filter-size≤ : ⦃ d : is-discrete A ⦄ {p : A → Bool} {s : LFSet A}
               → sizeₛ (filterₛ p s) ≤ sizeₛ s
  filter-size≤ {p} {s} = elim-prop go s
    where
    go : Elim-prop λ q → sizeₛ (filterₛ p q) ≤ sizeₛ q
    go .[]ʳ = z≤
    go .∷ʳ x {xs} ih with p x | recall p x
    ... | false | _ = ih ∙ ≤-+-l
    ... | true | ⟪ eq ⟫ = ≤-+ (=→≤ $ calc-filter= {xs = xs} (so≃is-true ⁻¹ $ eq)) ih
    go .truncʳ = hlevel!

  all←filter-size= : ⦃ d : is-discrete A ⦄ {p : A → Bool} {s : LFSet A}
                   → sizeₛ (filterₛ p s) ＝ sizeₛ s
                   → ∀ {z : A} → z ∈ s → ⌞ p z ⌟
  all←filter-size= {A} {p} {s} = elim-prop go s
    where
    go : Elim-prop λ q → sizeₛ (filterₛ p q) ＝ sizeₛ q → ∀ {z : A} → z ∈ q → ⌞ p z ⌟
    go .[]ʳ _ = false! ⦃ Refl-x∉ₛ[] ⦄ -- why
    go .∷ʳ x {xs} ih e z∈ with p x | recall p x
    go .∷ʳ x {xs} ih e z∈ | false | ⟪ eq ⟫ with Dec-∈ₛ {a = x} {xs = xs}
    go .∷ʳ x {xs} ih e z∈ | false | ⟪ eq ⟫ | yes x∈ =
       absurd ((¬so≃is-false ⁻¹ $ eq) (ih (e ∙ ap (λ q → bit (not q) + sizeₛ xs) (so≃is-true $ true→so! x∈)) x∈))
    go .∷ʳ x {xs} ih e z∈ | false | ⟪ eq ⟫ | no x∉ =
       absurd (suc≰id (subst (_≤ sizeₛ xs)
                             (e ∙ ap (λ q → bit (not q) + sizeₛ xs) (¬so≃is-false $ so-not $ false→so! x∉))
                             (filter-size≤ {s = xs})))
    go .∷ʳ x {xs} ih e z∈ | true  | ⟪ eq ⟫ =
      Recomputable-So .recompute $ erase
        (rec! [ (λ z=x → so≃is-true ⁻¹ $ ap p z=x ∙ eq)
              , (λ z∈′ → ih (+-cancel-l (calc x xs) (sizeₛ (filterₛ p xs)) (sizeₛ xs)
                                (ap (_+ sizeₛ (filterₛ p xs)) (calc-filter= {xs = xs} (so≃is-true ⁻¹ $ eq) ⁻¹) ∙ e))
                             (⇉∈ₛ (erase z∈′))) ]ᵤ
              (∈ₛ⇉ z∈ .erased))
    go .truncʳ = hlevel!

  all→filter-size= : ⦃ d : is-discrete A ⦄ {p : A → Bool} {s : LFSet A}
                   → (∀ {x : A} → x ∈ s → ⌞ p x ⌟)
                   → sizeₛ (filterₛ p s) ＝ sizeₛ s
  all→filter-size= {A} {p} {s} = elim-prop go s
    where
    go : Elim-prop λ q → (∀ {x : A} → x ∈ q → ⌞ p x ⌟) → sizeₛ (filterₛ p q) ＝ sizeₛ q
    go .[]ʳ _ = refl
    go .∷ʳ x {xs} ih a =
      subst (λ q → sizeₛ (if q then x ∷ filterₛ p xs else filterₛ p xs) ＝ sizeₛ (x ∷ xs))
            ((so≃is-true $ a (hereₛ refl)) ⁻¹)
            (  ap (_+ sizeₛ (filterₛ p xs)) (calc-filter= {xs = xs} (a (hereₛ refl)))
             ∙ ap (calc x xs +_) (ih (a ∘ thereₛ)))
    go .truncʳ = hlevel!

filter-size-neg : ⦃ d : is-discrete A ⦄ {p : A → Bool} {s : LFSet A} {z : A}
                → ⌞ not (p z) ⌟ → z ∈ s → sizeₛ (filterₛ p s) < sizeₛ s
filter-size-neg {p} {s} {z} npz z∈ =
  ≤→<⊎= (filter-size≤ {p = p} {s = s}) &
  [ id
  , (λ r → absurd (so-not npz (all←filter-size= r z∈))) ]ᵤ
