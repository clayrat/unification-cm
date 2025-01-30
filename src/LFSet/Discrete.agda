{-# OPTIONS --safe #-}
module LFSet.Discrete where

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
open import LFSet.Membership

private variable
  ℓ ℓ′ : Level
  A : 𝒰 ℓ
  B : 𝒰 ℓ′

-- discrete ops and properties

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

∈ₛ-∷→ : ⦃ di : is-discrete A ⦄
      → {z x : A} {xs : LFSet A} → z ∈ₛ (x ∷ xs) → (z ＝ x) ⊎ (z ∈ₛ xs)
∈ₛ-∷→ ⦃ di ⦄ {z} {x} {xs} z∈∷ with z ∈? xs
... | yes z∈ = inr z∈
... | no z≠x =
  inl (Recomputable-Dec .recompute
         (map (∥-∥₁.elim (λ _ → is-discrete→is-set di z x) id)  -- why?
              (∈ₛ∷-∉ᴱ z∈∷ z≠x)))

∈ₛ∷-∉ : ⦃ di : is-discrete A ⦄
       → {z x : A} {xs : LFSet A} → z ∈ₛ (x ∷ xs) → z ∉ xs → z ＝ x
∈ₛ∷-∉ z∈∷ z∉ =
  [ id
  , (λ z∈ → absurd (z∉ z∈)) ]ᵤ
  (∈ₛ-∷→ z∈∷)

∈ₛ-∪∷→ : ⦃ di : is-discrete A ⦄
        → {z : A} {xs ys : LFSet A}
        → z ∈ₛ (xs ∪∷ ys) → (z ∈ₛ xs) ⊎ (z ∈ₛ ys)
∈ₛ-∪∷→ ⦃ di ⦄ {z} {xs} {ys} z∈∷ with z ∈? xs
... | yes z∈ = inl z∈
... | no z∉ = inr (∈ₛ∪∷-∉ z∈∷ z∉)

∈ₛ?-∪∷ : ⦃ d : is-discrete A ⦄ {z : A} {s₁ s₂ : LFSet A}
        →  z ∈ₛ? (s₁ ∪∷ s₂) ＝ (z ∈ₛ? s₁) or (z ∈ₛ? s₂)
∈ₛ?-∪∷ {z} {s₁} {s₂} = elim-prop go s₁
  where
  go : Elim-prop λ q → z ∈ₛ? (q ∪∷ s₂) ＝ (z ∈ₛ? q) or (z ∈ₛ? s₂)
  go .[]ʳ = refl
  go .∷ʳ x {xs} ih = ap ((z =? x) or_) ih ∙ or-assoc (z =? x) (z ∈ₛ? xs) (z ∈ₛ? s₂) ⁻¹
  go .truncʳ x = hlevel!

opaque
  unfolding filterₛ rem
  rem-⊆ : ⦃ d : is-discrete A ⦄ → {x : A} {s : LFSet A}
         → rem ⦃ d ⦄ x s ⊆ s
  rem-⊆ = filter-⊆

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
  rem-∈ = first (λ q → so→false! q ∘ _⁻¹) ∘ filter-∈ₛ

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

opaque
  unfolding rem
  rem-size-neg : ⦃ d : is-discrete A ⦄ {s : LFSet A} {z : A}
               → z ∈ s → sizeₛ (rem z s) < sizeₛ s
  rem-size-neg {z} z∈ =
    filter-size-neg
      (subst So (not-invol (z =? z) ⁻¹) (true→so! ⦃ Reflects-does {P = z ＝ z} ⦄ refl))
      z∈

opaque
  unfolding bindₛ

  -- to get rid of truncation, we'd have to guarantee that x is uniquely determined by z
  bind-∈ : {A : 𝒰 ℓ} {B : 𝒰 ℓ′} -- why
          → ⦃ dB : is-discrete B ⦄
          → {f : A → LFSet B} {s : LFSet A} {z : B}
          → z ∈ bindₛ f s
          → ∃[ x ꞉ A ] ((x ∈ₛ s) × (z ∈ₛ f x))
  bind-∈ {A} {B} ⦃ dB ⦄ {f} {s} {z} = elim-prop go s
    where
    go : Elim-prop λ q → z ∈ bindₛ f q → ∃[ x ꞉ A ] ((x ∈ₛ q) × (z ∈ₛ f x))
    go .[]ʳ = false! ⦃ Refl-x∉ₛ[] ⦄
    go .∷ʳ x {xs} ih x∈∷ =
      [ (λ z∈fx → ∣ x , hereₛ refl , z∈fx ∣₁)
      , (λ z∈fxs →
           map (λ where (q , xq , zq) → q , thereₛ xq , zq)
               (ih z∈fxs))
      ]ᵤ (∈ₛ-∪∷→ {xs = f x} x∈∷)
    go .truncʳ x = hlevel!
