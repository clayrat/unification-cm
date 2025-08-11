{-# OPTIONS --safe #-}
module LFSet.Discrete where

open import Prelude
open import Foundations.Sigma
open import Meta.Effect

open import Data.Empty hiding (_≠_ ; elim ; rec)
open import Data.Dec as Dec hiding (elim ; rec)
open import Data.Reflects as Reflects
open import Data.Reflects.Sigma as ReflectsΣ
open import Data.Bool as Bool hiding (elim ; rec)
open import Data.Sum as Sum
open import Data.Nat hiding (elim ; rec)
open import Data.Nat.Order.Base
open import Data.Nat.Two
open import Data.Nat.Two.Properties
open import Data.Maybe hiding (elim ; rec)
open import Data.Maybe.Correspondences.Unary.Any renaming (here to hereₘ)

open import Data.List hiding (elim ; rec ; drop ; empty?)
open import Data.List.Correspondences.Unary.Unique
open import Data.List.Correspondences.Unary.Any
open import Data.List.Membership

open import Data.Vec.Inductive hiding (elim ; rec)

open import Order.Base
open import Order.Semilattice.Join
open import Order.Semilattice.Meet

open import LFSet
open import LFSet.Membership

private variable
  ℓ ℓ′ ℓ″ : Level
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

sng-∈ : ⦃ di : is-discrete A ⦄
      → {x z : A} → x ∈ₛ sng z → x ＝ z
sng-∈ x∈ = ∈ₛ∷-∉ x∈ ∉ₛ[]

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

∈ₛ?-filter : ⦃ d : is-discrete A ⦄ {z : A} {p : A → Bool} {s : LFSet A}
           → z ∈ₛ? filterₛ p s ＝ p z and (z ∈ₛ? s)
∈ₛ?-filter {z} {p} {s} =
  so→true! $
  subst So (biimplies-equals (z ∈ₛ? filterₛ p s) (p z and (z ∈ₛ? s))) $
  and-so-≃ {x = (z ∈ₛ? filterₛ p s) implies p z and (z ∈ₛ? s)} ⁻¹ $
    true→so! ⦃ reflects-implies ⦄
             (λ zf → let (pz , zm) = filter-∈ₛ (so→true! zf) in
                     and-so-≃ ⁻¹ $ pz , true→so! zm)
  , true→so! ⦃ reflects-implies ⦄
             (λ pz → let pzzm = and-so-≃ $ pz in
                     true→so! (∈-filterₛ (pzzm .fst) (so→true! (pzzm .snd))))

∈ₛ-∷= : ⦃ d : is-discrete A ⦄
      → {z : A} {s : LFSet A}
      → z ∈ₛ s → z ∷ s ＝ s
∈ₛ-∷= {z} {s} = elim-prop go s
  where
  go : Elim-prop λ q → z ∈ₛ q → z ∷ q ＝ q
  go .[]ʳ = false! ⦃ Refl-x∉ₛ[] ⦄ -- why
  go .∷ʳ x {xs} ih z∈ =
    [ (λ e → ap (_∷ x ∷ xs) e ∙ drop)
    , (λ z∈′ → swap ∙ ap (x ∷_) (ih z∈′)) ]ᵤ (∈ₛ-∷→ z∈)
  go .truncʳ _ = hlevel!

⊆-∪= : ⦃ d : is-discrete A ⦄
      → {xs ys : LFSet A}
      → xs ⊆ ys → xs ∪∷ ys ＝ ys
⊆-∪= {xs} {ys} = elim-prop go xs
  where
  go : Elim-prop λ q → q ⊆ ys → q ∪∷ ys ＝ ys
  go .[]ʳ _ = refl
  go .∷ʳ x {xs} ih su =
      ∈ₛ-∷= (∈ₛ-∪∷←r {s₁ = xs} (su (hereₛ refl)))
    ∙ ih (su ∘ thereₛ)
  go .truncʳ x = hlevel!

-- lfset extensionality

set-ext : ⦃ is-discrete A ⦄
        → {xs ys : LFSet A}
        → ((z : A) → z ∈ xs ≃ z ∈ ys) → xs ＝ ys
set-ext {xs} {ys} e =
    ⊆-∪= {xs = ys} (λ {x} x∈ys → e x ⁻¹ $ x∈ys) ⁻¹
  ∙ ∪∷-comm {x = ys}
  ∙ ⊆-∪= {xs = xs} (λ {x} x∈xs → e x $ x∈xs)

maybe-∈ : ⦃ d : is-discrete A ⦄
        → {xm : Maybe A}
        → {z : A} → z ∈ₛ from-maybe xm → z ∈ xm
maybe-∈ {xm = just x} z∈ = hereₘ $ ∈ₛ∷-∉ z∈ ∉ₛ[]

list-∈ : ⦃ d : is-discrete A ⦄
       → {xs : List A}
       → {z : A} → z ∈ₛ from-list xs → z ∈ xs
list-∈ {xs = List.[]} x∈ = absurd (∉ₛ[] x∈)
list-∈ {xs = x ∷ xs}  x∈ =
  [ here
  , there ∘ list-∈
  ]ᵤ (∈ₛ-∷→ x∈)

vec-∈ : ⦃ d : is-discrete A ⦄
      → {n : ℕ} {xs : Vec A n}
      → {z : A} → z ∈ₛ from-vec xs → z ∈ xs
vec-∈ {n = 0} {xs = Vec.[]} x∈ = absurd (∉ₛ[] x∈)
vec-∈ {n = suc n} {xs = x ∷ xs}  x∈ =
  [ hereᵥ
  , thereᵥ ∘ vec-∈ {xs = xs}
  ]ᵤ (∈ₛ-∷→ x∈)

-- TODO these should also work for non-discrete A
-- but P x under Reflects has to be Erased

opaque
  unfolding allₛ
  -- TODO factor out allₛ-×≃ : ((z : A) → z ∈ (x ∷ s) → P z) ≃ P x × ((z : A) → z ∈ s → P z)
  Reflects-allₛ : ⦃ d : is-discrete A ⦄
                → {s : LFSet A} {P : A → 𝒰 ℓ′} {p : A → Bool}
                → (∀ x → is-prop (P x))
                → (∀ x → Reflects (P x) (p x))
                → Reflects ((x : A) → x ∈ s → P x) (allₛ p s)
  Reflects-allₛ {A} {s} {P} {p} pp rp = elim-prop go s
    where
    go : Elim-prop λ q → Reflects ((x : A) → x ∈ q → P x) (allₛ p q)
    go .[]ʳ = ofʸ λ x → false! ⦃ Refl-x∉ₛ[] ⦄
    go .∷ʳ x {xs} ih =
      Reflects.dmap
        (λ where (px , ap) y →
                   [ (λ e → subst P (e ⁻¹) px) , ap y ]ᵤ ∘ ∈ₛ-∷→)
        (contra λ a → (a x (hereₛ refl)) , (λ y → a y ∘ thereₛ))
        (Reflects-× ⦃ rp = rp x ⦄ ⦃ rq = ih ⦄)
    go .truncʳ q =
      reflects-is-of-hlevel 0 $ Π-is-of-hlevel 1 (fun-is-of-hlevel 1 ∘ pp)

  Reflects-allₛ-bool : {A : 𝒰 ℓ} ⦃ d : is-discrete A ⦄
                     → {s : LFSet A} {p : A → Bool}
                     → Reflects ((x : A) → x ∈ s → So (p x)) (allₛ p s)
  Reflects-allₛ-bool = Reflects-allₛ (λ x → hlevel!) (λ x → Reflects-So)

  Dec-allₛ
    : ⦃ d : is-discrete A ⦄
    → {P : A → 𝒰 ℓ′} {s : LFSet A}
    → (∀ x → is-prop (P x))
    → (∀ x → Dec (P x))
    → Dec ((x : A) → x ∈ s → P x)
  Dec-allₛ {s} pp pd .does  = allₛ (λ x → pd x .does) s
  Dec-allₛ     pp pd .proof = Reflects-allₛ pp λ x → pd x .proof

opaque
  unfolding anyₛ
  -- TODO factor out any-⊎≃
  Reflects-anyₛ : {A : 𝒰 ℓ} ⦃ d : is-discrete A ⦄
                → {s : LFSet A} {P : A → 𝒰 ℓ′} {p : A → Bool}
                → (∀ x → Reflects (P x) (p x))
                → Reflects (∃[ x ꞉ A ] x ∈ s × P x) (anyₛ p s)
  Reflects-anyₛ {A} {s} {P} {p} rp = elim-prop go s
    where
    go : Elim-prop λ q → Reflects (∃[ x ꞉ A ] x ∈ q × P x) (anyₛ p q)
    go .[]ʳ = ofⁿ (rec! λ x x∈ _ → false! ⦃ Refl-x∉ₛ[] ⦄ x∈)
    go .∷ʳ x {xs} ih =
      Reflects.dmap
        [ (λ px → ∣ x , hereₛ refl , px ∣₁)
        , map (λ where (y , y∈ , py) → y , thereₛ y∈ , py) ]ᵤ
        (λ ¬x⊎xs → rec! λ y y∈ py → ¬x⊎xs (Sum.dmap (λ y=x → subst P y=x py)
                                                     (λ y∈′ → ∣ y , y∈′ , py ∣₁)
                                                     (∈ₛ-∷→ y∈)))
        (Reflects-⊎ ⦃ rp = rp x ⦄ ⦃ rq = ih ⦄)
    go .truncʳ q = hlevel!

  Reflects-anyₛ-bool : {A : 𝒰 ℓ} ⦃ d : is-discrete A ⦄
                     → {s : LFSet A} {p : A → Bool}
                     → Reflects (∃[ x ꞉ A ] x ∈ s × So (p x)) (anyₛ p s)
  Reflects-anyₛ-bool = Reflects-anyₛ λ x → Reflects-So

  Dec-anyₛ
    : {A : 𝒰 ℓ} ⦃ d : is-discrete A ⦄
    → {P : A → 𝒰 ℓ′} {s : LFSet A}
    → (∀ x → Dec (P x))
    → Dec (∃[ x ꞉ A ] x ∈ s × P x)
  Dec-anyₛ {s} pd .does  = anyₛ (λ x → pd x .does) s
  Dec-anyₛ     pd .proof = Reflects-anyₛ λ x → pd x .proof

Dec-⊆ₛ : ⦃ d : is-discrete A ⦄ {xs ys : LFSet A}
        → Dec (xs ⊆ ys)
Dec-⊆ₛ {xs} {ys} .does  = allₛ (_∈ₛ? ys) xs
Dec-⊆ₛ {xs} {ys} .proof =
  Reflects.dmap
    (λ f {x} → f x) (contra λ f x → f)
    (Reflects-allₛ hlevel! (λ x → Reflects-∈ₛ? {x = x} {xs = ys}) )

instance
  LFSet-is-discrete : ⦃ is-discrete A ⦄ → is-discrete (LFSet A)
  LFSet-is-discrete {x} {y} with Dec-⊆ₛ {xs = x} {ys = y}
  LFSet-is-discrete {x} {y} | yes x⊆y with Dec-⊆ₛ {xs = y} {ys = x}
  LFSet-is-discrete {x} {y} | yes x⊆y | yes y⊆x =
    yes $ set-ext λ z → prop-extₑ! x⊆y y⊆x
  LFSet-is-discrete {x} {y} | yes x⊆y | no ¬y⊆x =
    no (contra (λ e {z} → subst (z ∈_) (e ⁻¹)) ¬y⊆x)
  LFSet-is-discrete {x} {y} | no ¬x⊆y =
    no $ contra (λ e {z} → subst (z ∈_) e) ¬x⊆y

opaque
  unfolding filterₛ
  filter-=? : ⦃ d : is-discrete A ⦄ → {z : A} {s : LFSet A}
            → filterₛ (_=? z) s ＝ (if z ∈ₛ? s then z ∷ [] else [])
  filter-=? {z} {s} = elim-prop go s
    where
    go : Elim-prop λ q → filterₛ (_=? z) q ＝ (if z ∈ₛ? q then z ∷ [] else [])
    go .[]ʳ = refl
    go .∷ʳ x {xs} ih =
      the
       ((if x =? z then x ∷ filterₛ (_=? z) xs else filterₛ (_=? z) xs) ＝ (if (z =? x) or (z ∈ₛ? xs) then z ∷ [] else [])) $
       subst (λ q → (if x =? z then x ∷ (filterₛ (_=? z) xs) else filterₛ (_=? z) xs) ＝ (if q or z ∈ₛ? xs then z ∷ [] else []))
             (=?-sym {x = x}) $
      Dec.elim
        {C = λ q → (if ⌊ q ⌋ then x ∷ (filterₛ (_=? z) xs) else filterₛ (_=? z) xs) ＝ (if ⌊ q ⌋ or z ∈ₛ? xs then z ∷ [] else [])}
        (λ x=z →   ap (_∷ filterₛ (_=? z) xs) x=z
                 ∙ ap (z ∷_) ih
                 ∙ Bool.elim
                      {P = λ q → z ∷ (if q then z ∷ [] else []) ＝ z ∷ []}
                      drop
                      refl
                      (z ∈ₛ? xs))
        (λ _ → ih)
        (x ≟ z)
    go .truncʳ _ = hlevel!

  filter-sng : ⦃ d : is-discrete A ⦄ → {p : A → Bool} {z : A} {s : LFSet A}
             → ⌞ p z ⌟ → z ∈ s
             → (∀ {x} → x ∈ s → ⌞ p x ⌟ → x ＝ z)
             → filterₛ p s ＝ sng z
  filter-sng {p} {z} {s} pz z∈ x=z =
    set-ext λ x → prop-extₑ!
      (λ x∈f → let (px , x∈s) = filter-∈ₛ x∈f in
                hereₛ (x=z x∈s px))
      (λ x∈s → subst (_∈ₛ filterₛ p s) (∈ₛ∷-∉ x∈s ∉ₛ[] ⁻¹) $
                ∈-filterₛ pz z∈)

opaque
  unfolding filterₛ
  rem : ⦃ is-discrete A ⦄ → A → LFSet A → LFSet A
  rem x = filterₛ (not ∘ x =?_)

  rem-[] : ⦃ d : is-discrete A ⦄ → {x : A}
         → rem x [] ＝ []
  rem-[] = refl

  rem-⊆ : ⦃ d : is-discrete A ⦄ → {x : A} {s : LFSet A}
         → rem x s ⊆ s
  rem-⊆ = filter-⊆

  rem-∷ : ⦃ d : is-discrete A ⦄ → {x y : A} {s : LFSet A}
         → rem x (y ∷ s) ＝ (if x =? y then rem x s else y ∷ rem x s)
  rem-∷ {x} {y} = if-swap {b = x =? y} ⁻¹

  rem-∪∷ : ⦃ d : is-discrete A ⦄ → {x : A} {xs ys : LFSet A}
         → rem x (xs ∪∷ ys) ＝ rem x xs ∪∷ rem x ys
  rem-∪∷ {xs} = filter-∪∷ {xs = xs}

  -- TODO generalize to filter?
  rem-∉-eq : ⦃ d : is-discrete A ⦄ {s : LFSet A} {z : A}
         → z ∉ s → rem z s ＝ s
  rem-∉-eq {s} {z} = elim-prop go s
    where
    go : Elim-prop λ q → z ∉ q → rem z q ＝ q
    go .[]ʳ _ = refl
    go .∷ʳ x {xs} ih z∉∷ =
      let (z≠x , z∉) = ∉ₛ-uncons {xs = xs} z∉∷ in
      given-no z≠x
         return (λ q → (if (not ⌊ q ⌋) then x ∷ rem z xs else rem z xs) ＝ x ∷ xs)
         then ap (x ∷_) (ih z∉)
    go .truncʳ x = hlevel!

  rem-∈-eq : ⦃ d : is-discrete A ⦄ {x : A} {s : LFSet A}
           → x ∈ s → x ∷ rem x s ＝ s
  rem-∈-eq {x} {s} x∈ =
      ap (_∪∷ rem x s)
         (  if-true (true→so! x∈) ⁻¹
          ∙ filter-=? {z = x} {s = s} ⁻¹
          ∙ ap (λ q → filterₛ q s) (fun-ext (λ q → =?-sym {x = q})))
    ∙ filter-compl {p = x =?_}

  ∷-rem : ⦃ d : is-discrete A ⦄ {x : A} {s : LFSet A}
         → x ∷ s ＝ x ∷ rem x s
  ∷-rem {x} {s} with x ∈? s
  ... | yes x∈ = ∈ₛ-∷= x∈ ∙ rem-∈-eq x∈ ⁻¹
  ... | no x∉ = ap (x ∷_) (rem-∉-eq x∉ ⁻¹)

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
  rem-∈-≠ z≠x = ∈-filterₛ (false→so! (z≠x ∘ _⁻¹))

  ⊆-rem : ⦃ d : is-discrete A ⦄ → {z : A} {s : LFSet A}
        → s ⊆ (the (LFSet A) (z ∷ rem z s))
  ⊆-rem {z} {x} x∈ with x ≟ z
  ... | yes x=z = hereₛ x=z
  ... | no x≠z = thereₛ (rem-∈-≠ x≠z x∈)

  rem-idem : ⦃ d : is-discrete A ⦄ → {x : A} {s : LFSet A}
            → rem x (rem x s) ＝ rem x s
  rem-idem {s} = filter-idem {s = s}

record Elim-rem-prop {A : 𝒰 ℓ} ⦃ d : is-discrete A ⦄ (P : LFSet A → 𝒰 ℓ′) : 𝒰 (ℓ ⊔ ℓ′) where
  no-eta-equality
  field
    []rʳ    : P []
    ∷rʳ     : ∀ x {xs} → x ∈ xs → P (rem x xs) → P xs
    truncrʳ : ∀ x → is-prop (P x)

elim-rem-prop : ⦃ d : is-discrete A ⦄ {P : LFSet A → 𝒰 ℓ′} → Elim-rem-prop P → (x : LFSet A) → P x
elim-rem-prop ⦃ d ⦄ {P} e = elim-prop e′
  where
  module E = Elim-rem-prop e

  e′ : Elim-prop P
  e′ .[]ʳ = E.[]rʳ
  e′ .∷ʳ x {xs} ih =
    Dec.rec
       (λ x∈xs → subst P (∈ₛ-∷= x∈xs ⁻¹) ih)
       (λ x∉xs → E.∷rʳ x (hereₛ refl)
                    (subst P (  rem-∉-eq x∉xs ⁻¹
                              ∙ if-true (true→so! ⦃ d .Dec.proof ⦄ refl) ⁻¹
                              ∙ rem-∷ ⁻¹) ih))
       (x ∈? xs)
  e′ .truncʳ x = E.truncrʳ x

open Elim-rem-prop public

-- difference and intersection

opaque
  unfolding rem
  -- TODO rename _\∷_ ?
  minus : ⦃ is-discrete A ⦄ → LFSet A → LFSet A → LFSet A
  minus xs ys = filterₛ (λ x → not (x ∈ₛ? ys)) xs

  minus-[]-l : ⦃ d : is-discrete A ⦄ → {s : LFSet A} → minus [] s ＝ []
  minus-[]-l = refl

  minus-∷-l : ⦃ d : is-discrete A ⦄ {x : A} {s r : LFSet A}
            → minus (x ∷ s) r ＝ (if not (x ∈ₛ? r) then x ∷ minus s r else minus s r)
  minus-∷-l = refl

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

  minus-∈ : ⦃ d : is-discrete A ⦄ {z : A} {xs ys : LFSet A}
          → z ∈ minus xs ys
          → z ∈ xs × z ∉ ys
  minus-∈ {xs} z∈m =
    let (pz , z∈) = filter-∈ₛ {s = xs} z∈m in
    z∈ , so→false! pz

  minus-⊆ : ⦃ d : is-discrete A ⦄ {xs ys : LFSet A}
           → minus xs ys ⊆ xs
  minus-⊆ = filter-⊆

  ∈-minus : ⦃ d : is-discrete A ⦄ {z : A} {xs ys : LFSet A}
           → z ∈ xs
           → z ∉ ys
           → z ∈ minus xs ys
  ∈-minus z∈xs z∉ys = ∈-filterₛ (false→so! z∉ys) z∈xs

  minus-minus : ⦃ d : is-discrete A ⦄ {v s₁ s₂ : LFSet A}
              → minus (minus v s₁) s₂ ＝ minus v (s₁ ∪∷ s₂)
  minus-minus {v} {s₁} {s₂} =
      filter-and {s = v} ⁻¹
    ∙ ap (λ q → filterₛ q v)
         (fun-ext λ z →   not-or (z ∈ₛ? s₂) (z ∈ₛ? s₁) ⁻¹
                        ∙ ap not (  or-comm (z ∈ₛ? s₂) (z ∈ₛ? s₁)
                                  ∙ ∈ₛ?-∪∷ {s₁ = s₁} ⁻¹))

opaque
  unfolding filterₛ
  _∩∷_ : ⦃ is-discrete A ⦄ → LFSet A → LFSet A → LFSet A
  xs ∩∷ ys = filterₛ (_∈ₛ? ys) xs

  ∩∷-∈ : ⦃ d : is-discrete A ⦄ → {s t : LFSet A} {x : A}
        → x ∈ (s ∩∷ t) → x ∈ s × x ∈ t
  ∩∷-∈ x∈∩ =
    let (x∈?t , x∈s) = filter-∈ₛ x∈∩ in
    x∈s , so→true! x∈?t

  ∈-∩∷← : ⦃ d : is-discrete A ⦄ → {s t : LFSet A} {x : A}
        → x ∈ s → x ∈ t → x ∈ (s ∩∷ t)
  ∈-∩∷← x∈s x∈t = ∈-filterₛ (true→so! x∈t) x∈s

  ∩∷-zero-l : ⦃ d : is-discrete A ⦄ → {xs : LFSet A} → [] ∩∷ xs ＝ []
  ∩∷-zero-l = refl

  ∩∷-zero-r : ⦃ d : is-discrete A ⦄ → {xs : LFSet A} → xs ∩∷ [] ＝ []
  ∩∷-zero-r {xs} = filter-none {s = xs} λ _ → oh

  ∩∷-∷-l : ⦃ d : is-discrete A ⦄ → {x : A} {xs ys : LFSet A}
         → (x ∷ xs) ∩∷ ys ＝ (if x ∈ₛ? ys then x ∷ (xs ∩∷ ys) else xs ∩∷ ys)
  ∩∷-∷-l = refl

  ∩∷-idem : ⦃ d : is-discrete A ⦄ → {xs : LFSet A} → xs ∩∷ xs ＝ xs
  ∩∷-idem {xs} = filter-all {s = xs} true→so!

  -- TODO there should be a more general theory of filtering over membership?
  ∩∷-comm : ⦃ d : is-discrete A ⦄ → {xs ys : LFSet A} → xs ∩∷ ys ＝ ys ∩∷ xs
  ∩∷-comm ⦃ d ⦄ {xs} {ys} = elim-prop go xs
    where
    go : Elim-prop λ q → filterₛ (_∈ₛ? ys) q ＝ filterₛ (_∈ₛ? q) ys
    go .[]ʳ = ∩∷-zero-r {xs = ys} ⁻¹
    go .∷ʳ x {xs} ih =
        Dec.elim
           {C = λ q → (if ⌊ q ⌋ then x ∷ filterₛ (_∈ₛ? ys) xs else filterₛ (_∈ₛ? ys) xs) ＝
                      (if ⌊ q ⌋ then x ∷ [] else []) ∪∷ filterₛ (λ q → not (q =? x)) (filterₛ (_∈ₛ? xs) ys)}
           (λ x∈ →   ap (x ∷_) (ih ∙ filter-compl {s = filterₛ (_∈ₛ? xs) ys} {p = _=? x} ⁻¹)
                    ∙ ap (_∪∷ filterₛ (not ∘ (_=? x)) (filterₛ (_∈ₛ? xs) ys))
                         (ap (x ∷_) (filter-=? {z = x} {s = filterₛ (_∈ₛ? xs) ys})
                          ∙ Bool.elim
                              {P = λ q → x ∷ (if q then x ∷ [] else []) ＝ x ∷ []}
                              drop
                              refl
                              (x ∈ₛ? filterₛ (_∈ₛ? xs) ys)))
           (λ x∉ → ih ∙ filter-all (λ {x = z} z∈ → not-so (contra (λ s → subst (_∈ₛ ys) (so→true! s) (filter-∈ₛ z∈ .snd)) x∉)) ⁻¹)
           (x ∈? ys)
      ∙ ap (_∪∷ filterₛ (λ q → not (q =? x)) (filterₛ (_∈ₛ? xs) ys)) (filter-=? {z = x} {s = ys} ⁻¹)
      ∙ ap (filterₛ (_=? x) ys ∪∷_) (filter-and {s = ys} {p = λ q → not (q =? x)} {q = _∈ₛ? xs} ⁻¹)
      ∙ filter-or {s = ys} {p = _=? x} {q = _∈ₛ? xs} ⁻¹
    go .truncʳ _ = hlevel!

  ∈-∩∷→l : ⦃ d : is-discrete A ⦄ {s t : LFSet A} {x : A}
         → x ∈ (s ∩∷ t) → x ∈ s
  ∈-∩∷→l {s} {t} x∈∩ = filter-∈ₛ {p = _∈ₛ? t} {s = s} x∈∩ .snd

  ∈-∩∷→r : ⦃ d : is-discrete A ⦄ {s t : LFSet A} {x : A}
         → x ∈ (s ∩∷ t) → x ∈ t
  ∈-∩∷→r {s} {t} {x} x∈∩ = ∈-∩∷→l {t = s} (subst (x ∈ₛ_) (∩∷-comm {xs = s} {ys = t}) x∈∩)

  filter-∩∷ : ⦃ d : is-discrete A ⦄ → ∀ {xs ys} {p : A → Bool}
             → filterₛ p (xs ∩∷ ys) ＝ filterₛ p xs ∩∷ filterₛ p ys
  filter-∩∷ {xs} {ys} {p} =
      filter-and {s = xs} ⁻¹
    ∙ ap (λ q → filterₛ q xs)
         (fun-ext λ z →
              ap (_and (z ∈ₛ? ys)) (and-idem (p z) ⁻¹)
            ∙ and-assoc (p z) (p z) (z ∈ₛ? ys)
            ∙ ap (p z and_) (∈ₛ?-filter {s = ys} ⁻¹)
            ∙ and-comm (p z) (z ∈ₛ? filterₛ p ys))
    ∙ filter-and {s = xs}

  Reflects-∩∷-disjoint : ⦃ d : is-discrete A ⦄
                       → {s t : LFSet A}
                       → Reflects (s ∥ₛ t) (empty? $ s ∩∷ t)
  Reflects-∩∷-disjoint ⦃ d ⦄ {s} {t} = elim-prop go s
    where
    go : Elim-prop λ q → Reflects (q ∥ₛ t) (empty? $ q ∩∷ t)
    go .[]ʳ          = ofʸ λ {x} → false! ⦃ Refl-x∉ₛ[] ⦄ -- why
    go .∷ʳ x {xs} ih =
      Dec.elim
        {C = λ q → Reflects ((x ∷ xs) ∥ₛ t) (empty? $ if ⌊ q ⌋ then x ∷ filterₛ (_∈ₛ? t) xs else filterₛ (_∈ₛ? t) xs) }
        (λ x∈ → ofⁿ λ d → d (hereₛ refl) x∈)
        (λ x∉ → Reflects.dmap (∥ₛ-∷-l→ x∉)
                              (contra (snd ∘ ∥ₛ-∷-l←))
                              ih)
        (x ∈? t)
    go .truncʳ q     = reflects-is-of-hlevel 0 $ hlevel 1

Dec-disjoint : ⦃ d : is-discrete A ⦄
             → {s t : LFSet A}
             → Dec (s ∥ₛ t)
Dec-disjoint {s} {t} .does  = empty? $ s ∩∷ t
Dec-disjoint         .proof = Reflects-∩∷-disjoint

opaque
  unfolding rem
  rem-∩∷ : ⦃ d : is-discrete A ⦄ → {x : A} {xs ys : LFSet A}
         → rem x (xs ∩∷ ys) ＝ rem x xs ∩∷ rem x ys
  rem-∩∷ = filter-∩∷

opaque
  unfolding _∩∷_ minus
  ∩∷-minus-compl : ⦃ d : is-discrete A ⦄ → {xs ys : LFSet A}
                 → (xs ∩∷ ys) ∪∷ minus xs ys ＝ xs
  ∩∷-minus-compl = filter-compl

  ∩∷-minus-∥ₛ : ⦃ d : is-discrete A ⦄ → {xs ys : LFSet A}
               → (xs ∩∷ ys) ∥ₛ minus xs ys
  ∩∷-minus-∥ₛ {xs} {ys} x∈∩ x∈m = minus-∈ {xs = xs} {ys = ys} x∈m .snd (∈-∩∷→r {s = xs} x∈∩)

∉-∩∷ : ⦃ d : is-discrete A ⦄ → {s t : LFSet A} {x : A}
      → x ∉ (s ∩∷ t) → (x ∉ s × x ∈ t) ⊎ (x ∈ s × x ∉ t) ⊎ (x ∉ s × x ∉ t)
∉-∩∷ {s} {t} {x} x∉∩ with x ∈? s
∉-∩∷ {s} {t} {x} x∉∩ | yes x∈s with x ∈? t
∉-∩∷ {s} {t} {x} x∉∩ | yes x∈s | yes x∈t = absurd (x∉∩ (∈-∩∷← x∈s x∈t))
∉-∩∷ {s} {t} {x} x∉∩ | yes x∈s | no x∉t  = inr $ inl (x∈s , x∉t)
∉-∩∷ {s} {t} {x} x∉∩ | no x∉s  with x ∈? t
∉-∩∷ {s} {t} {x} x∉∩ | no x∉s | yes x∈t = inl (x∉s , x∈t)
∉-∩∷ {s} {t} {x} x∉∩ | no x∉s | no x∉t  = inr $ inr (x∉s , x∉t)

∩∷-∉-l : ⦃ d : is-discrete A ⦄ → {s t : LFSet A} {x : A}
       → x ∉ s → x ∉ (s ∩∷ t)
∩∷-∉-l = contra ∈-∩∷→l

∩∷-∉-r : ⦃ d : is-discrete A ⦄ → {s t : LFSet A} {x : A}
       → x ∉ t → x ∉ (s ∩∷ t)
∩∷-∉-r = contra ∈-∩∷→r

-- nub

nub-accₛ : ⦃ d : is-discrete A ⦄
          → LFSet A → LFSet A → LFSet A
nub-accₛ {A} ⦃ d ⦄ = rec go
  where
  go : Rec A (LFSet A → LFSet A)
  go .[]ʳ _ = []
  go .∷ʳ h _ rec a = if h ∈ₛ? a then rec a else h ∷ rec (h ∷ a)
  go .dropʳ x _ rec =
    fun-ext λ a →
      Dec.elim
        {C = λ q → (if ⌊ q ⌋ then if ⌊ q ⌋ then rec a else x ∷ rec (x ∷ a) else x ∷ (if x ∈ₛ? (x ∷ a) then rec (x ∷ a) else x ∷ rec (x ∷ x ∷ a)))
                 ＝ (if ⌊ q ⌋ then rec a else x ∷ rec (x ∷ a))}
        (λ x∈a → refl)
        (λ x∉a → ap (x ∷_) $ if-true (true→so! {P = x ∈ (x ∷ a)} (hereₛ refl)))
        (x ∈? a)
  go .swapʳ x y _ rec =
    fun-ext λ a →
      Dec.elim
        {C = λ q → (if ⌊ q ⌋ then if y ∈ₛ? a then rec a else y ∷ rec (y ∷ a) else x ∷ (if y ∈ₛ? (x ∷ a) then rec (x ∷ a) else y ∷ rec (y ∷ x ∷ a)))
                 ＝ (if y ∈ₛ? a then if ⌊ q ⌋ then rec a else x ∷ rec (x ∷ a) else y ∷ (if x ∈ₛ? (y ∷ a) then rec (y ∷ a) else x ∷ rec (x ∷ y ∷ a)))}
        (λ x∈a →
           Dec.elim
             {C = λ q → (if ⌊ q ⌋ then rec a else y ∷ rec (y ∷ a))
                     ＝ (if ⌊ q ⌋ then rec a else y ∷ (if x ∈ₛ? (y ∷ a) then rec (y ∷ a) else x ∷ rec (x ∷ y ∷ a)))}
             (λ y∈a → refl)
             (λ y∉a → ap (y ∷_) $ if-true (true→so! (thereₛ x∈a)) ⁻¹)
             (y ∈? a)
        )
        (λ x∉a →
            Dec.elim
             {P = y ∈ a}  -- why
             {C = λ q → (x ∷ (if y ∈ₛ? (x ∷ a) then rec (x ∷ a) else y ∷ rec (y ∷ x ∷ a)))
                     ＝ (if ⌊ q ⌋ then x ∷ rec (x ∷ a) else y ∷ (if x ∈ₛ? (y ∷ a) then rec (y ∷ a) else x ∷ rec (x ∷ y ∷ a)))}
             (λ y∈a → ap (x ∷_) $ if-true (true→so! (thereₛ y∈a)))
             (λ y∉a →
                Dec.elim
                  {C = λ q → (x ∷ (if y =? x or y ∈ₛ? a then rec (x ∷ a) else y ∷ rec (y ∷ x ∷ a)))
                          ＝ (y ∷ (if ⌊ q ⌋ or x ∈ₛ? a then rec (y ∷ a) else x ∷ rec (x ∷ y ∷ a)))}
                  (λ x=y → ap² {C = λ _ _ → LFSet A}
                               _∷_ x=y (  if-true (or-so-l (true→so! (x=y ⁻¹)))
                                        ∙ ap (λ q → rec (q ∷ a)) x=y))
                  (λ x≠y →   ap (x ∷_) (if-false (subst So (not-or (y =? x) (y ∈ₛ? a) ⁻¹) $
                                                  and-so-intro (false→so! (x≠y ∘ _⁻¹)) (false→so! y∉a)))
                            ∙ swap
                            ∙ ap {B = λ _ → LFSet A}
                                 (λ q → y ∷ x ∷ rec q) swap
                            ∙ ap (y ∷_) (if-false (false→so! x∉a) ⁻¹))
                  (x ≟ y)
             )
             (y ∈? a)
        )
        (x ∈? a)
  go .truncʳ = hlevel 2

nubₛ : ⦃ d : is-discrete A ⦄
     → LFSet A → LFSet A
nubₛ xs = nub-accₛ xs []

nub-accₛ-⊆-minus : ⦃ d : is-discrete A ⦄
                 → (xs : LFSet A) (a : LFSet A)
                 → nub-accₛ xs a ⊆ minus xs a
nub-accₛ-⊆-minus {A} ⦃ d ⦄ = elim-prop go
  where
  go : Elim-prop λ q → (a : LFSet A) → nub-accₛ q a ⊆ minus q a
  go .[]ʳ a = false! ⦃ Refl-x∉ₛ[] ⦄
  go .∷ʳ x {xs} ih a {x = z} =
    Dec.elim
      {C = λ q → z ∈ₛ (if ⌊ q ⌋ then nub-accₛ xs a else x ∷ nub-accₛ xs (x ∷ a)) → z ∈ₛ minus (x ∷ xs) a}
      (λ x∈a →   subst (z ∈ₛ_)
                       (  if-false (subst So (not-invol (x ∈ₛ? a) ⁻¹) (true→so! x∈a)) ⁻¹
                        ∙ minus-∷-l ⁻¹)
               ∘ ih a)
      (λ x∉a → subst (z ∈ₛ_)
                       (  if-true (false→so! x∉a) ⁻¹
                        ∙ minus-∷-l ⁻¹) ∘
               [ hereₛ
               ,   thereₛ
                 ∘ rem-⊆
                 ∘ subst (z ∈ₛ_) minus-∷-r
                 ∘ ih (x ∷ a)
               ]ᵤ ∘ ∈ₛ-∷→)
      (x ∈? a)
  go .truncʳ x = hlevel!

nub-accₛ-⊇-minus : ⦃ d : is-discrete A ⦄
                 → (xs : LFSet A) (a : LFSet A)
                 → minus xs a ⊆ nub-accₛ xs a
nub-accₛ-⊇-minus {A} ⦃ d ⦄ = elim-prop go
  where
  go : Elim-prop λ q → (a : LFSet A) → minus q a ⊆ nub-accₛ q a
  go .[]ʳ a {x = z} = subst (z ∈_) minus-[]-l
  go .∷ʳ x {xs} ih a {x = z} =
        Dec.elim
      {C = λ q → z ∈ₛ minus (x ∷ xs) a → z ∈ₛ (if ⌊ q ⌋ then nub-accₛ xs a else x ∷ nub-accₛ xs (x ∷ a)) }
      (λ x∈a →   ih a
               ∘ subst (z ∈ₛ_)
                       (  minus-∷-l
                         ∙ if-false (subst So (not-invol (x ∈ₛ? a) ⁻¹) (true→so! x∈a))))
      (λ x∉a →   [ hereₛ
                 ,   thereₛ
                   ∘ ih (x ∷ a)
                   ∘ subst (z ∈_) (minus-∷-r ⁻¹)
                 ]ᵤ
               ∘ ∈ₛ-∷→
               ∘ subst (z ∈ₛ_)
                       (  minus-∷-l
                        ∙ if-true (false→so! x∉a)
                        ∙ ∷-rem))
      (x ∈? a)
  go .truncʳ x = hlevel!

nub-accₛ-=-minus : ⦃ d : is-discrete A ⦄
                 → (xs : LFSet A) (a : LFSet A)
                 → nub-accₛ xs a ＝ minus xs a
nub-accₛ-=-minus xs a =
  set-ext λ z → prop-extₑ! (nub-accₛ-⊆-minus xs a) (nub-accₛ-⊇-minus xs a)

nubₛ-= : ⦃ d : is-discrete A ⦄
       → (xs : LFSet A)
       → nubₛ xs ＝ xs
nubₛ-= xs = nub-accₛ-=-minus xs [] ∙ minus-[]-r

-- size

calc : ⦃ d : is-discrete A ⦄ → A → LFSet A → ℕ
calc x xs = bit (not (x ∈ₛ? xs))

calc-∪∷ : ⦃ d : is-discrete A ⦄ {x : A} {xs ys : LFSet A}
        → calc x (xs ∪∷ ys) ＝ calc x xs · calc x ys
calc-∪∷ {x} {xs} {ys} =
    ap (bit ∘ not) (∈ₛ?-∪∷ {s₁ = xs})
  ∙ ap bit (not-or (x ∈ₛ? xs) (x ∈ₛ? ys))
  ∙ bit-and (not (x ∈ₛ? xs)) (not (x ∈ₛ? ys))

calc-filter= : ⦃ d : is-discrete A ⦄ {p : A → Bool} {x : A} {xs : LFSet A}
             → ⌞ p x ⌟ → calc x (filterₛ p xs) ＝ calc x xs
calc-filter= {p} {x} {xs} px with Dec-∈ₛ {a = x} {xs = filterₛ p xs}
... | yes x∈f =
  ap (bit ∘ not) (  (true→is-true x∈f)
                 ∙ (true→is-true $ filter-⊆ x∈f) ⁻¹)
... | no x∉f =
  ap (bit ∘ not) (  (false→is-false x∉f)
                  ∙ (false→is-false (contra (∈-filterₛ px) x∉f)) ⁻¹)

calc-rem : ⦃ d : is-discrete A ⦄ {x : A} {xs : LFSet A}
         → calc x (rem x xs) ＝ 1
calc-rem = ap (bit ∘ not) (false→is-false (∉-rem (inl refl)))

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
                     ⦃ A-pr = hlevel-instance (is-discrete→is-set d y x) ⦄  -- TODO
                     (x=y ⁻¹)
                     (λ q → calc y xs + n ＝ bit (not (⌊ q ⌋ or y ∈ₛ? xs)) + (calc x xs + n))
                     (ap (λ q → calc q xs + n) (x=y ⁻¹)))
        (λ x≠y → given-no x≠y ∘ _⁻¹
                    return (λ q → calc x xs + (calc y xs + n) ＝ bit (not (⌊ q ⌋ or y ∈ₛ? xs)) + (calc x xs + n))
                    then +-comm-assoc (calc x xs) (calc y xs) n)
        (x ≟ y)
    go .truncʳ = hlevel!

  size-[] : ⦃ d : is-discrete A ⦄ → sizeₛ {A = A} [] ＝ 0
  size-[] = refl

  size0 : ⦃ d : is-discrete A ⦄ → {s : LFSet A} → sizeₛ s ＝ 0 → s ＝ []
  size0 {A} {s} = elim-prop go s
    where
    go : Elim-prop λ q → sizeₛ {A = A} q ＝ 0 → q ＝ []
    go .[]ʳ _ = refl
    go .∷ʳ x {xs} ih =
       Dec.elim
          {C = λ q → bit (not (⌊ q ⌋)) + sizeₛ {A = A} xs ＝ 0 → x ∷ xs ＝ []}
          (λ x∈ e → false! ⦃ Refl-x∉ₛ[] ⦄ (subst (x ∈_) (ih e) x∈))
          (λ x∉ → false!)
          (x ∈? xs)
    go .truncʳ = hlevel!

  size-∷ : ⦃ d : is-discrete A ⦄ → {x : A} {s : LFSet A} → sizeₛ (x ∷ s) ＝ suc (sizeₛ (rem x s))
  size-∷ {x} {s} =
      ap sizeₛ (∷-rem {x = x} {s = s})
    ∙ ap (λ q → bit (not q) + sizeₛ (rem x s))
         (¬so≃is-false $ so-not (false→so! (∉-rem (inl refl))))

  size-sng : ⦃ d : is-discrete A ⦄ → {x : A} → sizeₛ (sng x) ＝ 1
  size-sng {x} = size-∷ {x = x} {s = []} ∙ ap (suc ∘ sizeₛ) rem-[]

  size-∪∷ : ⦃ d : is-discrete A ⦄ → {xs ys : LFSet A}
          → sizeₛ xs ≤ sizeₛ (xs ∪∷ ys)
  size-∪∷ {A} {xs} {ys} = elim-prop go xs ys
    where
    go : Elim-prop λ q → (ys : LFSet A) → sizeₛ q ≤ sizeₛ (q ∪∷ ys)
    go .[]ʳ _ = z≤
    go .∷ʳ x {xs} ih ys =
      ≤-trans
         (≤-+ (=→≤ (  ·-id-r (calc x xs) ⁻¹
                    ∙ ap (calc x xs ·_) (calc-rem ⁻¹)
                    ∙ calc-∪∷ {xs = xs} ⁻¹))
              (ih (rem x ys)))
         (=→≤ (ap sizeₛ (  ap (x ∷_) (∪∷-comm {x = xs} {y = rem x ys})
                         ∙ ap (_∪∷ xs) ∷-rem ⁻¹
                         ∙ ap (x ∷_) (∪∷-comm {x = ys} {y = xs}))))
    go .truncʳ _ = hlevel!

  size-∪∷-⊆ : ⦃ d : is-discrete A ⦄ → {xs ys : LFSet A}
             → sizeₛ (xs ∪∷ ys) ＝ sizeₛ xs
             → ys ⊆ xs
  size-∪∷-⊆ {A} {xs} {ys} = elim-prop go ys xs
    where
    go : Elim-prop λ q → (xs : LFSet A) → sizeₛ (xs ∪∷ q) ＝ sizeₛ xs → q ⊆ xs
    go .[]ʳ _ _ = false! ⦃ Refl-x∉ₛ[] ⦄
    go .∷ʳ y {xs = ys} ih xs e x∈∷ with y ∈? xs
    ... | yes y∈xs =
            [ (λ x=y  → subst (_∈ₛ xs) (x=y ⁻¹) y∈xs)
            , (ih xs (ap sizeₛ (ap (_∪∷ ys) (∈ₛ-∷= y∈xs ⁻¹) ∙ ∪∷-swap {s = xs}) ∙ e))
            ]ᵤ (∈ₛ-∷→ x∈∷)
    ... | no  y∉xs =
             absurd ((≤≃≯ $ size-∪∷ {xs = xs})
                          (<≃suc≤ $ =→≤ $   ap (λ q → suc $ sizeₛ (q ∪∷ rem y ys)) (rem-∉-eq y∉xs ⁻¹)
                                          ∙ ap (suc ∘ sizeₛ) (rem-∪∷ {xs = xs} ⁻¹)
                                          ∙ size-∷ {s = xs ∪∷ ys} ⁻¹
                                          ∙ ap sizeₛ (∪∷-swap {s = xs})
                                          ∙ e))
    go .truncʳ _ = hlevel!

  size-⊆ : ⦃ d : is-discrete A ⦄ → {xs ys : LFSet A}
         → xs ⊆ ys → sizeₛ xs ≤ sizeₛ ys
  size-⊆ {xs} xs⊆ys = subst (λ q → sizeₛ xs ≤ sizeₛ q) (⊆-∪= xs⊆ys) (size-∪∷ {xs = xs})

  -- TODO can we drop truncation?
  size>0-∈ : ⦃ d : is-discrete A ⦄ → {s : LFSet A} → 0 < sizeₛ s → ∃[ x ꞉ A ] x ∈ s
  size>0-∈ {A} {s} = elim-prop go s
    where
    go : Elim-prop λ q → 0 < sizeₛ {A = A} q → ∃[ x ꞉ A ] x ∈ q
    go .[]ʳ = false!
    go .∷ʳ x _ _ = ∣ x , hereₛ refl ∣₁
    go .truncʳ _ = hlevel!

  size-∈->0 : ⦃ d : is-discrete A ⦄ → {s : LFSet A} {z : A} → z ∈ s → 0 < sizeₛ s
  size-∈->0 {A} {s} {z} = elim-prop go s
    where
    go : Elim-prop λ q → z ∈ q → 0 < sizeₛ {A = A} q
    go .[]ʳ = false! ⦃ Refl-x∉ₛ[] ⦄
    go .∷ʳ x {xs} _ _ =
      subst (0 <_) (size-∷ {x = x} {s = xs} ⁻¹) z<s
    go .truncʳ _ = hlevel!

  size-unique : ⦃ d : is-discrete A ⦄ → {s : List A} → Uniq s → sizeₛ (from-list s) ＝ length s
  size-unique []ᵘ       = refl
  size-unique (x∉ ∷ᵘ u) =
    ap² _+_
      (ap (bit ∘ not) (¬so≃is-false $ so-not (false→so! (∉-list x∉))))
      (size-unique u)

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
  rem-size-∈ : ⦃ d : is-discrete A ⦄ {s : LFSet A} {z : A}
               → z ∈ s → sizeₛ s ＝ suc (sizeₛ (rem z s))
  rem-size-∈ {s} z∈s =
      ap sizeₛ (rem-∈-eq z∈s ⁻¹)
    ∙ size-∷
    ∙ ap (suc ∘ sizeₛ) (filter-idem {s = s})

opaque
  unfolding _∩∷_
  size-∩∷ : ⦃ d : is-discrete A ⦄ → {xs ys : LFSet A}
          → sizeₛ (xs ∩∷ ys) ≤ sizeₛ xs
  size-∩∷ = filter-size≤

  size-∩∷-⊆ : ⦃ d : is-discrete A ⦄ → {xs ys : LFSet A}
             → sizeₛ (xs ∩∷ ys) ＝ sizeₛ xs
             → xs ⊆ ys
  size-∩∷-⊆ e = so→true! ∘ all←filter-size= e

  size-∪∷-∩∷ : ⦃ d : is-discrete A ⦄ → {xs ys : LFSet A}
            → sizeₛ (xs ∪∷ ys) + sizeₛ (xs ∩∷ ys) ＝ sizeₛ xs + sizeₛ ys
  size-∪∷-∩∷ {A} {xs} {ys} = elim-rem-prop go xs ys
    where
    go : Elim-rem-prop λ q → (ys : LFSet A) → sizeₛ (q ∪∷ ys) + sizeₛ (q ∩∷ ys) ＝ sizeₛ q + sizeₛ ys
    go .[]rʳ ys = +-comm (sizeₛ ys) (sizeₛ [])
    go .∷rʳ x {xs} x∈ ih ys =
        ap (λ q → sizeₛ (q ∪∷ ys) + sizeₛ (q ∩∷ ys)) (rem-∈-eq x∈ ⁻¹)
      ∙ ap (_+ sizeₛ ((x ∷ rem x xs) ∩∷ ys)) size-∷
      ∙ ap suc
           (  ap (λ q → sizeₛ q + sizeₛ ((x ∷ rem x xs) ∩∷ ys))
                 (rem-∪∷ {xs = rem x xs})
            ∙ ap (λ q → sizeₛ (q ∪∷ rem x ys) + sizeₛ ((x ∷ rem x xs) ∩∷ ys))
                 (rem-idem {s = xs})
            ∙ ap (λ q → sizeₛ (rem x xs ∪∷ rem x ys) + sizeₛ q)
                 (∩∷-∷-l {xs = rem x xs} {ys = ys})
            ∙ Dec.elim
               {C = λ q → sizeₛ (rem x xs ∪∷ rem x ys)
                        + sizeₛ (if ⌊ q ⌋ then x ∷ (rem x xs ∩∷ ys) else (rem x xs ∩∷ ys))
                        ＝ sizeₛ (rem x xs) + sizeₛ ys}
               (λ x∈ys →   ap (sizeₛ (rem x xs ∪∷ rem x ys) +_) size-∷
                         ∙ ap (λ q → sizeₛ (rem x xs ∪∷ rem x ys) + suc (sizeₛ q))
                              (rem-∩∷ {xs = rem x xs} {ys = ys})
                         ∙ ap (λ q → sizeₛ (rem x xs ∪∷ rem x ys) + suc (sizeₛ (q ∩∷ rem x ys)))
                              (rem-idem {s = xs})
                         ∙ +-suc-r _ _
                         ∙ ap suc (  ih (rem x ys)
                                   ∙ ap (λ q → sizeₛ (rem x xs) + sizeₛ q)
                                        (rem-idem ⁻¹))
                         ∙ +-suc-r _ _ ⁻¹
                         ∙ ap (sizeₛ (rem x xs) +_) (size-∷ ⁻¹)
                         ∙ ap (λ q → sizeₛ (rem x xs) + sizeₛ q)
                              (rem-∈-eq x∈ys))
               (λ x∉ys →   ap (λ q → sizeₛ (rem x xs ∪∷ rem x ys) + sizeₛ (rem x xs ∩∷ q))
                              (rem-∉-eq x∉ys ⁻¹)
                         ∙ ih (rem x ys)
                         ∙ ap (λ q → sizeₛ (rem x xs) + sizeₛ q)
                              (rem-∉-eq x∉ys))
               (x ∈? ys)
            ∙ ap (λ q → sizeₛ q + sizeₛ ys) (rem-idem {s = xs} ⁻¹))
      ∙ ap (_+ sizeₛ ys) (size-∷ ⁻¹)
      ∙ ap (λ q → sizeₛ q + sizeₛ ys) (rem-∈-eq x∈)
    go .truncrʳ _ = hlevel!

  size-∪∷-∥ₛ : ⦃ d : is-discrete A ⦄ → {xs ys : LFSet A}
             → xs ∥ₛ ys
             → sizeₛ (xs ∪∷ ys) ＝ sizeₛ xs + sizeₛ ys
  size-∪∷-∥ₛ {xs} {ys} xdy =
      +-zero-r _ ⁻¹
    ∙ ap (sizeₛ (xs ∪∷ ys) +_)
         ((  ap sizeₛ (so→true! ⦃ Reflects-empty? ⦄ $ true→so! ⦃ Reflects-∩∷-disjoint ⦄ xdy)
           ∙ size-[]) ⁻¹)
    ∙ size-∪∷-∩∷

  size-minus-∩∷ : ⦃ d : is-discrete A ⦄ → {xs ys : LFSet A}
                → sizeₛ (minus xs ys) + sizeₛ (xs ∩∷ ys) ＝ sizeₛ xs
  size-minus-∩∷ {xs} {ys} =
      +-comm (sizeₛ (minus xs ys)) _
    ∙ size-∪∷-∥ₛ ∩∷-minus-∥ₛ ⁻¹
    ∙ ap sizeₛ (∩∷-minus-compl {ys = ys})

size-≥-⊆ : ⦃ d : is-discrete A ⦄ → {xs ys : LFSet A}
          → xs ⊆ ys → sizeₛ xs ＝ sizeₛ ys → ys ⊆ xs
size-≥-⊆ {A} {xs} {ys} xs⊆ys se =
  size-∪∷-⊆ (ap sizeₛ (⊆-∪= xs⊆ys) ∙ se ⁻¹)

opaque
  unfolding mapₛ

  -- to get rid of truncation, we'd have to guarantee that x is uniquely determined by z
  mapₛ-∈ : {A : 𝒰 ℓ} {B : 𝒰 ℓ′} -- why
         → ⦃ dB : is-discrete B ⦄
         → {f : A → B} {s : LFSet A} {z : B}
         → z ∈ mapₛ f s
         → ∃[ x ꞉ A ] ((x ∈ₛ s) × (z ＝ f x))
  mapₛ-∈ {A} {B} {f} {s} {z} = elim-prop go s
    where
    go : Elim-prop λ q → z ∈ mapₛ f q → ∃[ x ꞉ A ] ((x ∈ₛ q) × (z ＝ f x))
    go .[]ʳ = false! ⦃ Refl-x∉ₛ[] ⦄
    go .∷ʳ x {xs} ih x∈∷ =
       [ (λ z=fx → ∣ x , hereₛ refl , z=fx ∣₁)
       , (λ z∈fxs →
             map (λ where (q , xq , zq) → q , thereₛ xq , zq)
                 (ih z∈fxs))
       ]ᵤ (∈ₛ-∷→ x∈∷)
    go .truncʳ x = hlevel!

  mapₛ-⊆ : {A : 𝒰 ℓ} {B : 𝒰 ℓ′} -- why
         → ⦃ dB : is-discrete B ⦄
         → {f : A → B} {s1 s2 : LFSet A}
         → s1 ⊆ s2 → mapₛ f s1 ⊆ mapₛ f s2
  mapₛ-⊆ {f} {s1} {s2} s12 {x} x∈ =
    rec! (λ a a∈ xe → subst (_∈ₛ mapₛ f s2) (xe ⁻¹) (∈-mapₛ (s12 a∈)))
         (mapₛ-∈ {s = s1} x∈)

  -- TODO is there a more general way? seems to require injectivity of ∷
  mapₛ-inj : {f : A → B}
           → ⦃ dA : is-discrete A ⦄
           → ⦃ dB : is-discrete B ⦄
           → Injective f → Injective (mapₛ f)
  mapₛ-inj {f} inj {x} {y} e =
    set-ext λ z →
      prop-extₑ!
        (λ z∈x →
            rec! (λ fz fz∈y fze →
                     subst (_∈ₛ y) (inj (fze ⁻¹)) fz∈y)
              (mapₛ-∈ {f = f} {s = y} $
               subst (f z ∈ₛ_) e $
               ∈-mapₛ {f = f} z∈x))
        (λ z∈y →
            rec! (λ fz fz∈x fze →
                     subst (_∈ₛ x) (inj (fze ⁻¹)) fz∈x)
              (mapₛ-∈ {f = f} {s = x} $
               subst (f z ∈ₛ_) (e ⁻¹) $
               ∈-mapₛ {f = f} z∈y))

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

opaque
  unfolding joinₛ

  joinₛ-∈-≤ : {o ℓ : Level} {A : Poset o ℓ} {js : is-join-semilattice A}
              ⦃ d : is-discrete (Poset.Ob A) ⦄
            → {z : Poset.Ob A} {xs : LFSet (Poset.Ob A)}
            → z ∈ xs → Poset._≤_ A z (joinₛ {js = js} xs)
  joinₛ-∈-≤ {A} {js} {z} {xs} = elim-prop go xs
    where
      open Poset A renaming (_≤_ to _≤ₐ_; =→≤ to =→≤ₐ)
      open is-join-semilattice js
      go : Elim-prop λ q → z ∈ q → z ≤ₐ joinₛ {js = js} q
      go .[]ʳ = false! ⦃ Refl-x∉ₛ[] ⦄
      go .∷ʳ x ih z∈∷ =
        ≤⊎→∪ $
        Sum.dmap =→≤ₐ ih $
        ∈ₛ-∷→ z∈∷
      go .truncʳ = hlevel!

opaque
  unfolding meetₛ

  meetₛ-∈-≤ : {o ℓ : Level} {A : Poset o ℓ} {ms : is-meet-semilattice A}
              ⦃ d : is-discrete (Poset.Ob A) ⦄
            → {z : Poset.Ob A} {xs : LFSet (Poset.Ob A)}
            → z ∈ xs → Poset._≤_ A (meetₛ {ms = ms} xs) z
  meetₛ-∈-≤ {A} {ms} {z} {xs} = elim-prop go xs
    where
      open Poset A renaming (_≤_ to _≤ₐ_; =→≤ to =→≤ₐ)
      open is-meet-semilattice ms
      go : Elim-prop λ q → z ∈ q → meetₛ {ms = ms} q ≤ₐ z
      go .[]ʳ = false! ⦃ Refl-x∉ₛ[] ⦄
      go .∷ʳ x ih z∈∷ =
        ≤⊎→∩ $
        Sum.dmap (=→≤ₐ ∘ _⁻¹) ih $
        ∈ₛ-∷→ z∈∷
      go .truncʳ = hlevel!

opaque
--  unfolding empty?
  -- extract the element if the set is a singleton

  extract1 : ⦃ d : is-discrete A ⦄ → LFSet A → Maybe A
  extract1 {A} ⦃ d ⦄ = rec go
    where
      go : Rec A (Maybe A)
      go .[]ʳ = nothing
      go .∷ʳ x xs _ = if empty? (rem x xs) then just x else nothing
      go .dropʳ x xs _ =
        ap (λ q → if empty? q then just x else nothing) $
        rem-∷ ∙ (given-yes_return_then_ ⦃ A-pr = hlevel-instance (is-discrete→is-set d x x) ⦄  -- TODO
                   refl (λ q → (if ⌊ q ⌋ then rem x xs else x ∷ rem x xs) ＝ rem x xs) refl)
      go .swapʳ x y xs _ =
          ap (λ q → if empty? q then just x else nothing) rem-∷
        ∙ Dec.elim
             {C = λ q → (if empty? (if ⌊ q ⌋ then rem x xs else y ∷ rem x xs) then just x else nothing)
                        ＝
                        (if empty? (if ⌊ q ⌋ then rem y xs else x ∷ rem y xs) then just y else nothing)}
             (λ x=y → ap (λ q → if empty? (rem q xs) then just q else nothing) x=y)
             (λ _ → refl)
             (x ≟ y)
        ∙ ap (λ q → if empty? (if q then rem y xs else x ∷ rem y xs) then just y else nothing)
             (=?-sym {x = x})
        ∙ ap (λ q → if empty? q then just y else nothing)
             (rem-∷ ⁻¹)
      go .truncʳ = maybe-is-of-hlevel 0 $ is-discrete→is-set d

  extract1-[] : ⦃ d : is-discrete A ⦄ → extract1 (the (LFSet A) []) ＝ nothing
  extract1-[] = refl

  extract1-x∷ : ⦃ d : is-discrete A ⦄ → {x : A} → x ∈ extract1 (sng x)
  extract1-x∷ {x} = =just→∈ (ap (λ q → if empty? q then just x else nothing) rem-[])

  extract1-just : ⦃ d : is-discrete A ⦄
                → {s : LFSet A} {x : A}
                → x ∈ extract1 s
                → s ＝ sng x
  extract1-just {A} {s} {x} = elim-prop go s
    where
      go : Elim-prop λ q → x ∈ extract1 q → q ＝ sng x
      go .[]ʳ = false!
      go .∷ʳ x {xs} ih with empty? (rem x xs) | recall empty? (rem x xs)
      ... | true  | ⟪ eq ⟫ =
        λ e →   ∷-rem
              ∙ ap² {C = λ _ _ → LFSet A} _∷_
                    (just-inj (∈→true reflectsΣ-= e))
                    (so→true! ⦃ Reflects-empty? {A = A} {s = rem x xs} ⦄ (so≃is-true ⁻¹ $ eq))
      ... | false | _ = false!
      go .truncʳ _ = hlevel!

  -- TODO is there a nicer way?
  reflectsΣ-extract1 : ⦃ d : is-discrete A ⦄
                     → {s : LFSet A} → ReflectsΣ (λ x → s ＝ sng x) (extract1 s)
  reflectsΣ-extract1 {A} {s} =
    ReflectsΣ.dmap
      (λ x → extract1-just)
      (λ x → contra λ e → =just→∈ (ap extract1 e ∙ ∈→true reflectsΣ-= extract1-x∷))
      reflectsΣ-∈

  extract1-nothing : ⦃ d : is-discrete A ⦄
                   → {s : LFSet A}
                   → extract1 s ＝ nothing
                   → (s ＝ []) ⊎₁ (1 < sizeₛ s)
  extract1-nothing {A} {s} = elim-prop go s
    where
      go : Elim-prop λ q → extract1 {A = A} q ＝ nothing → (q ＝ []) ⊎₁ (1 < sizeₛ q)
      go .[]ʳ _ = ∣ inl refl ∣₁
      go .∷ʳ x {xs} ih with empty? (rem x xs) | recall empty? (rem x xs)
      ... | true  | _      = false!
      ... | false | ⟪ eq ⟫ = λ _ →
         ∣ inr (subst (1 <_) (size-∷ {x = x} {s = xs} ⁻¹) $
                s<s $
                [ id
                , (λ s=0 → false! (eq ⁻¹ ∙ ap empty? (size0 (s=0 ⁻¹))))
                ]ᵤ (≤→<⊎= (z≤ {n = sizeₛ (rem x xs)}))) ∣₁
      go .truncʳ _ = hlevel!
