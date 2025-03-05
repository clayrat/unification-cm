{-# OPTIONS --safe #-}
module Ren where

open import Prelude
open import Foundations.Sigma
open Variadics _
open import Meta.Effect

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.DivMod.Base
open import Data.Nat.Order.Base

open import Data.List as List
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Membership
open import Data.List.Correspondences.Unary.Unique
open import Data.List.Operations.Properties
open import Data.Sum as ⊎

open import Data.Acc

open import MinSearch

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

open import Id

-- cofinite renaming theory

record Ren : 𝒰 where
  constructor is-ren
  field
    eqvr : Id ≃ Id
    supr : LFSet Id
    cofr : {x : Id} → x ∉ supr → (eqvr $ x) ＝ x

open Ren public

-- TODO drop/move
ren-bwd : ∀ {r} {x y : Id} → (r .eqvr $ x) ＝ y → (r .eqvr ⁻¹ $ y) ＝ x
ren-bwd {r} e = Equiv.adjunct-l (r. eqvr) e ⁻¹

ren-fwd : ∀ {r} {x y : Id} → (r .eqvr ⁻¹ $ x) ＝ y → (r .eqvr $ y) ＝ x
ren-fwd {r} e = Equiv.adjunct-r (r. eqvr) (e ⁻¹)

iter-cancel : ∀ {r} {x : Id} {n} → iter n (r .eqvr $_) (iter n (r .eqvr ⁻¹ $_) x) ＝ x
iter-cancel {n = zero}  = refl
iter-cancel {r} {x} {n = suc n} =
    ap (λ q → iter q (r .eqvr $_) (r .eqvr ⁻¹ $ iter n (_$_ (r .eqvr ⁻¹)) x)) (+-comm 1 n)
  ∙ iter-add n 1 (r .eqvr $_) (iter (suc n) (r .eqvr ⁻¹ $_) x)
  ∙ ap (iter n (r .eqvr $_)) (is-equiv→counit (r .eqvr .snd) (iter n (r .eqvr ⁻¹ $_) x))
  ∙ iter-cancel {r} {n = n}

cofr⁻¹ : ∀ r {x : Id} → x ∉ r .supr → (r .eqvr ⁻¹ $ x) ＝ x
cofr⁻¹ r = ren-bwd {r = r} ∘ r .cofr

ren-ext : {r₁ r₂ : Ren} → r₁ .eqvr ＝ r₂ .eqvr → r₁ .supr ＝ r₂ .supr → r₁ ＝ r₂
ren-ext {r₁ = is-ren e₁ d₁ c₁} {r₂ = is-ren e₂ d₂ c₂} ee ed =
  ap² (is-ren $²_)
      (×-path ee ed)
      (to-pathᴾ ((∀-is-of-hlevel 1 λ x → Π-is-of-hlevel 1 λ x∉ → hlevel 1) _ c₂))

ren-sup→ : ∀ {r} {x : Id} → x ∈ r .supr → (r .eqvr $ x) ∈ r .supr
ren-sup→ {r} {x} x∈ =
  dec→essentially-classical Dec-∈ₛ
    λ rx∉ →
       rx∉ (subst (_∈ₛ r .supr) (is-equiv→unit (r .eqvr .snd) x ⁻¹ ∙ cofr⁻¹ r rx∉) x∈)

ren-sup-iter→ : ∀ {r} {x : Id} {n : ℕ} → x ∈ r .supr → iter n (r .eqvr $_) x ∈ r .supr
ren-sup-iter→     {n = zero}  x∈ = x∈
ren-sup-iter→ {r} {n = suc n} x∈ =
  ren-sup→ {r = r} $ ren-sup-iter→ {r = r} {n = n} x∈

ren-sup← : ∀ {r} {x : Id} → x ∈ r .supr → (r .eqvr ⁻¹ $ x) ∈ r .supr
ren-sup← {r} {x} x∈ =
  dec→essentially-classical Dec-∈ₛ
    λ rx∉ →
       rx∉ (subst (_∈ₛ r .supr) (is-equiv→counit (r .eqvr .snd) x ⁻¹ ∙ r .cofr rx∉) x∈)

ren-sup-iter← : ∀ {r} {x : Id} {n : ℕ} → x ∈ r .supr → iter n (r .eqvr ⁻¹ $_) x ∈ r .supr
ren-sup-iter←     {n = zero}  x∈ = x∈
ren-sup-iter← {r} {n = suc n} x∈ =
  ren-sup← {r = r} $ ren-sup-iter← {r = r} {n = n} x∈

-- identity

id-ren : Ren
id-ren = is-ren refl [] λ _ → refl

-- flip

flp : Ren → Ren
flp r .eqvr = r .eqvr ⁻¹
flp r .supr = r .supr
flp r .cofr = cofr⁻¹ r

-- composition

_◇↔_ : Ren → Ren → Ren
(s ◇↔ t) .eqvr = t .eqvr ∙ s .eqvr
(s ◇↔ t) .supr = t .supr ∪∷ s .supr
(s ◇↔ t) .cofr x∉ =
  let (x∉t , x∉s) = ∉ₛ-∪∷ {xs = t .supr} x∉ in
  ap (s .eqvr $_) (t .cofr x∉t) ∙ s .cofr x∉s

-- transposition

transpose : Id → Id → Id → Id
transpose x y z = if z == x then y else if z == y then x else z

transpose-inv : ∀ {x y z} → transpose x y (transpose x y z) ＝ z
transpose-inv {x} {y} {z} =
  Dec.elim
    {C = λ q →
       (if (if ⌊ q ⌋ then y else if z == y then x else z) == x then y
         else if (if ⌊ q ⌋ then y else if z == y then x else z) == y then x else
           (if ⌊ q ⌋ then y else if z == y then x else z)) ＝ z}
    (λ z=x → Dec.elim
              {C = λ q → (if ⌊ q ⌋ then y else (if y == y then x else y))  ＝ z}
              (λ y=x → y=x ∙ z=x ⁻¹ )
              (λ y≠x → given-yes (the (y ＝ y) refl)
                          return (λ q → (if ⌊ q ⌋ then x else y) ＝ z)
                          then (z=x ⁻¹))
              (y ≟ x))
    (λ z≠x → Dec.elim
                {C = λ q →
                   (if (if ⌊ q ⌋ then x else z) == x then y
                       else if (if ⌊ q ⌋ then x else z) == y then x
                            else if ⌊ q ⌋ then x else z) ＝ z}
                (λ z=y → given-yes (the (x ＝ x) refl)
                           return (λ q → (if ⌊ q ⌋ then y else (if x == y then x else x)) ＝ z)
                           then (z=y ⁻¹))
                (λ z≠y → given-no z≠x
                           return (λ q → (if ⌊ q ⌋ then y else (if z == y then x else z)) ＝ z)
                           then (given-no z≠y
                                  return (λ q → (if ⌊ q ⌋ then x else z) ＝ z)
                                  then refl))
                (z ≟ y))
    (z ≟ x)

transpose-≃ : Id → Id → Id ≃ Id
transpose-≃ x y =
  ≅→≃ $
  make-iso (transpose x y) (transpose x y) $
  make-inverses (fun-ext λ z → transpose-inv) (fun-ext λ z → transpose-inv)

_↔1_ : Id → Id → Ren
(x ↔1 y) .eqvr = transpose-≃ x y
(x ↔1 y) .supr = x ∷ y ∷ []
(x ↔1 y) .cofr {x = z} z∉ =
  let (z≠x , z∉′) = ∉ₛ-uncons z∉
      (z≠y , _) = ∉ₛ-uncons z∉′
    in
  given-no z≠x
    return (λ q → (if ⌊ q ⌋ then y else if z == y then x else z) ＝ z)
    then (given-no z≠y
           return (λ q → (if ⌊ q ⌋ then x else z) ＝ z)
           then refl)

{-
-- injective

injective-ren : (f : Id → Id) → Injective f → (s : LFSet Id) → ({x : Id} → x ∉ s → f x ＝ x) → Ren
injective-ren f fi s c .eqvr =
  f , is-surjective-embedding→is-equiv
        (λ x → Dec.elim
                  {C = λ _ → ∥ fibre f x ∥₁}
                  (λ x∈ → ∣ {!!} , {!!} ∣₁ )
                  (λ x∉ → ∣ x , c x∉ ∣₁)
                  (x ∈? s))
        (set-injective→is-embedding! fi)
injective-ren f fi s c .supr = s
injective-ren f fi s c .cofr = c
-}

-- orbits

is-fixed-point : Id ≃ Id → Id → ℕ → 𝒰
is-fixed-point r x n = (r $ iter n (r $_) x) ＝ x

-- TODO refactor as in Quasi

Pos : Id ≃ Id → Id → ℕ → Prop 0ℓ
Pos r x n = el! (is-fixed-point r x n)

opaque
  unfolding sizeₛ

  osizebnd-body-type : Id ≃ Id → LFSet Id → 𝒰
  osizebnd-body-type r s =
      (a : LFSet Id)
    → ((y : Id) → y ∉ (a ∪∷ s) → (r $ y) ＝ y)
    → (x : Id)
    → ((y : Id) → y ∈ₛ a → Σ[ n ꞉ ℕ ] (((r $ iter n (r $_) y) ＝ x)))
    → Σ[ Pos r x ]

  osizebnd-body : (r : Id ≃ Id) → (s : LFSet Id)
                → ((s′ : LFSet Id) → sizeₛ s′ < sizeₛ s → osizebnd-body-type r s′)
                → osizebnd-body-type r s
  osizebnd-body r s ih ac co x ae with x ∈? ac
  osizebnd-body r s ih ac co x ae | yes x∈a = ae x x∈a
  osizebnd-body r s ih ac co x ae | no x∉a with x ∈? s
  osizebnd-body r s ih ac co x ae | no x∉a | yes x∈s =
    let (n , e) = ih (rem x s) (rem-size-neg x∈s)
                           (x ∷ ac)
                            (λ z z∉ → co z (subst (z ∉_)
                                               (  ∪∷-swap {s = ac}
                                                ∙ ap (ac ∪∷_) (rem-∈-eq x∈s))
                                               z∉))
                           (r $ x)
                           (λ y y∈ → [ (λ y=x →  0 ,  ap (r $_) y=x)
                                      , (λ y∈′ → let (m ,  me) = ae y y∈′ in
                                                      suc m , ap (r $_) me)

                                      ]ᵤ (∈ₛ-∷→ y∈))
      in ( n
            ,   ap (λ q → iter q (r $_) x) (+-comm 1 n)
              ∙ iter-add n 1 (r $_) x
              ∙ (is-embedding→injective (is-equiv→is-embedding (r .snd)) $ e))
  osizebnd-body r s ih ac co x ae | no x∉a | no x∉s  =
    0 , co x (∪∷-∉ₛ x∉a x∉s)

  osizebnd : (r : Ren) → (x : Id) → Σ[ Pos (r .eqvr) x ]
  osizebnd r x =
    to-induction
      {A = LFSet Id}
      (wf-lift sizeₛ <-is-wf)
      (osizebnd-body-type (r .eqvr))
      (osizebnd-body (r .eqvr))
      (r .supr)
      []
      (λ z z∉ → r .cofr {z} z∉)
      x
      (λ y → false! ⦃ Refl-x∉ₛ[] ⦄)

osizeP : (r : Ren) → (x : Id)
      → Σ[ n ꞉ ℕ ] (is-fixed-point (r .eqvr) x n) × ((m : ℕ) → is-fixed-point (r .eqvr) x m → n ≤ m)
osizeP r x = minP {P = Pos (r .eqvr) x} auto ∣ osizebnd r x ∣₁

opaque
  osize : Ren → Id → ℕ
  osize r x = osizeP r x .fst

  osize-fixed : ∀ {r x} → is-fixed-point (r .eqvr) x (osize r x)
  osize-fixed {r} {x} = osizeP r x .snd .fst

  osize-min : ∀ {r x m} → is-fixed-point (r .eqvr) x m → osize r x ≤ m
  osize-min {r} {x} {m} = osizeP r x .snd .snd m

osize-ne : ∀ {r x m} → m < osize r x → (r .eqvr $ iter m (r .eqvr $_) x) ≠ x
osize-ne {r} {x} {m} mlt e = <→≱ mlt (osize-min {r = r} {m = m} e)

osize-inv : ∀ {r x} → (r .eqvr ⁻¹ $ x) ＝ (iter (osize r x) (r .eqvr $_) x)
osize-inv {r} {x} =
  is-embedding→injective (is-equiv→is-embedding (r .eqvr .snd)) $
  is-equiv→counit (r .eqvr .snd) x ∙ osize-fixed {r = r} ⁻¹

osize-r : ∀ {r x} → osize r x ＝ osize r (r .eqvr $ x)
osize-r {r} {x} =
  ≤-antisym
    (osize-min (  ap (λ q → iter q (r .eqvr $_) x) (+-comm 1 (osize r (r .eqvr $ x)))
                ∙ iter-add (osize r (r .eqvr $ x)) 1 (r .eqvr $_) x
                ∙ is-embedding→injective (is-equiv→is-embedding (r .eqvr .snd)) (osize-fixed {r} {r .eqvr $ x})))
    (osize-min (ap (r .eqvr $_) $
                   iter-add (osize r x) 1 (r .eqvr $_) x ⁻¹
                 ∙ ap (λ q → iter q (r .eqvr $_) x) (+-comm (osize r x) 1)
                 ∙ osize-fixed {r} {x}))

osize-iter : ∀ {r x n} → osize r x ＝ osize r (iter n (r .eqvr $_) x)
osize-iter {r} {x} {n = zero } = refl
osize-iter {r} {x} {n = suc n} = osize-iter {r} {x} {n = n} ∙ osize-r

osize-mod : ∀ {r x n} → iter n (r .eqvr $_) x ＝ iter (n % suc (osize r x)) (r .eqvr $_) x
osize-mod {r} {x} {n} =
    ap (λ q → iter q (r .eqvr $_) x) (m≡m%n+[m/n]*n n (suc (osize r x)))
  ∙ ap (λ q → iter q (r .eqvr $_) x) (+-comm (n % suc (osize r x)) (n / suc (osize r x) · suc (osize r x)))
  ∙ iter-add (n / suc (osize r x) · suc (osize r x)) (n % suc (osize r x)) (r .eqvr $_) x
  ∙ iter-mul (n / suc (osize r x)) (suc (osize r x)) (r .eqvr $_) (iter (n % (suc (osize r x))) (r .eqvr $_) x)
  ∙ iter-idem (n / suc (osize r x)) (iter (suc (osize r x)) (r .eqvr $_)) (iter (n % (suc (osize r x))) (r .eqvr $_) x)
      λ m → ap (λ q → r .eqvr $ (iter q (r .eqvr $_) (iter m (iter (suc (osize r x)) (r .eqvr $_)) (iter (n % suc (osize r x)) (r .eqvr $_) x))))
               (  osize-iter {n = m · suc (osize r x) + n % suc (osize r x)}
                ∙ ap (osize r) (  iter-add (m · suc (osize r x)) (n % suc (osize r x)) (r .eqvr $_) x
                                ∙ iter-mul m (suc (osize r x)) (r .eqvr $_) (iter (n % suc (osize r x)) (r .eqvr $_) x)))
            ∙ osize-fixed {r = r}

traject : Ren → Id → List Id
traject r x = map (λ n → iter n (r .eqvr $_) x) $ count-from-to 0 (suc (osize r x))

traject-uniq-aux : ∀ {r} {x} n
                 → n ≤ suc (osize r x)
                 → Uniq (map (λ n → iter n (r .eqvr $_) x) $ count-from-to 0 n)
traject-uniq-aux          zero   nle = []ᵘ
traject-uniq-aux {r} {x} (suc n) nle =
  let nle′ = ≤-peel nle
      ih = traject-uniq-aux {r = r} {x = x} n (nle′ ∙ ≤-ascend)
      meq = happly (map-pres-comp {f = suc} {g = λ k → iter k (r .eqvr $_) x}) (count-from-to 0 n)
    in
  subst (x ∉_) meq
        (contra (map-∈Σ λ k → r .eqvr $ iter k (r .eqvr $_) x)
                λ where (q , q∈ , qe) →
                          let q<n = count-from-to-∈ {m = 0} {n = n} q∈ .snd in
                          osize-ne (<-≤-trans q<n nle′) (qe ⁻¹)
        )
  ∷ᵘ subst Uniq
           (happly (map-pres-comp {f = λ k → iter k (r .eqvr $_) x} {g = r .eqvr $_} ⁻¹) (count-from-to 0 n) ∙ meq)
           (uniq-map (is-embedding→injective (is-equiv→is-embedding (r .eqvr .snd))) ih)

traject-uniq : ∀ {r} {x} → Uniq (traject r x)
traject-uniq {r} {x} =
  traject-uniq-aux (suc (osize r x)) ≤-refl

orbit : Ren → Id → LFSet Id
orbit r x = from-list $ traject r x

orbit-size : ∀ {r} {x} → sizeₛ (orbit r x) ＝ suc (osize r x)
orbit-size {r} {x} =
    size-unique {s = traject r x} traject-uniq
  ∙ ap suc (map-length ∙ map-length ∙ count-from-to-len {m = 0} {n = osize r x})

-- TODO ad-hoc
cft-mapsuc : ∀ {n m} → n ≤ m → (suc <$> count-from-to (m ∸ n) m) ＝ count-from-to (suc m ∸ n) (suc m)
cft-mapsuc {n = zero}  {m = zero}  n≤m = refl
cft-mapsuc {n = suc n} {m = zero}  n≤m = false! n≤m
cft-mapsuc {n = zero}  {m = suc m} n≤m = refl
cft-mapsuc {n = suc n} {m = suc m} n≤m =
  ap (map suc) (count-from-to-suc-r {m = m ∸ n} {n = m} (∸≤≃≤+ {m = m} {n = n} ⁻¹ $ ≤-+-l))
  ∙ map-∷r
  ∙ ap (λ q → snoc q (suc m)) (cft-mapsuc (≤-peel n≤m))
  ∙ count-from-to-suc-r {m = suc m ∸ n} {n = suc m} (∸≤≃≤+ {m = suc m} {n = n} ⁻¹ $ ≤-+-l) ⁻¹

traject-mem-aux : ∀ {r} {x} {y} n
                    → n ≤ suc (osize r x)
                    → y ∈ (map (λ n → iter n (r .eqvr $_) x) $ count-from-to ((suc (osize r x)) ∸ n) (suc (osize r x)))
                    → Σ[ m ꞉ ℕ ] (m ≤ osize r x) × (iter m (r .eqvr $_) x ＝ y)
traject-mem-aux {r} {x} {y}  zero   nle yi =
  false! (subst (λ q → y ∈ (mapₗ (λ n → iter n (_$_ (r .eqvr)) x) $ suc <$> q))
                (count-from-to-idem {n = osize r x})
                yi)
traject-mem-aux {r} {x} {y} (suc n) nle yi =
  let nle′ = ≤-peel nle in
  [ (λ e → (osize r x ∸ n) , (∸≤≃≤+ {m = osize r x} {n = n} ⁻¹ $ ≤-+-l) , (e ⁻¹))
  , (λ y∈′ → traject-mem-aux {r = r} {x = x} {y = y} n (nle′ ∙ ≤-ascend)
                      (subst (λ q → y ∈ₗ (mapₗ (λ n₁ → iter n₁ (_$_ (r .eqvr)) x) $ q)) (cft-mapsuc nle′) y∈′))
  ]ᵤ (any-uncons $
      subst (λ q → y ∈ (mapₗ (λ n → iter n (_$_ (r .eqvr)) x) $ q))
                 (count-from-to-suc-l {m = osize r x ∸ n} {n = suc (osize r x)}
                      (≤≃<suc $ ∸≤≃≤+ {m = osize r x} {n = n} ⁻¹ $ ≤-+-l))
                 yi)

traject-mem : ∀ {r} {x} {y}
                    → y ∈ traject r x
                    → Σ[ m ꞉ ℕ ] (m ≤ osize r x) × (iter m (r .eqvr $_) x ＝ y)
traject-mem {r} {x} {y} y∈ =
  traject-mem-aux (suc (osize r x)) ≤-refl $
  subst (λ q → y ∈ (mapₗ (λ n → iter n (_$_ (r .eqvr)) x) $ count-from-to q (suc (osize r x))))
        (∸-cancel (osize r x) ⁻¹)
        y∈

orbit-mem : ∀ {r} {x} {y} → y ∈ orbit r x → Σ[ n ꞉ ℕ ] (n ≤ osize r x) × (iter n (r .eqvr $_) x ＝ y)
orbit-mem {r} {x} = traject-mem ∘ list-∈ {xs = traject r x}

mem-orbit : ∀ {r} {x} {n} → iter n (r .eqvr $_) x ∈ orbit r x
mem-orbit {r} {x} {n} =
  subst (_∈ orbit r x) (osize-mod {r = r} {x = x} {n = n} ⁻¹) $
  ∈-list {xs = traject r x} $
  ∈-map {x = n % suc (osize r x)} {xs = count-from-to 0 (suc (osize r x))}
         (λ k → iter k (r .eqvr .fst) x) $
  ∈-count-from-to {m = 0} {n = suc (osize r x)}
     z≤
     (m%n<n n (suc (osize r x)) z<s)

orbit-r : ∀ {r} {x} → orbit r x ＝ orbit r (r .eqvr $ x)
orbit-r {r} {x}=
  set-ext λ z →
     prop-extₑ!
       (λ z∈o →
           let (n , _ , ne) = orbit-mem z∈o in
           subst (_∈ₛ orbit r (r .eqvr $ x))
                 (  iter-add (n + osize r x) 1 (r .eqvr $_) x ⁻¹
                  ∙ ap (λ q → iter q (r .eqvr $_) x)
                       (+-comm (n + osize r x) 1 ∙ +-suc-r n (osize r x) ⁻¹)
                  ∙ iter-add n (suc (osize r x)) (r .eqvr $_) x
                  ∙ ap (iter n (r .eqvr $_)) (osize-fixed {r = r} {x = x})
                  ∙ ne)
                 (mem-orbit {n = n + osize r x}))
       λ z∈ro →
           let (n , nle , ne) = orbit-mem z∈ro in
           subst (_∈ₛ orbit r x)
                 (iter-add n 1 (r .eqvr $_) x ∙ ne)
                 (mem-orbit {n = n + 1})

orbit-iter : ∀ {r} {x} {n} → orbit r x ＝ orbit r (iter n (r .eqvr $_) x)
orbit-iter {n = zero}  = refl
orbit-iter {n = suc n} = orbit-iter {n = n} ∙ orbit-r

orbit-mem-eq : ∀ {r} {x} {y} → y ∈ orbit r x → orbit r x ＝ orbit r y
orbit-mem-eq {r} y∈ =
  let (k , _ , ke) = orbit-mem y∈ in
  orbit-iter {n = k} ∙ ap (orbit r) ke

orbit-sym : ∀ {r} {x} {y} → y ∈ orbit r x → x ∈ orbit r y
orbit-sym {x} y∈ = subst (x ∈_) (orbit-mem-eq y∈) (mem-orbit {n = 0})

orbit-flp : ∀ {r} {x} → orbit (flp r) x ＝ orbit r x
orbit-flp {r} {x} =
  set-ext λ z →
    prop-extₑ!
       (λ z∈fo →
            let (n , nle , ne) = orbit-mem (orbit-sym z∈fo) in
            subst (  _∈ orbit r x)
                  (  ap (iter n (r .eqvr $_)) (ne ⁻¹)
                   ∙ iter-cancel {r = r} {x = z} {n = n})
                  (mem-orbit {n = n}))
       λ z∈o →
            let (n , nle , ne) = orbit-mem (orbit-sym z∈o) in
            subst (_∈ orbit (flp r) x)
                  (  ap (iter n (r .eqvr ⁻¹ $_)) (ne ⁻¹)
                   ∙ iter-cancel {r = flp r} {x = z} {n = n})
                  (mem-orbit {n = n})
