{-# OPTIONS --safe #-}
module Nominal.Cofinite.Ren.Quasi where

open import Prelude
open import Foundations.Sigma
open Variadics _
open import Meta.Effect

open import Data.Empty hiding (_≠_)
open import Data.Bool as Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.DivMod
open import Data.Nat.DivMod.Base
open import Data.Nat.Order.Base
open import Data.Maybe
open import Data.List as List
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Membership
open import Data.List.Correspondences.Unary.Unique
open import Data.List.Correspondences.Binary.Prefix
open import Data.List.Operations.Properties
open import Data.List.Traject
open import Data.Sum as ⊎

open import Data.Acc

open import MinSearch

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

open import Nominal.Term
open import Nominal.Cofinite.Base
open import Nominal.Cofinite.Ren

-- cofinite quasirenaming theory
-- (renaming where source and target variable sets don't necessarily coincide)

record QRen : 𝒰 where
  constructor is-qren
  field
    fwd  : Id → Id
    bwd  : Id → Id
    fdom : LFSet Id
    bdom : LFSet Id
    fcoh : {x : Id} → x ∈ fdom → (fwd x ∈ bdom) × (bwd (fwd x) ＝ x)
    bcoh : {x : Id} → x ∈ bdom → (bwd x ∈ fdom) × (fwd (bwd x) ＝ x)
    -- do we need these?
    fcof : {x : Id} → x ∉ fdom → fwd x ＝ x
    bcof : {x : Id} → x ∉ bdom → bwd x ＝ x

open QRen public

qren-ext : {r₁ r₂ : QRen}
         → r₁ .fwd ＝ r₂ .fwd
         → r₁ .bwd ＝ r₂ .bwd
         → r₁ .fdom ＝ r₂ .fdom
         → r₁ .bdom ＝ r₂ .bdom
         → r₁ ＝ r₂
qren-ext {r₁ = is-qren f₁ b₁ fd₁ bd₁ fc₁ bc₁ ff₁ bf₁} {r₂ = is-qren f₂ b₂ fd₂ bd₂ fc₂ bc₂ ff₂ bf₂} ef eb efb ebd =
  ap² {A = (Id → Id) × (Id → Id) × LFSet Id × LFSet Id}
      {B = λ where (f , b , fd , bd) →  ({x : Id} → x ∈ fd → (f x ∈ bd) × (b (f x) ＝ x))
                                       × ({x : Id} → x ∈ bd → (b x ∈ fd) × (f (b x) ＝ x))
                                       × ({x : Id} → x ∉ fd → f x ＝ x)
                                       × ({x : Id} → x ∉ bd → b x ＝ x)}
      {C = λ _ _ → QRen}
     (λ where (f , b , fd , bd) → λ where (fc , bc , ff , bf) → is-qren f b fd bd fc bc ff bf)
     (×-path ef (×-path eb (×-path efb ebd)))
     (to-pathᴾ ((×-is-of-hlevel 1 (∀-is-of-hlevel 1 λ x → Π-is-of-hlevel 1 λ x∈ → hlevel 1) $
                 ×-is-of-hlevel 1 (∀-is-of-hlevel 1 λ x → Π-is-of-hlevel 1 λ x∈ → hlevel 1) $
                 ×-is-of-hlevel 1 (∀-is-of-hlevel 1 λ x → Π-is-of-hlevel 1 λ x∉ → hlevel 1)
                                  (∀-is-of-hlevel 1 λ x → Π-is-of-hlevel 1 λ x∉ → hlevel 1))
        _
        (((λ {x} → fc₂) , (λ {x} → bc₂) , (λ {x} → ff₂) , (λ {x} → bf₂)))))

fwd-unwind : ∀ {r x} → r .fwd x ∈ r .fdom → x ∈ r .fdom
fwd-unwind {r} rx∈ =
  dec→essentially-classical Dec-∈ₛ
    λ x∉ →
       x∉ (subst (_∈ₛ r .fdom) (r .fcof x∉) rx∈)

fwd-iter-unwind : ∀ {r x n}
                → iter n (r .fwd) x ∈ r .fdom
                → ∀ k → k < n → iter k (r .fwd) x ∈ r .fdom
fwd-iter-unwind         {n = zero}  nx∈ k k<n = false! k<n
fwd-iter-unwind {r} {x} {n = suc n} nx∈ k k<n =
  let nx∈′ = fwd-unwind {r = r} nx∈ in
  [ (λ k<n′ → fwd-iter-unwind {r = r} nx∈′ k k<n′)
  , (λ k=n → subst (λ q → iter q (r .fwd) x ∈ r .fdom) (k=n ⁻¹) nx∈′)
  ]ᵤ (≤→<⊎= $ ≤≃<suc ⁻¹ $ k<n)

-- TODO bwd-unwind

fwd-∈-inj : ∀ {r x y} → x ∈ r .fdom → y ∈ r .fdom → r .fwd x ＝ r .fwd y → x ＝ y
fwd-∈-inj {r} x∈ y∈ e =
  fcoh r x∈ .snd ⁻¹ ∙ ap (r .bwd) e ∙ fcoh r y∈ .snd

bwd-∈-inj : ∀ {r x y} → x ∈ r .bdom → y ∈ r .bdom → r .bwd x ＝ r .bwd y → x ＝ y
bwd-∈-inj {r} x∈ y∈ e =
  bcoh r x∈ .snd ⁻¹ ∙ ap (r .fwd) e ∙ bcoh r y∈ .snd

fwd-∈-iter-inj : ∀ {r n x y}
                → (∀ m → m < n → iter m (r .fwd) x ∈ r .fdom × iter m (r .fwd) y ∈ r .fdom)
                → iter n (r .fwd) x ＝ iter n (r .fwd) y → x ＝ y
fwd-∈-iter-inj {r} {n = zero}  xy∈ e = e
fwd-∈-iter-inj {r} {n = suc n} xy∈ e =
  let (nx∈ , ny∈) = xy∈ n <-ascend in
  fwd-∈-iter-inj {r = r} {n = n} (λ m m<n → xy∈ m (<-suc-r m<n)) $
  fwd-∈-inj {r = r} nx∈ ny∈ e

fwd-∈-iter-<-inj : ∀ {r m n x}
                  → (∀ k → k < n → iter k (r .fwd) x ∈ r .fdom)
                  → m < n
                  → iter m (r .fwd) x ＝ iter n (r .fwd) x
                  → x ＝ iter (n ∸ m) (r .fwd) x
fwd-∈-iter-<-inj {r} {m} {n} {x} x∈ m<n e =
  fwd-∈-iter-inj {r = r} {n = m} {x = x}
    (λ k k< →   x∈ k (<-trans k< m<n)
              , subst (_∈ r .fdom) (iter-add k (n ∸ m) (r .fwd) x) (x∈ (k + (n ∸ m)) $
                subst (_< n) (∸∸-assoc n m k (<-weaken k m k<) (<-weaken m n m<n) ∙ +-comm (n ∸ m) k) $
                <-∸-l-≃ {m = n} {n = m ∸ k} (≤-<-trans z≤ m<n) ⁻¹ $
                <-+-0lr $
                <-∸-r-≃ {m = k} ⁻¹ $
                subst (_< m) (+-zero-r k ⁻¹) $
                k<))
    (  e
     ∙ ap (λ q → iter q (r .fwd) x)
          (  ap (n ∸_) (∸-cancel m ⁻¹)
           ∙ ∸∸-assoc n m m ≤-refl (<-weaken m n m<n)
           ∙ +-comm (n ∸ m) m)
     ∙ iter-add m (n ∸ m) (r .fwd) x)

fwd-∈-iter-cancel : ∀ {r} {x : Id} {k n}
                   → (∀ m → m < n → iter m (r .fwd) x ∈ r .fdom)
                   → k ≤ n → iter k (r .bwd) (iter n (r .fwd) x) ＝ iter (n ∸ k) (r .fwd) x
fwd-∈-iter-cancel {k = zero} {n = n} imd k≤n = refl
fwd-∈-iter-cancel {k = suc k} {n = zero} imd k≤n = absurd (s≰z k≤n)
fwd-∈-iter-cancel {r} {x} {k = suc k} {n = suc n} imd k≤n =
    ap (λ q → iter q (r .bwd) (r .fwd (iter n (r .fwd) x))) (+-comm 1 k)
  ∙ iter-add k 1 (r .bwd) (r .fwd (iter n (r .fwd) x))
  ∙ ap (iter k (r .bwd)) (r .fcoh (imd n <-ascend) .snd)
  ∙ fwd-∈-iter-cancel {r = r} {x = x} {k = k} {n = n} (λ m → imd m ∘ <-suc-r) (≤-peel k≤n)

bwd-∈-iter-inj : ∀ {r n x y}
                → (∀ m → m < n → iter m (r .bwd) x ∈ r .bdom × iter m (r .bwd) y ∈ r .bdom)
                → iter n (r .bwd) x ＝ iter n (r .bwd) y → x ＝ y
bwd-∈-iter-inj {r} {n = zero}  xy∈ e = e
bwd-∈-iter-inj {r} {n = suc n} xy∈ e =
  let (nx∈ , ny∈) = xy∈ n <-ascend in
  bwd-∈-iter-inj {r = r} {n = n} (λ m m<n → xy∈ m (<-suc-r m<n)) $
  bwd-∈-inj {r = r} nx∈ ny∈ e

fcof-iter : ∀ {r n x} → x ∉ r .fdom → iter (suc n) (r .fwd) x ＝ x
fcof-iter {r} {n = zero}  x∉ = r .fcof x∉
fcof-iter {r} {n = suc n} x∉ = ap (r .fwd) (fcof-iter {r = r} {n = n} x∉) ∙ r .fcof x∉

bcof-iter : ∀ {r n x} → x ∉ r .bdom → iter (suc n) (r .bwd) x ＝ x
bcof-iter {r} {n = zero}  x∉ = r .bcof x∉
bcof-iter {r} {n = suc n} x∉ = ap (r .bwd) (bcof-iter {r = r} {n = n} x∉) ∙ r .bcof x∉

-- identity

id-qren : QRen
id-qren .fwd = id
id-qren .bwd = id
id-qren .fdom = []
id-qren .bdom = []
id-qren .fcoh = false! ⦃ Refl-x∉ₛ[] ⦄
id-qren .bcoh = false! ⦃ Refl-x∉ₛ[] ⦄
id-qren .fcof _ = refl
id-qren .bcof _ = refl

-- flip

qflp : QRen → QRen
qflp r .fwd = r .bwd
qflp r .bwd = r .fwd
qflp r .fdom = r .bdom
qflp r .bdom = r .fdom
qflp r .fcoh = r .bcoh
qflp r .bcoh = r .fcoh
qflp r .fcof = r .bcof
qflp r .bcof = r .fcof

qflp-inv : ∀ {r} → qflp (qflp r) ＝ r
qflp-inv = qren-ext refl refl refl refl

-- transposition

_↔Q_ : Id → Id → QRen
(x ↔Q y) .fwd  z = if z == x then y else z
(x ↔Q y) .bwd  z = if z == y then x else z
(x ↔Q y) .fdom = x ∷ []
(x ↔Q y) .bdom = y ∷ []
(x ↔Q y) .fcoh {x = z} z∈ =
  let z=x = ∈ₛ∷-∉ z∈ ∉ₛ[] in
  given-yes z=x
     return (λ q → ((if ⌊ q ⌋ then y else z) ∈ₛ (y ∷ []))
                 × ((if (if ⌊ q ⌋ then y else z) == y then x
                    else if ⌊ q ⌋ then y else z) ＝ z))
     then (hereₛ refl , if-true (true→so! (the (y ＝ y) refl)) ∙ z=x ⁻¹)
(x ↔Q y) .bcoh {x = z} z∈ =
  let z=y = ∈ₛ∷-∉ z∈ ∉ₛ[] in
  given-yes z=y
     return (λ q → ((if ⌊ q ⌋ then x else z) ∈ₛ (x ∷ []))
                 × ((if (if ⌊ q ⌋ then x else z) == x then y
                    else if ⌊ q ⌋ then x else z) ＝ z))
     then (hereₛ refl , if-true (true→so! (the (x ＝ x) refl)) ∙ z=y ⁻¹)
(x ↔Q y) .fcof {x = z} z∉ =
  let z≠x = ∉ₛ-uncons z∉ .fst in
  given-no z≠x
     return (λ q → (if ⌊ q ⌋ then y else z) ＝ z)
     then refl
(x ↔Q y) .bcof {x = z} z∉ =
  let z≠y = ∉ₛ-uncons z∉ .fst in
  given-no z≠y
     return (λ q → (if ⌊ q ⌋ then x else z) ＝ z)
     then refl

-- quasirenaming trajectory

IsQTraject : QRen → Id → List Id → 𝒰
IsQTraject r z xs =
    (xs ＝ traj (r .fwd) z (length xs))
  × Uniq xs
  × All (_∈ r .fdom) xs  -- actually only last one is needed

iqt-head : ∀ {r z xs}
         → IsQTraject r z xs
         → head z xs ＝ z
iqt-head {xs = []}      _           = refl
iqt-head {xs = x ∷ xs} (ex , _ , _) = ∷-head-inj ex

iqt-head-∈ : ∀ {r z xs}
           → IsQTraject r z xs
           → z ∈ r .fdom
           → head z xs ∈ r .fdom
iqt-head-∈     {xs = []}     iqt               z∈ = z∈
iqt-head-∈ {r} {xs = x ∷ xs} (ex , _ , x∈ ∷ _) _  = x∈

iqt-z∉-[] : ∀ {r z xs}
           → IsQTraject r z xs
           → z ∉ r .fdom
           → xs ＝ []
iqt-z∉-[]     {xs = []}     (ex , _ ,      ax) z∉ = refl
iqt-z∉-[] {r} {xs = x ∷ xs} (ex , _ , x∈ ∷ ax) z∉ =
  absurd (z∉ (subst (_∈ r .fdom) (∷-head-inj ex) x∈))

iqt-next-0<-≠ : ∀ {r z xs k}
              → IsQTraject r z xs
              → 0 < k → k < length xs
              → iter (length xs) (r .fwd) z ≠ iter k (r .fwd) z
iqt-next-0<-≠              {k = zero}  _              0<k k< e = false! 0<k
iqt-next-0<-≠ {r} {z} {xs} {k = suc k} (ex , ux , ax) _   k< e =
  let 0<l = <-trans z<s k<
      ze = fwd-∈-iter-<-inj {r = r}
             (λ l l< → All→∀∈ ax (iter l (r .fwd) z) (subst (iter l (r .fwd) z ∈_) (ex ⁻¹) (∈-traj l<)))
             k<
             (e ⁻¹)
      lme = traj-uniq→iter-inj {n = length xs}
             (subst Uniq ex ux)
             0 (length xs ∸ suc k)
             0<l (<-∸-l-≃ {m = length xs} {n = suc k} 0<l ⁻¹ $ <-+-lr)
             ze
   in
  <→≱ k< (∸=0→≤ (lme ⁻¹))

iqt-next-loop : ∀ {r z xs}
              → IsQTraject r z xs
              → iter (length xs) (r .fwd) z ∈ xs
              → iter (length xs) (r .fwd) z ＝ z
iqt-next-loop {r} {z} {xs} (ex , ux , ax) nx∈ with traj-∈ (subst (iter (length xs) (r .fwd) z ∈_) ex nx∈)
... | zero  , _  , e = e
... | suc k , k< , e = absurd (iqt-next-0<-≠ {r = r} (ex , ux , ax) z<s k< e)

-- TODO!!
-- using `r .fwd (last z t)` from here on to get the "next" element after `t` seems
-- to mess up things because we have to be extra cautious about `t` being empty,
-- should probably refactor to use `iter` or `lastᵐ` instead so that we get `z` when `t` is empty

iqt-rev-traj-aux : ∀ {r} {z} {n}
                 → traj (r .bwd) (r .fwd (last z (traj (r .fwd) z n))) n ＝ traj (r .bwd) (iter n (r .fwd) z) n
iqt-rev-traj-aux         {n = zero}  = refl
iqt-rev-traj-aux {r} {z} {n = suc n} =
  ap (λ q → r .fwd q ∷ traj (r .bwd) (r .bwd (r .fwd q)) n)
     (traj-last {f = r .fwd} {x = z} {n = n})

iqt-rev-traj : ∀ {r z xs}
             → xs ＝ traj (r .fwd) z (length xs)
             → All (_∈ r .fdom) xs
             → reverse (map (r .fwd) xs) ＝ traj (r .bwd) (r .fwd (last z xs)) (length xs)
iqt-rev-traj {r} {z} {xs} =
  last-elim
    (λ q → q ＝ traj (r .fwd) z (length q)
         → All (_∈ r .fdom) q
         → reverse (map (r .fwd) q) ＝ traj (r .bwd) (r .fwd (last z q)) (length q))
    (λ _ _ → refl)
    (λ y ys ih e a →
       let (yse , ye) = snoc-inj (e ∙ ap (traj (r .fwd) z) (snoc-length ys) ∙ traj-snoc)
           (ays , ay) = ∷r-all a
         in
         (  ap reverse (map-∷r {f = r .fwd} {xs = ys})
          ∙ reverse-∷r {xs = map (r .fwd) ys}
          ∙ ap (r .fwd y ∷_)
               (  ih yse ays
                ∙ ap (λ q → traj (r .bwd) (r .fwd (last z q)) (length ys)) yse
                ∙ iqt-rev-traj-aux {r = r}
                ∙ ap (λ q → traj (r .bwd) q (length ys)) (ye ⁻¹ ∙ r .fcoh ay .snd ⁻¹))
          ∙ ap (traj (r .bwd) (r .fwd y)) (snoc-length ys ⁻¹)
          ∙ ap (λ q → traj (r .bwd) (r .fwd q) (length (snoc ys y))) (last-snoc {xs = ys} ⁻¹)))
    xs

iqt-flip : ∀ {r z t}
         → IsQTraject r z t
         → IsQTraject (qflp r) (r .fwd (last z t)) (reverse (map (r .fwd) t))
iqt-flip {r} {z} {t} (ex , ux , ax) =
      iqt-rev-traj {r = r} ex ax
    ∙ ap (traj (r .bwd) (r .fwd (last z t))) (map-length ⁻¹ ∙ reverse-length ⁻¹)
  , uniq-reverse {xs = map (r .fwd) t}
      (uniq-map-∈
        (λ {x} {y} x∈ y∈ →
            fwd-∈-inj {r = r}
              (All→∀∈ ax x x∈)
              (All→∀∈ ax y y∈))
        ux)
  , (all-⊆ (⊆-reverse {xs = mapₗ (r .fwd) t}) $
     all→map $
     all-map (fst ∘ r .fcoh) ax)

-- TODO can be further generalized to traj
iqt-0<-last : ∀ {r x t}
            → IsQTraject r x t
            → 0 < length t
            → iter (length t) (r .fwd) x ＝ r .fwd (last x t)
iqt-0<-last {r} {x} {t} iqt 0<l =
    traj-last {f = r .fwd} {x = x} {n = length t} ⁻¹
  ∙ last-change {xs = traj (r .fwd) (r .fwd x) (length t)}
      (subst (0 <_) (traj-length ⁻¹) 0<l)
  ∙ ap (last (r .fwd x)) (traj-map {f = r .fwd} {x = x} {n = length t} ⁻¹)
  ∙ ap (λ q → last (r .fwd x) (mapₗ (r .fwd) q)) (iqt .fst ⁻¹)
  ∙ last-map {f = r .fwd} {xs = t}

-- cyclic trajectory

-- TODO redefine via iter?
IsCycle : QRen → Id → List Id → 𝒰
IsCycle r x t = r .fwd (last x t) ＝ x

iqt-cyc-aux : ∀ {r z t}
            → IsQTraject r z t
            → z ∈ r .fdom  -- only needed when t is empty
            → r .bwd (last (r .fwd (last z t)) (reverse (map (r .fwd) t))) ＝ z
iqt-cyc-aux {r} {z} {t} iqt z∈ =
    ap (r .bwd) (last-reverse {xs = map (r .fwd) t} ∙ head-map {xs = t})
  ∙ ap (λ q → r .bwd (r .fwd q)) (head-last {xs = t})
  ∙ r .fcoh (iqt-head-∈ {r = r} iqt z∈) .snd
  ∙ iqt-head {r = r} iqt

iqt-cyc-flip : ∀ {r z t}
             → IsQTraject r z t
             → z ∈ r .fdom  -- only needed when t is empty
             → IsCycle r z t
             → IsCycle (qflp r) (r .fwd (last z t)) (reverse (map (r .fwd) t))
iqt-cyc-flip {r} {z} {t} iqt z∈ cyc = iqt-cyc-aux {r = r} iqt z∈ ∙ cyc ⁻¹

iqt-cyc-flip-inv : ∀ {r z t}
                 → IsQTraject r z t
                 → z ∈ r .fdom  -- only needed when t is empty
                 → IsCycle (qflp r) (r .fwd (last z t)) (reverse (map (r .fwd) t))
                 → IsCycle r z t
iqt-cyc-flip-inv {r} {z} {t} iqt z∈ cyc = cyc ⁻¹ ∙ iqt-cyc-aux {r = r} iqt z∈

iqt-cyc-bdom : ∀ {r z xs}
             → IsQTraject r z xs
             → z ∈ r .fdom  -- only needed when xs is empty
             → IsCycle r z xs
             → z ∈ r .bdom
iqt-cyc-bdom {r} {xs} (ex , ux , ax) z∈f cy =
  subst ( _∈ r .bdom) cy $
  r .fcoh
    (all→last {P = _∈ r .fdom} z∈f ax)
    .fst

-- linear trajectory

-- TODO maybe lastᵐ would be better?
IsLinear : QRen → Id → LFSet Id → List Id → 𝒰
IsLinear r x s t = iter (length t) (r .fwd) x ∉ s

ifqt-∈-0< : ∀ {r z t}
           → IsLinear r z (r .fdom) t
           → z ∈ r .fdom
           → 0 < length t
ifqt-∈-0< {r} {z} {t = []}    l x∈ = absurd (l x∈)
ifqt-∈-0< {r} {z} {t = x ∷ t} _ _ = z<s

lin→last∉ : ∀ {r x t}
           → IsQTraject r x t
           → IsLinear r x (r .fdom) t
           → r .fwd (last x t) ∉ r .fdom
lin→last∉ {r} {x} {t} iqt lin =
  [ (λ 0<l →
       subst (_∉ r .fdom) (iqt-0<-last {r = r} iqt 0<l) lin)
  , (λ l=0 →
       contra (subst (λ q → r .fwd (last x q) ∈ r .fdom
                          → iter (length q) (r .fwd) x ∈ r .fdom)
                     (length=0→nil (l=0 ⁻¹) ⁻¹)
                     (fwd-unwind {r = r})) lin)
  ]ᵤ (≤→<⊎= $ z≤ {n = length t})

traj-lin-flip-inj : ∀ {r z m n}
                  → All (_∈ r .fdom) (traj (r .fwd) z m)
                  → All (_∈ r .fdom) (traj (r .fwd) z n)
                  → IsLinear r z (r .fdom) (traj (r .fwd) z m)
                  → IsLinear r z (r .fdom) (traj (r .fwd) z n)
                  → m ＝ n
traj-lin-flip-inj         {m = zero}  {n = zero}  []         []         iltm iltn = refl
traj-lin-flip-inj         {m = zero}  {n = suc n} []         (an ∷ atn) iltm iltn =
  absurd (iltm an)
traj-lin-flip-inj         {m = suc m} {n = zero}  (am ∷ atm) []         iltm iltn =
  absurd (iltn am)
traj-lin-flip-inj {r} {z} {m = suc m} {n = suc n} (am ∷ atm) (an ∷ atn) iltm iltn =
  ap suc $
  traj-lin-flip-inj {r = r} {m = m} {n = n} atm atn
     (subst (_∉ r .fdom) (iter-swap 1 (length (traj (r .fwd) (r .fwd z) m)) (r .fwd) z) iltm)
     (subst (_∉ r .fdom) (iter-swap 1 (length (traj (r .fwd) (r .fwd z) n)) (r .fwd) z) iltn)

iqt-lin-flip : ∀ {r z t}
             → IsQTraject r z t
             → 0 < length t
             → z ∉ r .bdom
             → IsLinear (qflp r) (r .fwd (last z t)) (r .bdom) (reverse (map (r .fwd) t))
iqt-lin-flip {r} {z} {t} iqt 0<l z∉b =
  subst (λ q → iter q (r .bwd) (r .fwd (last z t)) ∉ r .bdom)
        (map-length ⁻¹ ∙ reverse-length {xs = map (r .fwd) t} ⁻¹) $
  contra (λ i∈ →
               subst (λ q → iter q (r .fwd) z ∈ₛ r .bdom) (∸-cancel (length t)) $
               subst (_∈ₛ r .bdom)
                     (fwd-∈-iter-cancel {r = r} {x = z} {k = length t}
                               (λ m m< → All→∀∈ (iqt .snd .snd) (iter m (r .fwd) z) $
                                         subst (iter m (r .fwd) z ∈_) (iqt .fst ⁻¹) $
                                         ∈-traj m<)
                               ≤-refl) $
               subst (λ q → iter (length t) (r .bwd) q ∈ₛ r .bdom)
                     (iqt-0<-last {r = r} iqt 0<l ⁻¹) $
               i∈)
          z∉b

-- inl = cycle, inr = linear
IsFullQTraject : QRen → Id → LFSet Id → List Id → 𝒰
IsFullQTraject r x s t = IsQTraject r x t × (IsCycle r x t ⊎ IsLinear r x s t)

-- computation

opaque
  unfolding sizeₛ

  qtraject-body-type : QRen → Id → LFSet Id → 𝒰
  qtraject-body-type r x s =
      s ⊆ r .fdom
    → (a : List Id)
    → IsQTraject r x (x ∷ a)
    -- TOOD should probably drop `z`
    → (z : Id)
    → z ＝ r .fwd (last x a)
    → Σ[ t ꞉ List Id ] IsFullQTraject r x s t × Prefix (x ∷ a) t

  qtraject-body : (r : QRen) → (x : Id) → (s : LFSet Id)
                → ((s′ : LFSet Id) → sizeₛ s′ < sizeₛ s → qtraject-body-type r x s′)
                → qtraject-body-type r x s
  qtraject-body r x s ih ss ac art z za with z ≟ x
  qtraject-body r x s ih ss ac art z za | yes z=x =
      (x ∷ ac)
    , (art , inl (za ⁻¹ ∙ z=x))
    , prefix-refl
  qtraject-body r x s ih ss ac art z za | no z≠x with z ∈? s
  qtraject-body r x s ih ss ac art z za | no z≠x | yes z∈s =
    let aceq = ∷-tail-inj $ art .fst
        zeq =   za
              ∙ ap (λ q → r .fwd (last x q)) (art .fst)
              ∙ last-map {f = r .fwd} {xs = traj (r .fwd) (r .fwd x) (length ac)} ⁻¹
              ∙ ap (last (r .fwd x)) (traj-map {f = r .fwd} {n = length ac})
              ∙ traj-last {f = r .fwd} {x = r .fwd x} {n = length ac}
        (tr , (iqt , col) , pr) =
           ih (rem z s) (rem-size-neg z∈s)
                 (λ q∈ → ss (rem-∈ q∈ .snd))
                 (ac ∷r z)
                 ((ap (x ∷_) $
                     ap² _∷r_ aceq zeq
                   ∙ traj-snoc ⁻¹
                   ∙ ap (traj (r .fwd) (r .fwd x)) (snoc-length ac ⁻¹))
                  , uniq-snoc (art .snd .fst)
                      (contra
                        (subst (λ q → q ∈ (x ∷ ac) → q ＝ x)
                               (iter-swap 1 (length ac) (r .fwd) x ∙ zeq ⁻¹)
                               (iqt-next-loop {r = r} art))
                        z≠x)
                  , all-∷r (art .snd .snd) (ss z∈s))
                 (r .fwd z)
                 (ap (r .fwd) (last-snoc {xs = ac} ⁻¹))
        ple = prefix-length pr
      in
     tr
   , (  iqt
      , map-r (contra (rem-∈-≠ $
                         λ e →
                           iqt-next-0<-≠ {r = r} {k = suc (length ac)}
                              iqt
                              z<s
                              (<≃suc≤ $
                               subst (λ q → suc q ≤ length tr) (snoc-length ac) ple)
                              (  e
                               ∙ zeq
                               ∙ iter-swap (length ac) 1 (r .fwd) x)
                        ))
              col)
   , prefix-∷r-l pr
  qtraject-body r x s ih ss ac art z za | no z≠x | no z∉s  =
      (x ∷ ac)
    , (art , inr (subst (_∉ s)
                        (za ∙ ap (r .fwd)
                                 (  ap (last x) (∷-tail-inj (art .fst))
                                  ∙ traj-last {f = r .fwd} {x = x} {n = length ac}))
                        z∉s))
    , prefix-refl

  qtraject-aux : (r : QRen) → (x : Id) → Σ[ t ꞉ List Id ] IsFullQTraject r x (r .fdom) t
  qtraject-aux r x =
    Dec.rec
      (λ x∈ →
          let (tr , r , _) =
                to-induction
                  {A = LFSet Id}
                  (wf-lift sizeₛ <-is-wf)
                  (qtraject-body-type r x)
                  (qtraject-body r x)
                  (r .fdom)
                  id
                  []
                  (refl , false! ∷ᵘ []ᵘ , x∈ ∷ [])
                  (r .fwd x)
                  refl
           in
          tr , r)
     -- TODO can also be inr
     (λ x∉ → [] , (refl , []ᵘ , []) , inl (r. fcof x∉))
     (x ∈? r .fdom)

  qtraject : QRen → Id → List Id × Bool
  qtraject r x =
    let (tr , (_ , col)) = qtraject-aux r x in
    tr , is-inl? col

  qtraject-iqt : (r : QRen) → (x : Id) → IsQTraject r x (qtraject r x .fst)
  qtraject-iqt r x = qtraject-aux r x .snd .fst

  qtraject-¬cyc→lin : (r : QRen) → (x : Id)
                    → ¬ IsCycle r x (qtraject r x .fst)
                    → IsLinear r x (r .fdom) (qtraject r x .fst)
  qtraject-¬cyc→lin r x ncyc with qtraject-aux r x
  ... | tr , r , inl cy = absurd (ncyc cy)
  ... | tr , r , inr li = li

  -- the other direction doesn't hold because trajectory might be empty thus there's a trivial cycle

  qtraject-cyc : (r : QRen) → (x : Id)
               → if qtraject r x .snd then IsCycle r x (qtraject r x .fst)
                                      else IsLinear r x (r .fdom) (qtraject r x .fst)
  qtraject-cyc r x with qtraject-aux r x
  ... | tr , r , inl cy = cy
  ... | tr , r , inr li = li


-- completion

complete-≃ : QRen → Id ≃ Id
complete-≃ r =
  ≅→≃ $ make-iso to fro $ make-inverses (fun-ext re) (fun-ext se)
  where
  to : Id → Id
  to x = if x ∈ₛ? r .fdom
            then r .fwd x
            else r .bwd (last x (qtraject (qflp r) x .fst))
  fro : Id → Id
  fro x = if x ∈ₛ? r .bdom
             then r .bwd x
             else r .fwd (last x (qtraject r x .fst))
  re : ∀ x → to (fro x) ＝ x
  re x =
    Dec.elim
      {C = λ q → (if (if ⌊ q ⌋
                       then r .bwd x
                       else r .fwd (last x (qtraject r x .fst))) ∈ₛ? r .fdom
                     then r .fwd (if ⌊ q ⌋
                                    then r .bwd x
                                    else r .fwd (last x (qtraject r x .fst)))
                     else r .bwd (last (if ⌊ q ⌋
                                          then r .bwd x
                                          else r .fwd (last x (qtraject r x .fst)))
                                       (qtraject (qflp r) (if ⌊ q ⌋
                                                              then r .bwd x
                                                              else r .fwd (last x (qtraject r x .fst))) .fst))) ＝ x}
      (λ x∈b →
         let (bx∈f , fbx) = r .bcoh x∈b in
         given-yes bx∈f
            return (λ q → (if ⌊ q ⌋
                     then r .fwd (r .bwd x)
                     else r .bwd (last (r .bwd x) (qtraject (qflp r) (r .bwd x) .fst))) ＝ x)
            then fbx)
      (λ x∉b →
           let qiq = qtraject-iqt r x
               qiq′ = qtraject-iqt (qflp r) (r .fwd (last x (qtraject r x .fst)))
               qiq″ = iqt-flip {r = r} qiq
             in
           Dec.rec
             (λ x∈f →
                  let ncyc = contra (iqt-cyc-bdom {r = r} qiq x∈f) x∉b
                      isl = qtraject-¬cyc→lin r x ncyc
                      isln = lin→last∉ {r = r} qiq isl
                      isl′ = qtraject-¬cyc→lin (qflp r) (r .fwd (last x (qtraject r x .fst)))
                                 (contra (iqt-cyc-bdom {r = qflp r} qiq′
                                             (r .fcoh (all→last x∈f (qiq .snd .snd)) .fst))
                                         isln)
                      iqlb = iqt-lin-flip {r = r} qiq (ifqt-∈-0< {r = r} isl x∈f) x∉b
                      ee = traj-lin-flip-inj {r = qflp r}
                             (subst (λ q → All (_∈ r .bdom) q) (qiq′ .fst) (qiq′ .snd .snd))
                             (subst (λ q → All (_∈ r .bdom) q) (qiq″ .fst) (qiq″ .snd .snd))
                             (subst (IsLinear (qflp r) (r .fwd (last x (qtraject r x .fst))) (r .bdom)) (qiq′ .fst) isl′)
                             (subst (IsLinear (qflp r) (r .fwd (last x (qtraject r x .fst))) (r .bdom)) (qiq″ .fst) iqlb)
                     in
                  given-no isln
                     return (λ q → (if ⌊ q ⌋
                                      then r .fwd (r .fwd (last x (qtraject r x .fst)))
                                      else r .bwd (last (r .fwd (last x (qtraject r x .fst)))
                                                  (qtraject (qflp r) (r .fwd (last x (qtraject r x .fst))) .fst))) ＝ x)
                     then   ap (λ q → r .bwd (last (r .fwd (last x (qtraject r x .fst))) q)) (qiq′ .fst)
                          ∙ ap (λ q → r .bwd (last (r .fwd (last x (qtraject r x .fst))) (traj (r .bwd) (r .fwd (last x (qtraject r x .fst))) q))) ee
                          ∙ ap (λ q → r .bwd (last (r .fwd (last x (qtraject r x .fst))) q)) (qiq″ .fst ⁻¹)
                          -- TODO replace with iqt-cyc-aux
                          ∙ ap (r .bwd) (last-reverse {xs = map (r .fwd) (qtraject r x .fst)} ∙ head-map {xs = qtraject r x .fst})
                          ∙ ap (λ q → r .bwd (r .fwd q)) (head-last {xs = qtraject r x .fst})
                          ∙ r .fcoh (iqt-head-∈ {r = r} qiq x∈f) .snd
                          ∙ iqt-head {r = r} qiq)
             (λ x∉f →
                  let qte = iqt-z∉-[] {r = r} qiq x∉f
                      re = r .fcof x∉f
                      tbe = iqt-z∉-[] {r = qflp r}
                                 (subst (λ q → IsQTraject (qflp r) q (qtraject (qflp r) q .fst))
                                        (ap (λ q → r .fwd (last x q)) qte ∙ re)
                                        qiq′)
                                 x∉b
                    in
                    ap (λ q → if (r .fwd (last x q)) ∈ₛ? r .fdom
                                 then r .fwd (r .fwd (last x q))
                                 else r .bwd (last (r .fwd (last x q))
                                             (qtraject (qflp r) (r .fwd (last x q)) .fst))) qte
                  ∙ ap (λ q → if q ∈ₛ? r .fdom
                                 then r .fwd q
                                 else r .bwd (last q
                                             (qtraject (qflp r) q .fst))) re
                  ∙ if-false (not-so (contra so→true! x∉f))
                  ∙ ap (λ q → r .bwd (last x q)) tbe
                  ∙ r .bcof x∉b)
             (x ∈? r .fdom))
    (x ∈? r .bdom)
  se : ∀ x → fro (to x) ＝ x
  se x =
    Dec.elim
      {C = λ q → (if (if ⌊ q ⌋
                       then r .fwd x
                       else r .bwd (last x (qtraject (qflp r) x .fst))) ∈ₛ? r .bdom
                     then r .bwd (if ⌊ q ⌋
                                    then r .fwd x
                                    else r .bwd (last x (qtraject (qflp r) x .fst)))
                     else r .fwd (last (if ⌊ q ⌋
                                          then r .fwd x
                                          else r .bwd (last x (qtraject (qflp r) x .fst)))
                                       (qtraject r (if ⌊ q ⌋
                                                              then r .fwd x
                                                              else r .bwd (last x (qtraject (qflp r) x .fst))) .fst))) ＝ x}
      (λ x∈f →
         let (fx∈b , bfx) = r .fcoh x∈f in
         given-yes fx∈b
            return (λ q → (if ⌊ q ⌋
                     then r .bwd (r .fwd x)
                     else r .fwd (last (r .fwd x) (qtraject r (r .fwd x) .fst))) ＝ x)
            then bfx)
      (λ x∉f →
         let qiq = qtraject-iqt (qflp r) x
             qiq′ = qtraject-iqt r (r .bwd (last x (qtraject (qflp r) x .fst)))
             qiq″ =
                subst
                  (λ q → IsQTraject q (r .bwd (last x (qtraject (qflp r) x .fst)))
                                      (reverse (map (r .bwd) (qtraject (qflp r) x .fst))))
                  (qflp-inv {r = r})
                  (iqt-flip {r = qflp r} qiq)
           in
         Dec.rec
           (λ x∈b →
               let ncyc = contra (iqt-cyc-bdom {r = qflp r} qiq x∈b) x∉f
                   isl = qtraject-¬cyc→lin (qflp r) x ncyc
                   isln = lin→last∉ {r = qflp r} qiq isl
                   isl′ = qtraject-¬cyc→lin r (r .bwd (last x (qtraject (qflp r) x .fst)))
                              (contra (iqt-cyc-bdom {r = r} qiq′
                                        (r .bcoh (all→last x∈b (qiq .snd .snd)) .fst))
                                    isln)
                   iqlb = subst
                             (λ q → IsLinear q (r .bwd (last x (qtraject (qflp r) x .fst))) (r .fdom)
                                               (reverse (map (r .bwd) (qtraject (qflp r) x .fst))))
                             (qflp-inv {r = r})
                             (iqt-lin-flip {r = qflp r} qiq (ifqt-∈-0< {r = qflp r} isl x∈b) x∉f)
                   ee = traj-lin-flip-inj {r = r}
                             (subst (λ q → All (_∈ r .fdom) q) (qiq′ .fst) (qiq′ .snd .snd))
                             (subst (λ q → All (_∈ r .fdom) q) (qiq″ .fst) (qiq″ .snd .snd))
                             (subst (IsLinear r (r .bwd (last x (qtraject (qflp r) x .fst))) (r .fdom)) (qiq′ .fst) isl′)
                             (subst (IsLinear r (r .bwd (last x (qtraject (qflp r) x .fst))) (r .fdom)) (qiq″ .fst) iqlb)

                 in
              given-no isln
                 return (λ q → (if ⌊ q ⌋
                                  then r .bwd (r .bwd (last x (qtraject (qflp r) x .fst)))
                                  else r .fwd (last (r .bwd (last x (qtraject (qflp r) x .fst)))
                                              (qtraject r (r .bwd (last x (qtraject (qflp r) x .fst))) .fst))) ＝ x)
                 then
               (  ap (λ q → r .fwd (last (r .bwd (last x (qtraject (qflp r) x .fst))) q)) (qiq′ .fst)
                ∙ ap (λ q → r .fwd (last (r .bwd (last x (qtraject (qflp r) x .fst))) (traj (r .fwd) (r .bwd (last x (qtraject (qflp r) x .fst))) q))) ee
                ∙ ap (λ q → r .fwd (last (r .bwd (last x (qtraject (qflp r) x .fst))) q)) (qiq″ .fst ⁻¹)
                -- replace with iqt-cyc-aux
                ∙ ap (r .fwd) (last-reverse {xs = map (r .bwd) (qtraject (qflp r) x .fst)} ∙ head-map {xs = qtraject (qflp r) x .fst})
                ∙ ap (λ q → r .fwd (r .bwd q)) (head-last {xs = qtraject (qflp r) x .fst})
                ∙ r .bcoh (iqt-head-∈ {r = qflp r} qiq x∈b) .snd
                ∙ iqt-head {r = qflp r} qiq))

           (λ x∉b →
              let qte = iqt-z∉-[] {r = qflp r} qiq x∉b
                  re = r .bcof x∉b
                  tbe = iqt-z∉-[] {r = r}
                              (subst (λ q → IsQTraject r q (qtraject r q .fst))
                                     (ap (λ q → r .bwd (last x q)) qte ∙ re)
                                     qiq′)
                              x∉f
                 in
               ap (λ q → if (r .bwd (last x q)) ∈ₛ? r .bdom
                            then r .bwd (r .bwd (last x q))
                            else r .fwd (last (r .bwd (last x q))
                                        (qtraject r (r .bwd (last x q)) .fst))) qte
             ∙ ap (λ q → if q ∈ₛ? r .bdom
                            then r .bwd q
                            else r .fwd (last q
                                        (qtraject r q .fst))) re
             ∙ if-false (not-so (contra so→true! x∉b))
             ∙ ap (λ q → r .fwd (last x q)) tbe
             ∙ r .fcof x∉f)
           (x ∈? r .bdom))
    (x ∈? r .fdom)

complete : QRen → Ren
complete r .eqvr = complete-≃ r
complete r .supr = r .fdom ∪∷ r .bdom
complete r .cofr {x} x∉ =
  let (x∉f , x∉b) = ∉ₛ-∪∷ {xs = r .fdom} x∉ in
  given-no x∉f
     return (λ q → (if ⌊ q ⌋
                      then r .fwd x
                      else r .bwd (last x (qtraject (qflp r) x .fst))) ＝ x)
     then (ap (r .bwd)
              (ap (last x) (iqt-z∉-[] {r = qflp r}
                              (qtraject-iqt (qflp r) x)
                              x∉b))
          ∙ r .bcof x∉b)

-- compatibility

qcompat : QRen → QRen → 𝒰
qcompat s t =
    ((x : Id) → x ∈ s .fdom → x ∈ t .fdom → (s .fwd x) ＝ (t .fwd x))
  × ((x : Id) → x ∈ s .bdom → x ∈ t .bdom → (s .bwd x) ＝ (t .bwd x))

qcompat-∈-→ : ∀ {s t} {x : Id}
             → qcompat s t
             → x ∈ t .fdom
             → (t .fwd x) ∈ s .bdom
             → x ∈ s .fdom
qcompat-∈-→ {s} {t} {x} c x∈t tx∈s =
  let (tfx∈tb , ttx) = t .fcoh x∈t in
  subst (_∈ₛ s .fdom)
        (c .snd (t .fwd x) tx∈s tfx∈tb ∙ ttx)
        (s .bcoh tx∈s .fst)

qcompat-∈-← : ∀ {s t} {x : Id}
             → qcompat s t
             → x ∈ t .bdom
             → (t .bwd x) ∈ s .fdom
             → x ∈ s .bdom
qcompat-∈-← {s} {t} {x} c x∈t tx∈s =
  let (tbx∈tf , ttx) = t .bcoh x∈t in
  subst (_∈ₛ s .bdom)
        (c .fst (t .bwd x) tx∈s tbx∈tf ∙ ttx)
        (s .fcoh tx∈s .fst)

-- union

∪Q : (s t : QRen) → qcompat s t → QRen
∪Q s t c .fwd  z = if z ∈ₛ? s .fdom then s .fwd z else
                    if z ∈ₛ? t .fdom then t .fwd z else z
∪Q s t c .bwd  z = if z ∈ₛ? s .bdom then s .bwd z else
                     if z ∈ₛ? t .bdom then t .bwd z else z
∪Q s t c .fdom = s .fdom ∪∷ t .fdom
∪Q s t c .bdom = s .bdom ∪∷ t .bdom
∪Q s t c .fcoh {x = z} z∈∪ =
   Dec.elim
     {C = λ q →
       ((if ⌊ q ⌋ then s .fwd z else
         if z ∈ₛ? t .fdom then t .fwd z else z) ∈ (s .bdom ∪∷ t .bdom))
     × ((if (if ⌊ q ⌋ then s .fwd z else
             if z ∈ₛ? t .fdom then t .fwd z else z) ∈ₛ? s .bdom
           then s .bwd (if ⌊ q ⌋ then s .fwd z else
                        if z ∈ₛ? t .fdom then t .fwd z else z)
           else (if (if ⌊ q ⌋ then s .fwd z else
                     if z ∈ₛ? t .fdom then t .fwd z else z) ∈ₛ? t .bdom
                   then t .bwd (if ⌊ q ⌋ then s .fwd z else
                                if z ∈ₛ? t .fdom then t .fwd z else z)
                   else (if ⌊ q ⌋ then s .fwd z else
                         if z ∈ₛ? t .fdom then t .fwd z else z))) ＝ z)}
             (λ z∈sf →
                  let (sfz∈sb , sbsfz) = s .fcoh z∈sf in
                    (∈ₛ-∪∷←l sfz∈sb)
                  , (given-yes sfz∈sb
                       return (λ q → (if ⌊ q ⌋ then s .bwd (s .fwd z)
                                               else (if s .fwd z ∈ₛ? t .bdom then t .bwd (s .fwd z)
                                                                             else s .fwd z)) ＝ z)
                       then sbsfz))
             (λ z∉sf →
                 Dec.elim
                  {C = λ q →
                      ((if ⌊ q ⌋ then t .fwd z else z) ∈ (s .bdom ∪∷ t .bdom))
                    × ((if (if ⌊ q ⌋ then t .fwd z else z) ∈ₛ? s .bdom
                          then s .bwd (if ⌊ q ⌋ then t .fwd z else z)
                          else (if (if ⌊ q ⌋ then t .fwd z else z) ∈ₛ? t .bdom
                                  then t .bwd (if ⌊ q ⌋ then t .fwd z else z)
                                  else (if ⌊ q ⌋ then t .fwd z else z))) ＝ z)}
                 (λ z∈tf →
                      let (tfz∈tb , tbtfz) = t .fcoh z∈tf in
                        (∈ₛ-∪∷←r {s₁ = s .bdom} tfz∈tb)
                      , (given-no contra (qcompat-∈-→ {s = s} {t = t} c z∈tf) z∉sf
                           return (λ q → (if ⌊ q ⌋ then s .bwd (t .fwd z)
                                          else if t .fwd z ∈ₛ? t .bdom then t .bwd (t .fwd z)
                                                                       else t .fwd z) ＝ z)
                           then (given-yes tfz∈tb
                                   return (λ q → (if ⌊ q ⌋ then t .bwd (t .fwd z)
                                                           else t .fwd z) ＝ z)
                                   then tbtfz)))
                 (λ z∉tf → absurd (∪∷-∉ₛ z∉sf z∉tf z∈∪))
                 (z ∈? t .fdom))
             (z ∈? s .fdom)
∪Q s t c .bcoh {x = z} z∈∪ =
   Dec.elim
     {C = λ q →
       ((if ⌊ q ⌋ then s .bwd z else
         if z ∈ₛ? t .bdom then t .bwd z else z) ∈ (s .fdom ∪∷ t .fdom))
     × ((if (if ⌊ q ⌋ then s .bwd z else
             if z ∈ₛ? t .bdom then t .bwd z else z) ∈ₛ? s .fdom
           then s .fwd (if ⌊ q ⌋ then s .bwd z else
                        if z ∈ₛ? t .bdom then t .bwd z else z)
           else (if (if ⌊ q ⌋ then s .bwd z else
                     if z ∈ₛ? t .bdom then t .bwd z else z) ∈ₛ? t .fdom
                   then t .fwd (if ⌊ q ⌋ then s .bwd z else
                                if z ∈ₛ? t .bdom then t .bwd z else z)
                   else (if ⌊ q ⌋ then s .bwd z else
                         if z ∈ₛ? t .bdom then t .bwd z else z))) ＝ z)}
             (λ z∈sb →
                  let (sfz∈sf , sfsbz) = s .bcoh z∈sb in
                    (∈ₛ-∪∷←l sfz∈sf)
                  , (given-yes sfz∈sf
                       return (λ q → (if ⌊ q ⌋ then s .fwd (s .bwd z)
                                               else (if s .bwd z ∈ₛ? t .fdom then t .fwd (s .bwd z)
                                                                             else s .bwd z)) ＝ z)
                       then sfsbz))
             (λ z∉sb →
                 Dec.elim
                  {C = λ q →
                      ((if ⌊ q ⌋ then t .bwd z else z) ∈ (s .fdom ∪∷ t .fdom))
                    × ((if (if ⌊ q ⌋ then t .bwd z else z) ∈ₛ? s .fdom
                          then s .fwd (if ⌊ q ⌋ then t .bwd z else z)
                          else (if (if ⌊ q ⌋ then t .bwd z else z) ∈ₛ? t .fdom
                                  then t .fwd (if ⌊ q ⌋ then t .bwd z else z)
                                  else (if ⌊ q ⌋ then t .bwd z else z))) ＝ z)}
                 (λ z∈tb →
                      let (tbz∈tf , tftbz) = t .bcoh z∈tb in
                        (∈ₛ-∪∷←r {s₁ = s .fdom} tbz∈tf)
                      , (given-no contra (qcompat-∈-← {s = s} {t = t} c z∈tb) z∉sb
                           return (λ q → (if ⌊ q ⌋ then s .fwd (t .bwd z)
                                          else if t .bwd z ∈ₛ? t .fdom then t .fwd (t .bwd z)
                                                                       else t .bwd z) ＝ z)
                           then (given-yes tbz∈tf
                                   return (λ q → (if ⌊ q ⌋ then t .fwd (t .bwd z)
                                                           else t .bwd z) ＝ z)
                                   then tftbz))
                                   )
                 (λ z∉tb → absurd (∪∷-∉ₛ z∉sb z∉tb z∈∪))
                 (z ∈? t .bdom))
             (z ∈? s .bdom)
∪Q s t c .fcof {x = z} z∉ =
  let (z∉s , z∉t) = ∉ₛ-∪∷ {xs = s .fdom} z∉ in
  given-no z∉s
     return (λ q → (if ⌊ q ⌋ then s .fwd z
                    else if z ∈ₛ? t .fdom then t .fwd z else z) ＝ z)
     then (given-no z∉t
            return (λ q → (if ⌊ q ⌋ then t .fwd z else z) ＝ z)
            then refl)
∪Q s t c .bcof {x = z} z∉ =
  let (z∉s , z∉t) = ∉ₛ-∪∷ {xs = s .bdom} z∉ in
  given-no z∉s
     return (λ q → (if ⌊ q ⌋ then s .bwd z
                    else if z ∈ₛ? t .bdom then t .bwd z else z) ＝ z)
     then (given-no z∉t
            return (λ q → (if ⌊ q ⌋ then t .bwd z else z) ＝ z)
            then refl)
