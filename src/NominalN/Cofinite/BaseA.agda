{-# OPTIONS --safe #-}
module NominalN.Cofinite.BaseA where

open import Prelude
open import Meta.Effect
open import Meta.Effect.Traversable

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.String
open import Data.Maybe as Maybe
open import Data.Maybe.Instances.Map.Properties
open import Data.Maybe.Instances.Idiom.Properties
open import Data.List as List
open import Data.List.Correspondences.Unary.All
open import Data.List.Operations.Properties

open import Id
open import NominalN.Term

private variable
  ℓᵃ ℓᵇ ℓᶜ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ

couple : List Term → List Term → List Term
couple = zip-with _⟶_

uncouple : List Term → Maybe (List Term × List Term)
uncouple = map unzip ∘ traverse ⟶-split

uncouple1 : Term → List Term → Maybe ((Term × List Term) × (Term × List Term))
uncouple1 (p ⟶ q) ts =
  map (λ where (ps , qs) → (p , ps) , (q , qs)) $ uncouple ts
uncouple1 _         _ = nothing

tm-sizes : List Term → ℕ
tm-sizes = List.rec 0 λ t → tm-size t +_

uncouple-[] : uncouple [] ＝ just ([] , [])
uncouple-[] = refl

uncouple-nothing-size : ∀ {ts}
                      → uncouple ts ＝ nothing
                      → 0 < length ts
uncouple-nothing-size e =
  ≱→< λ le → false! $ e ⁻¹ ∙ ap uncouple (length=0→nil $ ≤0→=0 le)

-- TODO how to make these less adhoc?
-- extract an induction principle?
traverse-sizes : ∀ {ts} {pqs : List (Term × Term)}
               → list-traverse ⟶-split ts ＝ just pqs
               → let (ps , qs) = unzip pqs in
                 (tm-sizes ps ≤ tm-sizes ts)
               × (tm-sizes qs ≤ tm-sizes ts)
traverse-sizes {ts = []}                           e =
  let e′ = just-inj e in
    subst (λ q → tm-sizes (unzip q .fst) ≤ 0) e′ z≤
  , subst (λ q → tm-sizes (unzip q .snd) ≤ 0) e′ z≤
traverse-sizes {ts = t ∷ ts} {pqs = []}            e =
  let ((p′ , q′) , xs , _ , _ , ceq) = map²ₘ=just {f = _∷_} {ma = ⟶-split t} e in
  false! ceq
traverse-sizes {ts = t ∷ ts} {pqs = (p , q) ∷ pqs} e =
  let ((p′ , q′) , xs , steq , treq , ceq) = map²ₘ=just {f = _∷_} {ma = ⟶-split t} e
      teq = ⟶-split=just steq
      (ps≤ , qs≤) = traverse-sizes {ts = ts} {pqs = pqs} (treq ∙ ap just (∷-tail-inj ceq))
      pqeq = ×-path-inv $ ∷-head-inj ceq
   in
    ≤-+ (subst (λ w → tm-size p ≤ tm-size w)
               (teq ⁻¹)
               (≤-ascend ∙ s≤s (=→≤ (ap tm-size (pqeq .fst ⁻¹)) ∙ ≤-+-r)))
        ps≤
  , ≤-+ (subst (λ w → tm-size q ≤ tm-size w)
               (teq ⁻¹)
               (≤-ascend ∙ s≤s (=→≤ (ap tm-size (pqeq .snd ⁻¹)) ∙ ≤-+-l)))
        qs≤

uncouple-sizes : ∀ {ts ps qs}
               → uncouple ts ＝ just (ps , qs)
               → (tm-sizes ps ≤ tm-sizes ts)
               × (tm-sizes qs ≤ tm-sizes ts)
uncouple-sizes {ts} e =
  let (pqs , meq , eq) = mapₘ=just e
      treq = traverse-sizes {ts = ts} meq
      (pseq , qseq) = ×-path-inv eq
    in
    =→≤ (ap tm-sizes (pseq ⁻¹)) ∙ treq .fst
  , =→≤ (ap tm-sizes (qseq ⁻¹)) ∙ treq .snd

{-
all→traverse : ∀ {ts}
             → All (λ t → Σ[ (p , q) ꞉ (Term × Term) ] (t ＝ p ⟶ q)) ts
             → Σ[ zs ꞉ List (Term × Term) ]   (list-traverse ⟶-split ts ＝ just zs)
                                            × (unzip zs ＝ (xs , ys))
all→traverse = ?
-}

traverse-couple : ∀ {xs ys}
                  → length xs ＝ length ys
                  → Σ[ zs ꞉ List (Term × Term) ] (list-traverse ⟶-split (couple xs ys) ＝ just zs)
                                              × (unzip zs ＝ (xs , ys))
traverse-couple {xs = []}     {ys = []}     e = [] , refl , refl
traverse-couple {xs = []}     {ys = y ∷ ys} e = false! e
traverse-couple {xs = x ∷ xs} {ys = []}     e = false! e
traverse-couple {xs = x ∷ xs} {ys = y ∷ ys} e =
  let (zs , ej , eu) = traverse-couple {xs = xs} {ys = ys} (suc-inj e)
      (ex , ey) = ×-path-inv eu
    in
    (x , y) ∷ zs
  , ap (mapₘ ((x , y) ∷_)) ej
  , ×-path (ap (x ∷_) ex) (ap (y ∷_) ey)

couple-traverse : ∀ {ts zs}
                → list-traverse ⟶-split ts ＝ just zs
                → let (xs , ys) = unzip zs in
                  (couple xs ys ＝ ts) × (length xs ＝ length ys)
couple-traverse {ts = []} {zs = zs} e =
    let (pe , qe) = ×-path-inv (ap unzip (just-inj e)) in
    ap² couple (pe ⁻¹) (qe ⁻¹)
  , ap length (pe ⁻¹ ∙ qe)
couple-traverse {ts = t ∷ ts} {zs = []} e =
  let ((p′ , q′) , xs , _ , _ , ceq) = map²ₘ=just {f = _∷_} {ma = ⟶-split t} e in
  false! ceq
couple-traverse {ts = t ∷ ts} {zs = (x , y) ∷ zs} e =
  let ((p′ , q′) , xs , steq , treq , ceq) = map²ₘ=just {f = _∷_} {ma = ⟶-split t} e
      teq = ⟶-split=just steq
      (ihc , ihl) = couple-traverse {ts = ts} {zs = zs} (treq ∙ ap just (∷-tail-inj ceq))
      pqeq = ×-path-inv $ ∷-head-inj ceq
   in
    ap² {C = λ _ _ → List Term} _∷_ (ap² _⟶_ (pqeq .fst ⁻¹) (pqeq .snd ⁻¹) ∙ teq ⁻¹) ihc
  , ap suc ihl

{-
traverse-eqlen : ∀ {ts} {pqs : List (Term × Term)}
               → list-traverse ⟶-split ts ＝ just pqs
               → let (ps , qs) = unzip pqs in
                 length ps ＝ length qs
traverse-eqlen {ts = []} e =
  let (pe , qe) = ×-path-inv (ap unzip (just-inj e)) in
  ap length (pe ⁻¹ ∙ qe)
traverse-eqlen {ts = t ∷ ts} {pqs = []} e =
  let ((p′ , q′) , xs , _ , _ , ceq) = map²ₘ=just {f = _∷_} {ma = ⟶-split t} e in
  false! ceq
traverse-eqlen {ts = t ∷ ts} {pqs = x ∷ pqs} e =
  let ((p′ , q′) , xs , steq , treq , ceq) = map²ₘ=just {f = _∷_} {ma = ⟶-split t} e
      teq = ⟶-split=just steq
      pqeq = ×-path-inv $ ∷-head-inj ceq
   in
  ap suc (traverse-eqlen {ts = ts} (treq ∙ ap just (∷-tail-inj ceq)))

couple-traverse : ∀ {ts zs}
                → list-traverse ⟶-split ts ＝ just zs
                → let (xs , ys) = unzip zs in
                couple xs ys ＝ ts
couple-traverse {ts = []} {zs = zs} e =
  ap (λ q → couple (unzip q .fst) (unzip q .snd)) (just-inj e ⁻¹)
couple-traverse {ts = t ∷ ts} {zs = []} e =
  let ((p′ , q′) , xs , _ , _ , ceq) = map²ₘ=just {f = _∷_} {ma = ⟶-split t} e in
  false! ceq
couple-traverse {ts = t ∷ ts} {zs = (x , y) ∷ zs} e =
  let ((p′ , q′) , xs , steq , treq , ceq) = map²ₘ=just {f = _∷_} {ma = ⟶-split t} e
      teq = ⟶-split=just steq
      ih = couple-traverse {ts = ts} {zs = zs} (treq ∙ ap just (∷-tail-inj ceq))
      pqeq = ×-path-inv $ ∷-head-inj ceq
   in
  ap² {C = λ _ _ → List Term} _∷_ (ap² _⟶_ (pqeq .fst ⁻¹) (pqeq .snd ⁻¹) ∙ teq ⁻¹) ih
-}

couple-uncouple : ∀ {ts xs ys}
                → uncouple ts ＝ just (xs , ys)
                → (couple xs ys ＝ ts) × (length xs ＝ length ys)
couple-uncouple {ts} {xs} {ys}  e =
  let (xys , e′ , ue) = mapₘ=just e
      (xe , ye) = ×-path-inv (ue ⁻¹)
      (xye , xyl) = couple-traverse {ts = ts} {zs = xys} e′
    in
    ap² couple xe ye ∙ xye
  , ap length xe ∙ xyl ∙ ap length ye ⁻¹

uncouple-couple : ∀ {xs ys}
                → length xs ＝ length ys
                → uncouple (couple xs ys) ＝ just (xs , ys)
uncouple-couple e =
  let (zs , ej , eu) = traverse-couple e in
  ap (map unzip) ej ∙ ap just eu

{-
Reflects-uncouple : ∀ {ts}
                  → Reflects (Σ[ (xs , ys) ꞉ (List Term × List Term) ] (uncouple ts ＝ just (xs , ys)))
                             (all is-⟶ ts)
Reflects-uncouple {ts} =
  Reflects.dmap
    ({!!})
    {!!}
    (Reflects-all {xs = ts} {p = is-⟶} λ t → Reflects-⟶ {t = t})
-}

-- uncouple1

uncouple1-sizes : ∀ {t ts p ps q qs}
               → uncouple1 t ts ＝ just ((p , ps) , (q , qs))
               → (tm-sizes (p ∷ ps) < tm-sizes (t ∷ ts))
               × (tm-sizes (q ∷ qs) < tm-sizes (t ∷ ts))
uncouple1-sizes {t = `` _}           e = false! e
uncouple1-sizes {t = p′ ⟶ q′} {ts} {p} {q} e =
  let (pqs , meq , eq) = mapₘ=just e
      (ppseq , qqseq) = ×-path-inv eq
      (peq , pseq) = ×-path-inv ppseq
      (qeq , qseq) = ×-path-inv qqseq
      (psz , qsz) = uncouple-sizes {ts = ts} (meq ∙ ap just (×-path pseq qseq))
    in
    <-≤-+ (<-+-r (subst (λ w → tm-size p < 1 + tm-size w) (peq ⁻¹) <-ascend)) psz
  , <-≤-+ (≤-<-trans (=→≤ (ap tm-size (qeq ⁻¹))) (<-+-0lr z<s)) qsz
uncouple1-sizes {t = con _}    e = false! e

-- unreplicate

unreplicate : List Term → Maybe Id
unreplicate [] = nothing
unreplicate ((`` x) ∷ ts) = if all (_==tm (`` x)) ts then just x else nothing
unreplicate (_ ∷ ts) = nothing

unreplicate-just : ∀ {x ts}
                 → unreplicate ts ＝ just x
                 → ts ＝ replicate (length ts) (`` x)
unreplicate-just     {ts = []}            e = false! e
unreplicate-just {x} {ts = (`` y) ∷ ts}   e with all (_==tm (`` y)) ts | recall (all (_==tm (`` y))) ts
... | true | ⟪ eq ⟫ =
  let e′ = just-inj e in
   ap² {C = λ _ _ → List Term} _∷_ (ap ``_ e′) $
   All-replicate ts $
   all-map (λ e → e ∙ ap ``_ e′) $
   so→true! ⦃ Reflects-all {xs = ts} λ t → tm-eq-reflects {x = t} {y = `` y} ⦄ $ so≃is-true ⁻¹ $ eq
... | false | _ = false! e
unreplicate-just     {ts = (_ ⟶ _) ∷ ts} e = false! e
unreplicate-just     {ts = con _ ∷ ts}     e = false! e

unreplicate-nothing : ∀ {ts}
                    → unreplicate ts ＝ nothing
                    → 0 < length ts
                    → ∀ {x} → ts ≠ replicate (length ts) (`` x)
unreplicate-nothing {ts = []} _ lt = false! lt
unreplicate-nothing {ts = (`` y) ∷ ts} e _ {x} with all (_==tm (`` y)) ts | recall (all (_==tm (`` y))) ts
... | true  | eq = false! e
... | false | ⟪ eq ⟫ with y ≟ x
...   | yes y=x =
  contra
    (λ e →
        true→so! ⦃ Reflects-all {xs = ts} λ t → tm-eq-reflects {x = t} {y = `` y} ⦄ $
        subst (λ xs → All (_＝ (`` y)) xs) (∷-tail-inj e ⁻¹) $
        subst (λ q → All (_＝ (`` y)) (replicate (length ts) (`` q))) y=x $
        replicate-all (length ts))
  (¬so≃is-false ⁻¹ $ eq)
...   | no  y≠x = contra (``-inj ∘ ∷-head-inj) y≠x
unreplicate-nothing {ts = (_ ⟶ _) ∷ ts} e _ = false! ⦃ Reflects-List-≠-head ⦄
unreplicate-nothing {ts = con _ ∷ ts} e _ = false! ⦃ Reflects-List-≠-head ⦄

Reflects-unreplicate : ∀ {ts}
                     → 0 < length ts
                     → Reflects (Σ[ x ꞉ Id ] (ts ＝ replicate (length ts) (`` x))) (is-just? (unreplicate ts))
Reflects-unreplicate {ts} lt with unreplicate ts | recall unreplicate ts
... | just x | ⟪ eq ⟫ =
  ofʸ (x , unreplicate-just eq)
... | nothing | ⟪ eq ⟫ =
  ofⁿ λ where (x , e) →
                unreplicate-nothing eq lt e

Dec-unreplicate : ∀ {ts}
                → 0 < length ts
                → Dec (Σ[ x ꞉ Id ] (ts ＝ replicate (length ts) (`` x)))
Dec-unreplicate {ts} lt .does = is-just? (unreplicate ts)
Dec-unreplicate {ts} lt .proof = Reflects-unreplicate lt
