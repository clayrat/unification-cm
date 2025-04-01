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
open import Data.Vec.Inductive as Vec
open import Data.Vec.Inductive.Correspondences.Unary.All
open import Data.Vec.Inductive.Operations
open import Data.Vec.Inductive.Operations.Properties

open import Id
open import NominalN.Term

private variable
  ℓᵃ ℓᵇ ℓᶜ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ

tm-sizes : {@0 n : ℕ} → Vec Term n → ℕ
tm-sizes = Vec.rec 0 λ t → tm-size t +_

-- unvar

is-var : Term → Bool
is-var (`` _) = true
is-var _      = false

unvar : Term → Maybe Id
unvar (`` x) = just x
unvar _      = nothing

unvar-just : {t : Term} {x : Id}
           → unvar t ＝ just x
           → t ＝ `` x
unvar-just {t = `` x} e = ap ``_ (just-inj e)
unvar-just {t = _ ⟶ _} e = false! e
unvar-just {t = con _} e = false! e

unvar-nothing : {t : Term}
              → unvar t ＝ nothing
              → ∀ {x} → t ≠ `` x
unvar-nothing {t = `` x}    e = false! e
unvar-nothing {t = _ ⟶ _} _ = false!
unvar-nothing {t = con _}   _ = false!

Reflects-unvar : {t : Term}
               → Reflects (Σ[ x ꞉ Id ] (t ＝ `` x)) (is-just? (unvar t))
Reflects-unvar {t} with unvar t | recall unvar t
... | just x | ⟪ eq ⟫ = ofʸ (x , unvar-just eq)
... | nothing | ⟪ eq ⟫ = ofⁿ λ where (x , e) → unvar-nothing eq e

Dec-unvar : {t : Term}
          → Dec (Σ[ x ꞉ Id ] (t ＝ `` x))
Dec-unvar {t} .does = is-just? (unvar t)
Dec-unvar     .proof = Reflects-unvar

-- unreplicate

unreplicate : {@0 n : ℕ} → Vec Term n → Maybe Term
unreplicate []       = nothing
unreplicate (t ∷ ts) = if all (_==tm t) ts then just t else nothing

unreplicate-just : {n : ℕ} {z : Term} {ts : Vec Term n}
                 → unreplicate ts ＝ just z
                 → ts ＝ replicate n z
unreplicate-just {n = 0}         {ts = []}     e = false! e
unreplicate-just {n = suc n} {z} {ts = t ∷ ts} e with all (_==tm t) ts | recall (all (_==tm t)) ts
... | true | ⟪ eq ⟫ =
  let t=z = just-inj e in
  ap² {C = λ _ _ → Vec _ (suc _)} _∷_ t=z $
  All-replicate ts $
  all-map (λ x=t → x=t ∙ t=z) $
  so→true! ⦃ Reflects-all {xs = ts} λ w → tm-eq-reflects {x = w} {y = t} ⦄ $ so≃is-true ⁻¹ $ eq
... | false | _ = false! e

unreplicate-nothing : {n : ℕ} {ts : Vec Term n}
                    → 0 < n
                    → unreplicate ts ＝ nothing
                    → ∀ {z} → ts ≠ replicate n z
unreplicate-nothing {n = zero}  {ts = []}     lt e = false! lt
unreplicate-nothing {n = suc n} {ts = t ∷ ts} lt e {z} with all (_==tm t) ts | recall (all (_==tm t)) ts
... | true  | eq = false! e
... | false | ⟪ eq ⟫ with t ≟ z
...   | yes t=z =
  contra
    (λ e →
        true→so! ⦃ Reflects-all {xs = ts} λ w → tm-eq-reflects {x = w} {y = t} ⦄ $
        subst (λ xs → All (_＝ t) xs) (∷-tail-inj e ⁻¹) $
        subst (λ q → All (_＝ t) (replicate n q)) t=z $
        replicate-all n)
  (¬so≃is-false ⁻¹ $ eq)
...   | no  t≠z = contra (∷-head-inj) t≠z

Reflects-unreplicate : {n : ℕ} {ts : Vec Term n}
                     → 0 < n
                     → Reflects (Σ[ x ꞉ Term ] (ts ＝ replicate n x)) (is-just? (unreplicate ts))
Reflects-unreplicate {ts} lt with unreplicate ts | recall unreplicate ts
... | just x | ⟪ eq ⟫ =
  ofʸ (x , unreplicate-just eq)
... | nothing | ⟪ eq ⟫ =
  ofⁿ λ where (x , e) →
                unreplicate-nothing lt eq e

Dec-unreplicate : {n : ℕ} {ts : Vec Term n}
                → 0 < n
                → Dec (Σ[ x ꞉ Term ] (ts ＝ replicate n x))
Dec-unreplicate {ts} lt .does = is-just? (unreplicate ts)
Dec-unreplicate {ts} lt .proof = Reflects-unreplicate lt

-- uncouple

is-⟶ : Term → Bool
is-⟶ (p ⟶ q) = true
is-⟶ _        = false

⟶-split : Term → Maybe (Term × Term)
⟶-split (p ⟶ q) = just (p , q)
⟶-split _        = nothing

⟶-split=just : ∀ {t p q}
               → ⟶-split t ＝ just (p , q)
               → t ＝ p ⟶ q
⟶-split=just {t = `` _} e = false! e
⟶-split=just {t = p′ ⟶ q′} e =
  let pqeq = ×-path-inv $ just-inj e in
  ap² _⟶_ (pqeq .fst) (pqeq .snd)
⟶-split=just {t = con _} e = false! e

Reflects-⟶ : ∀ {t}
             → Reflects (Σ[ (p , q) ꞉ Term × Term ] (t ＝ p ⟶ q)) (is-⟶ t)
Reflects-⟶ {t = `` _} = ofⁿ λ where ((p , q) , e) → false! e
Reflects-⟶ {t = p ⟶ q} = ofʸ ((p , q) , refl)
Reflects-⟶ {t = con _} = ofⁿ λ where ((p , q) , e) → false! e

couple : {@0 n : ℕ} → Vec Term n → Vec Term n → Vec Term n
couple = zip-with _⟶_

uncouple : {@0 n : ℕ} → Vec Term n → Maybe (Vec Term n × Vec Term n)
uncouple = map unzip ∘ traverse ⟶-split

uncouple-[] : uncouple [] ＝ just ([] , [])
uncouple-[] = refl

uncouple-nothing-size : {n : ℕ} {ts : Vec Term n}
                      → uncouple ts ＝ nothing
                      → 0 < n
uncouple-nothing-size {n = zero} {ts = []} e = false! e
uncouple-nothing-size {n = suc n}          _ = z<s

-- TODO how to make these less adhoc?
-- extract an induction principle?
traverse-sizes : {@0 n : ℕ} {ts : Vec Term n} {pqs : Vec (Term × Term) n}
               → vec-traverse ⟶-split ts ＝ just pqs
               → let (ps , qs) = unzip pqs in
                 (tm-sizes ps ≤ tm-sizes ts)
               × (tm-sizes qs ≤ tm-sizes ts)
traverse-sizes {ts = []}                           e =
  let e′ = just-inj e in
    subst (λ q → tm-sizes (unzip q .fst) ≤ 0) e′ z≤
  , subst (λ q → tm-sizes (unzip q .snd) ≤ 0) e′ z≤
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

uncouple-sizes : {@0 n : ℕ} {ts ps qs : Vec Term n}
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

traverse-couple : {@0 n : ℕ} {xs ys : Vec Term n}
                  → Σ[ zs ꞉ Vec (Term × Term) n ] (vec-traverse ⟶-split (couple xs ys) ＝ just zs)
                                              × (unzip zs ＝ (xs , ys))
traverse-couple {xs = []}     {ys = []}     = [] , refl , refl
traverse-couple {xs = x ∷ xs} {ys = y ∷ ys} =
  let (zs , ej , eu) = traverse-couple {xs = xs} {ys = ys}
      (ex , ey) = ×-path-inv eu
    in
    (x , y) ∷ zs
  , ap (mapₘ ((x , y) ∷_)) ej
  , ×-path (ap (x ∷_) ex) (ap (y ∷_) ey)

couple-traverse : {@0 n : ℕ} {ts : Vec Term n} {zs : Vec (Term × Term) n}
                → vec-traverse ⟶-split ts ＝ just zs
                → let (xs , ys) = unzip zs in
                  couple xs ys ＝ ts
couple-traverse {ts = []} {zs = zs} e =
    let (pe , qe) = ×-path-inv (ap unzip (just-inj e)) in
    ap² couple (pe ⁻¹) (qe ⁻¹)
couple-traverse {ts = t ∷ ts} {zs = (x , y) ∷ zs} e =
  let ((p′ , q′) , xs , steq , treq , ceq) = map²ₘ=just {f = _∷_} {ma = ⟶-split t} e
      pqeq = ×-path-inv $ ∷-head-inj ceq
   in
  ap² {C = λ _ _ → Vec _ (suc _)} _∷_
    (ap² _⟶_ (pqeq .fst ⁻¹) (pqeq .snd ⁻¹) ∙ ⟶-split=just steq ⁻¹)
    (couple-traverse {ts = ts} {zs = zs} (treq ∙ ap just (∷-tail-inj ceq)))

couple-uncouple : {@0 n : ℕ} {ts xs ys : Vec Term n}
                → uncouple ts ＝ just (xs , ys)
                → couple xs ys ＝ ts
couple-uncouple {ts} {xs} {ys}  e =
  let (xys , e′ , ue) = mapₘ=just e
      (xe , ye) = ×-path-inv (ue ⁻¹)
    in
    ap² couple xe ye ∙ couple-traverse {ts = ts} {zs = xys} e′

uncouple-couple : {@0 n : ℕ} {xs ys : Vec Term n}
                → uncouple (couple xs ys) ＝ just (xs , ys)
uncouple-couple =
  let (zs , ej , eu) = traverse-couple in
  ap (map unzip) ej ∙ ap just eu

uncouple-∷ : ∀ {@0 n : ℕ} {t p q} {ts ps qs : Vec Term n}
           → uncouple (t ∷ ts) ＝ just (p ∷ ps , q ∷ qs)
           → (t ＝ p ⟶ q) × (uncouple ts ＝ just (ps , qs))
uncouple-∷ {t} {ts} e =
  let e′ = couple-uncouple {ts = t ∷ ts} e ⁻¹ in
    (∷-head-inj e′)
  , ap uncouple (∷-tail-inj e′) ∙ uncouple-couple

uncouple-sizes>0 : {n : ℕ} {ts ps qs : Vec Term n}
                 → 0 < n
                 → uncouple ts ＝ just (ps , qs)
                 → (tm-sizes ps < tm-sizes ts)
                 × (tm-sizes qs < tm-sizes ts)
uncouple-sizes>0 {n = zero}                                           lt _ = false! lt
uncouple-sizes>0 {n = suc n} {ts = t ∷ ts} {ps = p ∷ ps} {qs = q ∷ qs} _ e =
  let (et , ets) = uncouple-∷ {t = t} {ts = ts} e
      (psz , qsz) = uncouple-sizes {ts = ts} ets
    in
    <-≤-+ (<-≤-trans (<-≤-trans <-ascend ≤-+-r) (=→≤ (ap tm-size (et ⁻¹)))) psz
  , <-≤-+ (<-≤-trans <-+-lr (=→≤ (ap tm-size (et ⁻¹)))) qsz
