{-# OPTIONS --safe #-}
module NominalN.Cofinite.BaseA where

open import Prelude
open import Meta.Effect
open import Meta.Effect.Traversable

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Acc
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Sum
open import Data.String
open import Data.Maybe as Maybe
open import Data.Maybe.Instances.Map.Properties
open import Data.Maybe.Instances.Idiom.Properties
open import Data.Vec.Inductive as Vec
open import Data.Vec.Inductive.Correspondences.Unary.All
open import Data.Vec.Inductive.Operations
open import Data.Vec.Inductive.Operations.Properties

open import LFSet
open import LFSet.Membership
open import LFSet.Discrete

open import Id
open import NominalN.Term

private variable
  ℓᵃ ℓᵇ ℓᶜ : Level
  A : 𝒰 ℓᵃ
  B : 𝒰 ℓᵇ
  C : 𝒰 ℓᶜ

tm-sizes : {@0 n : ℕ} → Vec Term n → ℕ
tm-sizes = Vec.rec 0 λ t → tm-size t +_

-- TODO REWRITE WITH FIBERS?

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

just-unreplicate : {n : ℕ} {z : Term}
                 → 0 < n
                 → unreplicate (replicate n z) ＝ just z
just-unreplicate {n = zero} lt = false! lt
just-unreplicate {n = suc n} {z} _ =
  if-true {b = all (_==tm z) (replicate n z)} $
  true→so! ⦃ Reflects-all {xs = replicate n z} λ w → tm-eq-reflects {x = w} ⦄ $
  replicate-all n

unreplicate-nothing : {n : ℕ} {ts : Vec Term n}
                    → 0 < n
                    → unreplicate ts ＝ nothing
                    → ∀ {z} → ts ≠ replicate n z
unreplicate-nothing {n = zero}  {ts = []}     lt e = false! lt
unreplicate-nothing {n = suc n} {ts = t ∷ ts} lt e {z} with all (_==tm t) ts | recall (all (_==tm t)) ts
... | true  | _ = false! e
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

-- unrepvar

unrepvar : ∀ {n} → Vec Term n → Maybe Id
unrepvar = unreplicate >=> unvar

unrepvar-just : ∀ {n} {ts : Vec Term n} {x : Id}
              → unrepvar ts ＝ just x
              → Σ[ t ꞉ Term ] (unreplicate ts ＝ just t) × (unvar t ＝ just x)
unrepvar-just {ts} e with unreplicate ts
unrepvar-just e | just t = t , refl , e
unrepvar-just e | nothing = false! e

unrepvar-just-eq : ∀ {n} {ts : Vec Term n} {x : Id}
                 → unrepvar ts ＝ just x
                 → ts ＝ replicate n (`` x)
unrepvar-just-eq {ts} eq =
  let (t , e1 , e2) = unrepvar-just {ts = ts} eq in
  unreplicate-just (e1 ∙ ap just (unvar-just e2))

unrepvar-nothing : ∀ {n} {ts : Vec Term n}
                 → unrepvar ts ＝ nothing
                 → (unreplicate ts ＝ nothing) ⊎ (Σ[ t ꞉ Term ] (unreplicate ts ＝ just t) × (unvar t ＝ nothing))
unrepvar-nothing {ts} e with unreplicate ts
unrepvar-nothing {ts} e | just t = inr (t , refl , e)
unrepvar-nothing {ts} e | nothing = inl refl

nothing-unrep-unrepvar : ∀ {n} {ts : Vec Term n}
                       → unreplicate ts ＝ nothing
                       → unrepvar ts ＝ nothing
nothing-unrep-unrepvar = ap (_>>= unvar)

{-
Reflects-unrepvar : {n : ℕ} {ts : Vec Term n}
                  → 0 < n
                  → Reflects (Σ[ x ꞉ Id ] (ts ＝ replicate n (`` x))) (is-just? (unrepvar ts))
Reflects-unrepvar {ts} lt with unrepvar ts | recall unrepvar ts
... | just x  | ⟪ eq ⟫ =
  let (t , e1 , e2) = unrepvar-just {ts = ts} eq in
  ofʸ (x , unreplicate-just (e1 ∙ ap just (unvar-just e2)))
... | nothing | ⟪ eq ⟫ =
  ofⁿ λ where (x , e) →
                [ (λ un → false! $ un ⁻¹ ∙ ap unreplicate e ∙ just-unreplicate lt)
                , (λ where (t , ue , uvn) →
                              let te = just-inj $ ue ⁻¹ ∙ ap unreplicate e ∙ just-unreplicate lt in
                              false! (uvn ⁻¹ ∙ ap unvar te))
                ]ᵤ (unrepvar-nothing {ts = ts} eq)

Dec-unrepvar : {n : ℕ} {ts : Vec Term n}
                → 0 < n
                → Dec (Σ[ x ꞉ Id ] (ts ＝ replicate n (`` x)))
Dec-unrepvar {ts} lt .does = is-just? (unrepvar ts)
Dec-unrepvar {ts} lt .proof = Reflects-unrepvar lt
-}

-- couple

couple : {@0 n : ℕ} → Vec Term n → Vec Term n → Vec Term n
couple = zip-with _⟶_

-- TODO ahdoc
couple-replicate-aux : ∀ {n} {xs ys : Vec Term n} {a b : Term}
                     → couple xs ys ＝ replicate n (a ⟶ b)
                     → (xs ＝ replicate n a) × (ys ＝ replicate n b)
couple-replicate-aux {n = zero}  {xs = []}     {ys = []}             e = refl , refl
couple-replicate-aux {n = suc n} {xs = x ∷ xs} {ys = y ∷ ys} {a} {b} e =
  let xye = ⟶-inj $ ∷-head-inj e
      xyse = couple-replicate-aux (∷-tail-inj e)
    in
    ap² {C = λ _ _ → Vec _ _} _∷_ (xye .fst) (xyse .fst)
  , ap² {C = λ _ _ → Vec _ _} _∷_ (xye .snd) (xyse .snd)

couple-replicate : ∀ {n} {xs ys : Vec Term n} {t : Term}
                 → 0 < n
                 → couple xs ys ＝ replicate n t
                 → Σ[ p ꞉ Term ] Σ[ q ꞉ Term ] (t ＝ p ⟶ q) × (xs ＝ replicate n p) × (ys ＝ replicate n q)
couple-replicate {n = zero}                          lt e = false! lt
couple-replicate {n = suc n} {xs = x ∷ xs} {ys = y ∷ ys} {(t)} lt e =
  let te = ∷-head-inj e ⁻¹
      (xse , yse) = couple-replicate-aux (∷-tail-inj e ∙ ap (replicate n) te)
    in
  x , y , te , ap (x ∷_) xse , ap (y ∷_) yse

unrepvar-couple : ∀ {n} {xs ys : Vec Term n}
                → unrepvar (couple xs ys) ＝ nothing
unrepvar-couple {n = zero}  {xs}     = ap² (λ x y → unrepvar (couple x y)) {x = xs} size0-nil size0-nil
unrepvar-couple {n = suc n} {xs} {ys} with unreplicate (couple xs ys) | recall unreplicate (couple xs ys)
... | just t | ⟪ eq ⟫ =
  let ce = unreplicate-just {ts = couple xs ys} eq
      (p , q , e , _ , _) = couple-replicate z<s ce
   in
  ap unvar e
... | nothing | _ = refl

couple-inj : ∀ {n} {as bs xs ys : Vec Term n}
           → couple as bs ＝ couple xs ys
           → (as ＝ xs) × (bs ＝ ys)
couple-inj = zip-with-inj ⟶-inj

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

uncouple : {@0 n : ℕ} → Vec Term n → Maybe (Vec Term n × Vec Term n)
uncouple = map unzip ∘ traverse ⟶-split

uncouple-[] : uncouple [] ＝ just ([] , [])
uncouple-[] = refl

uncouple-nothing-size : {n : ℕ} {ts : Vec Term n}
                      → uncouple ts ＝ nothing
                      → 0 < n
uncouple-nothing-size {n = zero} {ts = []} e = false! e
uncouple-nothing-size {n = suc n}          _ = z<s

uncouple-replicate-`` : {n : ℕ} {x : Id}
                      → 0 < n
                      → uncouple (replicate n (`` x)) ＝ nothing
uncouple-replicate-`` {n = zero} lt = false! lt
uncouple-replicate-`` {n = suc n} lt = refl

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

-- sequence vars

varsq : ∀ {n} → Vec Term n → LFSet Id
varsq = bindₛ vars ∘ from-vec

varsq-replicate : ∀ {n} {x}
                → 0 < n
                → varsq (replicate n (`` x)) ＝ sng x
varsq-replicate lt = ap (bindₛ vars) (from-vec-replicate-0< lt) ∙ bindₛ-sng

varsq-couple-l : ∀ {n} {xs ys : Vec Term n}
               → varsq xs ⊆ varsq (couple xs ys)
varsq-couple-l {xs} {ys} {x} =
  rec!
     (λ y y∈ x∈y →
        let (z , z∈ , yz∈) = ∈-zip-with-l {f = _⟶_} {as = xs} {bs = ys}
                                     (vec-∈ {xs = xs} y∈)
          in
        ∈-bind (∈-vec {xs = couple xs ys} yz∈) (∈ₛ-∪∷←l x∈y))
     ∘ bind-∈

varsq-couple-r : ∀ {n} {xs ys : Vec Term n}
               → varsq ys ⊆ varsq (couple xs ys)
varsq-couple-r {xs} {ys} {x} =
  rec!
     (λ y y∈ x∈y →
        let (z , z∈ , yz∈) = ∈-zip-with-r {f = _⟶_} {as = xs} {bs = ys}
                                     (vec-∈ {xs = ys} y∈)
          in
        ∈-bind (∈-vec {xs = couple xs ys} yz∈) (∈ₛ-∪∷←r {s₁ = vars z} x∈y))
     ∘ bind-∈

varsq-couple-∪∷ : ∀ {n} {xs ys : Vec Term n}
                → varsq (couple xs ys) ⊆ (varsq xs ∪∷ varsq ys)
varsq-couple-∪∷ {xs} {ys} {x} =
  rec!
     (λ y y∈ x∈y →
        let y∈′ = vec-∈ {xs = couple xs ys} y∈
            (a , b , a∈ , b∈ , ye) = zip-with-∈ {as = xs} {bs = ys} y∈′
          in
        [ (∈ₛ-∪∷←l ∘ ∈-bind (∈-vec {xs = xs} a∈))
        , (∈ₛ-∪∷←r {s₁ = varsq xs} ∘ ∈-bind (∈-vec {xs = ys} b∈))
        ]ᵤ (∈ₛ-∪∷→ {xs = vars a} $
            subst (λ q → x ∈ₛ vars q) ye x∈y))
     ∘ bind-∈

varsq-couple : ∀ {n} {xs ys : Vec Term n}
             → varsq (couple xs ys) ＝ varsq xs ∪∷ varsq ys
varsq-couple {xs} {ys} =
  set-ext λ z →
    prop-extₑ! (varsq-couple-∪∷ {xs = xs})
      ([ varsq-couple-l {xs = xs} , varsq-couple-r {xs = xs} ]ᵤ ∘ ∈ₛ-∪∷→ {xs = varsq xs})

-- induction/recursion over uncoupling of sequences

-- todo levels?
record Elim-un {n : ℕ}
               (A : 𝒰)
               (f : Vec Term n → Maybe A)
               (P : Vec Term n → 𝒰) : 𝒰 where
  no-eta-equality
  field
    eu[] : ∀ {ts : Vec Term n} → n ＝ 0 → P ts
    euf  : ∀ {ts : Vec Term n} {a : A}
         → 0 < n → f ts ＝ just a
         → P ts
    eunj : {ps qs ts : Vec Term n}
         → 0 < n → f ts ＝ nothing → uncouple ts ＝ just (ps , qs)
         → P ps → P qs → P ts
    eunn : {ts : Vec Term n}
         → 0 < n → f ts ＝ nothing → uncouple ts ＝ nothing
         → P ts

open Elim-un public

elim-un-ind : {n : ℕ} {A : 𝒰}
              {f : Vec Term (suc n) → Maybe A}
              {P : Vec Term (suc n) → 𝒰}
            → Elim-un A f P
            → (ts : Vec Term (suc n))
            → f ts ＝ nothing
            → ((ts' : Vec Term (suc n)) → tm-sizes ts' < tm-sizes ts → P ts')
            → P ts
elim-un-ind {P} e ts fn ih =
  Maybe.elim
    (λ m → uncouple ts ＝ m → P ts)
    (e .eunn z<s fn)
    (λ where (ps , qs) eqj →
              let (p< , q<) = uncouple-sizes>0 {ts = ts} z<s eqj in
              e .eunj z<s fn eqj (ih ps p<) (ih qs q<))
    (uncouple ts)
    refl

elim-un : {n : ℕ} {A : 𝒰}
          {f : Vec Term n → Maybe A}
          {P : Vec Term n → 𝒰}
        → Elim-un A f P
        → (ts : Vec Term n) → P ts
elim-un {n = zero}      {P} e [] = subst P (subst-refl {B = λ q → Vec Term q} []) (e .eu[] refl)
elim-un {n = suc m} {f} {P} e ts =
  to-induction (wf-lift tm-sizes <-is-wf) P
    (λ ts′ ih →
       Maybe.elim
         (λ v → f ts′ ＝ v → P ts′)
         (λ fn → elim-un-ind e ts′ fn ih)
         (λ a → e .euf z<s)
         (f ts′)
         refl)
    ts

elim-un-step : {n : ℕ} {A : 𝒰}
               {f : Vec Term (suc n) → Maybe A}
               {P : Vec Term (suc n) → 𝒰}
             → (e : Elim-un A f P)
             → (ts : Vec Term (suc n))
             → elim-un e ts ＝ Maybe.elim (λ v → f ts ＝ v → P ts)
                                (λ fn → elim-un-ind  e ts fn (λ zs _ → elim-un e zs))
                                (λ a → e .euf z<s)
                                (f ts)
                                refl
elim-un-step {n} {A} {f} {P} e ts =
  to-induction-eq (wf-lift tm-sizes <-is-wf) P
    (λ ts′ ih →
       Maybe.elim
         (λ v → f ts′ ＝ v → P ts′)
         (λ fn → elim-un-ind e ts′ fn ih)
         (λ a → e .euf z<s)
         (f ts′)
         refl)
    ts

elim-un-step-fj : {n : ℕ} {A : 𝒰}
                → is-set A
                → {f : Vec Term (suc n) → Maybe A}
                  {P : Vec Term (suc n) → 𝒰}
                → (e : Elim-un A f P)
                → {ts : Vec Term (suc n)}
                → ∀ {a} → (fj : f ts ＝ just a)
                → elim-un e ts ＝ e .euf z<s fj
elim-un-step-fj sA {f} {P} e {ts} fj =
    elim-un-step e ts
  ∙ ap² (Maybe.elim (λ v → f ts ＝ v → P ts)
                    (λ fn → elim-un-ind e ts fn λ zs _ → elim-un e zs)
                    (λ a → e .euf z<s))
        fj (to-pathᴾ (maybe-is-of-hlevel 0 sA _ _ _ fj))

elim-un-step-uj : {n : ℕ} {A : 𝒰}
                → is-set A
                → {f : Vec Term (suc n) → Maybe A}
                  {P : Vec Term (suc n) → 𝒰}
                → (e : Elim-un A f P)
                → {ts : Vec Term (suc n)}
                → (fn : f ts ＝ nothing)
                → ∀ {ps} {qs}
                → (eqj : uncouple ts ＝ just (ps , qs))
                → elim-un e ts ＝ e .eunj z<s fn eqj (elim-un e ps) (elim-un e qs)
elim-un-step-uj sA {f} {P} e {ts} fn {ps} {qs} eqj =
    elim-un-step e ts
  ∙ ap² (Maybe.elim (λ v → f ts ＝ v → P ts)
                    (λ fn → elim-un-ind e ts fn λ zs _ → elim-un e zs)
                    (λ a → e .euf z<s))
        fn (to-pathᴾ (maybe-is-of-hlevel 0 sA _ _ _ fn))
  ∙ ap² (Maybe.elim
           (λ m → uncouple ts ＝ m → P ts)
           (e .eunn z<s fn)
           (λ where (ps , qs) eqj → e .eunj z<s fn eqj (elim-un e ps) (elim-un e qs)))
        eqj (to-pathᴾ (hlevel 1 _ eqj))

elim-un-step-un : {n : ℕ} {A : 𝒰}
                → is-set A
                → {f : Vec Term (suc n) → Maybe A}
                  {P : Vec Term (suc n) → 𝒰}
                → (e : Elim-un A f P)
                → {ts : Vec Term (suc n)}
                → (fn : f ts ＝ nothing)
                → (eqn : uncouple ts ＝ nothing)
                → elim-un e ts ＝ e .eunn z<s fn eqn
elim-un-step-un sA {f} {P} e {ts} fn eqn =
    elim-un-step e ts
  ∙ ap² (Maybe.elim (λ v → f ts ＝ v → P ts)
                    (λ fn → elim-un-ind e ts fn λ zs _ → elim-un e zs)
                    (λ a → e .euf z<s))
        fn (to-pathᴾ (maybe-is-of-hlevel 0 sA _ _ _ fn))
  ∙ ap² (Maybe.elim
           (λ m → uncouple ts ＝ m → P ts)
           (e .eunn z<s fn)
           (λ where (ps , qs) eqj → e .eunj z<s fn eqj (elim-un e ps) (elim-un e qs)))
        eqn (to-pathᴾ (hlevel 1 _ eqn))

record Rec-un (n : ℕ) (A : 𝒰)
              (f : Vec Term n → Maybe A)
              (T : ℕ → 𝒰) : 𝒰 where
  no-eta-equality
  field
    ru[] : n ＝ 0 → T n
    ruf  : A → Vec Term n → T n
    runj : T n → T n → T n
    runn : Vec Term n → T n

open Rec-un public

rec→elim→-un : {n : ℕ} {A : 𝒰}
               {f : Vec Term n → Maybe A}
               {T : ℕ → 𝒰}
             → Rec-un n A f T → Elim-un {n} A f (λ _ → T n)
rec→elim→-un {T} r .eu[] = r .ru[]
rec→elim→-un r .euf {ts} {a} _ _ = r .ruf a ts
rec→elim→-un r .eunj _ _ _ = r .runj
rec→elim→-un r .eunn {ts} _ _ _ = r .runn ts

rec-un : {n : ℕ} {A : 𝒰}
         {f : Vec Term n → Maybe A}
         {T : ℕ → 𝒰}
       → Rec-un n A f T → Vec Term n → T n
rec-un = elim-un ∘ rec→elim→-un
