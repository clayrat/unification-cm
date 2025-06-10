{-# OPTIONS --safe #-}
module NominalN.Cofinite.BaseA where

open import Prelude
open import Meta.Effect
open import Meta.Effect.Traversable

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Reflects.Sigma as ReflectsΣ
open import Data.Dec.Sigma as DecΣ

open import Data.Acc
open import Data.Nat
open import Data.Nat.Order.Base
open import Data.Sum
open import Data.String
open import Data.Maybe as Maybe
open import Data.Maybe.Instances.Map.Properties
open import Data.Maybe.Correspondences.Unary.Any
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

Reflects-unvar : {t : Term}
               → ReflectsΣ (λ x → t ＝ `` x) (unvar t)
Reflects-unvar {t = `` x}    = ofʲ x refl
Reflects-unvar {t = p ⟶ q} = ofⁿ λ x → false!
Reflects-unvar {t = con x}   = ofⁿ λ x → false!

Dec-unvar : {t : Term}
          → DecΣ (λ x → t ＝ `` x)
Dec-unvar {t} .doesm = unvar t
Dec-unvar     .proofm = Reflects-unvar

{-
unvar-just : {t : Term} {x : Id}
           → x ∈ unvar t
           → t ＝ `` x
unvar-just = ∈→true Reflects-unvar

unvar-nothing : {t : Term}
              → unvar t ＝ nothing
              → ∀ {x} → t ≠ `` x
unvar-nothing = nothing→false Reflects-unvar
-}

-- unreplicate

unreplicate : {@0 n : ℕ} → Vec Term n → Maybe Term
unreplicate []       = nothing
unreplicate (t ∷ ts) = if all (_==tm t) ts then just t else nothing

just-unreplicate : {n : ℕ} {z : Term}
                 → 0 < n
                 → z ∈ unreplicate (replicate n z)
just-unreplicate {n = zero}      lt = false! lt
just-unreplicate {n = suc n} {z} _  =
  =just→∈ $
  if-true {t = just z} $
  true→so! ⦃ Reflects-all {xs = replicate n z} λ w → tm-eq-reflects {x = w} ⦄ $
  replicate-all n

Reflects-unreplicate : {n : ℕ} {ts : Vec Term n}
                     → 0 < n
                     → ReflectsΣ (λ x → ts ＝ replicate n x) (unreplicate ts)
Reflects-unreplicate {n = zero}                lt = false! lt
Reflects-unreplicate {n = suc n} {ts = t ∷ ts} lt with all (_==tm t) ts | recall (all (_==tm t)) ts
... | true  | ⟪ eq ⟫ =
  ofʲ t (ap² {C = λ _ _ → Vec _ (suc _)} _∷_ refl $
         All-replicate ts $
         so→true! ⦃ Reflects-all {xs = ts} λ w → tm-eq-reflects {x = w} {y = t} ⦄ $
         so≃is-true ⁻¹ $ eq)
... | false | ⟪ eq ⟫ =
  ofⁿ λ z →
    contra
      (λ e →
        true→so! ⦃ Reflects-all {xs = ts} λ w → tm-eq-reflects {x = w} {y = t} ⦄ $
        subst (λ xs → All (_＝ t) xs) (∷-tail-inj e ⁻¹) $
        subst (λ q → All (_＝ t) (replicate n q)) (∷-head-inj e) $
        replicate-all n)
      (¬so≃is-false ⁻¹ $ eq)

unreplicate-just : {n : ℕ} {z : Term} {ts : Vec Term n}
                 → z ∈ unreplicate ts
                 → ts ＝ replicate n z
unreplicate-just {n = 0}     {ts = []} m = false! m
unreplicate-just {n = suc n} {z}       m =
  ∈→true (Reflects-unreplicate z<s) m

unreplicate-nothing : {n : ℕ} {ts : Vec Term n}
                    → 0 < n
                    → unreplicate ts ＝ nothing
                    → ∀ {z} → ts ≠ replicate n z
unreplicate-nothing lt =
  nothing→false (Reflects-unreplicate lt)

Dec-unreplicate : {n : ℕ} {ts : Vec Term n}
                → 0 < n
                → DecΣ (λ x → ts ＝ replicate n x)
Dec-unreplicate {ts} lt .doesm = unreplicate ts
Dec-unreplicate {ts} lt .proofm = Reflects-unreplicate lt

-- unrepvar

unrepvar : ∀ {n} → Vec Term n → Maybe Id
unrepvar = unreplicate >=> unvar

unrepvar-just : ∀ {n} {ts : Vec Term n} {x : Id}
              → x ∈ unrepvar ts
              → Σ[ t ꞉ Term ] (t ∈ unreplicate ts) × (x ∈ unvar t)
unrepvar-just {ts} = bind-∈Σ

unrepvar-just-eq : ∀ {n} {ts : Vec Term n} {x : Id}
                 → x ∈ unrepvar ts
                 → ts ＝ replicate n (`` x)
unrepvar-just-eq {ts} m =
  let (t , e1 , e2) = unrepvar-just {ts = ts} m in
  unreplicate-just $ =just→∈ $
  ∈→true reflectsΣ-= e1 ∙ ap just (∈→true Reflects-unvar e2)

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
                  → ReflectsΣ (λ x → ts ＝ replicate n (`` x)) (unrepvar ts)
Reflects-unrepvar {ts} lt =
  reflectsΣ-bind
    ``_
    {!!}
    (Reflects-unreplicate lt)
    λ t → {!!}
-}

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
unrepvar-couple {n = zero}  {xs}      = ap² (λ x y → unrepvar (couple x y)) {x = xs} size0-nil size0-nil
unrepvar-couple {n = suc n} {xs} {ys} with unreplicate (couple xs ys) | recall unreplicate (couple xs ys)
... | just t | ⟪ eq ⟫ =
  let ce = unreplicate-just {ts = couple xs ys} (=just→∈ eq)
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

Reflects-⟶ : ∀ {t}
             → ReflectsΣ (λ (p , q) → t ＝ p ⟶ q) (⟶-split t)
Reflects-⟶ {t = `` x}    = ofⁿ λ pq e → false! e
Reflects-⟶ {t = p ⟶ q} = ofʲ (p , q) refl
Reflects-⟶ {t = con x}   = ofⁿ λ pq e → false! e

uncouple : {@0 n : ℕ} → Vec Term n → Maybe (Vec Term n × Vec Term n)
uncouple = map unzip ∘ traverse ⟶-split

uncouple-[] : ([] , []) ∈ uncouple []
uncouple-[] = here refl

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
               → pqs ∈ vec-traverse ⟶-split ts
               → let (ps , qs) = unzip pqs in
                 (tm-sizes ps ≤ tm-sizes ts)
               × (tm-sizes qs ≤ tm-sizes ts)
traverse-sizes {ts = []}                           (here e) =
    subst (λ q → tm-sizes (unzip q .fst) ≤ 0) (e ⁻¹) z≤
  , subst (λ q → tm-sizes (unzip q .snd) ≤ 0) (e ⁻¹) z≤
traverse-sizes {ts = t ∷ ts} {pqs = (p , q) ∷ pqs}  m       =
  let ((p′ , q′) , xs , steq , treq , ceq) =
           map²-∈Σ {f = _∷_} {xm = ⟶-split t} m
      teq = ∈→true Reflects-⟶ steq
      psqs≤ = traverse-sizes {ts = ts} {pqs = pqs} $
              =just→∈ (∈→true reflectsΣ-= treq ∙ ap just (∷-tail-inj ceq))
      pqeq = ×-path-inv $ ∷-head-inj ceq
    in
    ≤-+ (subst (λ w → tm-size p ≤ tm-size w)
               (teq ⁻¹)
               (≤-ascend ∙ s≤s (=→≤ (ap tm-size (pqeq .fst ⁻¹)) ∙ ≤-+-r)))
        (psqs≤ .fst)
  , ≤-+ (subst (λ w → tm-size q ≤ tm-size w)
               (teq ⁻¹)
               (≤-ascend ∙ s≤s (=→≤ (ap tm-size (pqeq .snd ⁻¹)) ∙ ≤-+-l)))
        (psqs≤ .snd)

uncouple-sizes : {@0 n : ℕ} {ts ps qs : Vec Term n}
               → (ps , qs) ∈ uncouple ts
               → (tm-sizes ps ≤ tm-sizes ts)
               × (tm-sizes qs ≤ tm-sizes ts)
uncouple-sizes {ts} m =
  let (pqs , meq , eq) = map-∈Σ unzip m
      treq = traverse-sizes {ts = ts} meq
      (pseq , qseq) = ×-path-inv eq
   in
    =→≤ (ap tm-sizes pseq) ∙ treq .fst
  , =→≤ (ap tm-sizes qseq) ∙ treq .snd

traverse-couple : {@0 n : ℕ} {xs ys : Vec Term n}
                  → Σ[ zs ꞉ Vec (Term × Term) n ] (zs ∈ vec-traverse ⟶-split (couple xs ys))
                                                × (unzip zs ＝ (xs , ys))
traverse-couple {xs = []}     {ys = []}     = [] , here refl , refl
traverse-couple {xs = x ∷ xs} {ys = y ∷ ys} =
  let (zs , ej , eu) = traverse-couple {xs = xs} {ys = ys}
      (ex , ey) = ×-path-inv eu
    in
    (x , y) ∷ zs
  , any→map (any-map (ap ((x , y) ∷_)) ej)
  , ×-path (ap (x ∷_) ex) (ap (y ∷_) ey)

couple-traverse : {@0 n : ℕ} {ts : Vec Term n} {zs : Vec (Term × Term) n}
                → zs ∈ vec-traverse ⟶-split ts
                → let (xs , ys) = unzip zs in
                  couple xs ys ＝ ts
couple-traverse {ts = []} {zs = zs}               (here e) =
  let (pe , qe) = ×-path-inv (ap unzip e) in
  ap² couple pe qe
couple-traverse {ts = t ∷ ts} {zs = (x , y) ∷ zs}  m       =
  let ((p′ , q′) , xs , steq , treq , ceq) =
           map²-∈Σ {f = _∷_} {xm = ⟶-split t} m
      pqeq = ×-path-inv $ ∷-head-inj ceq
    in
  ap² {C = λ _ _ → Vec _ (suc _)} _∷_
    (  ap² _⟶_ (pqeq .fst ⁻¹) (pqeq .snd ⁻¹)
     ∙ ∈→true Reflects-⟶ steq ⁻¹)
    (couple-traverse {ts = ts} {zs = zs} $
     =just→∈ $
     ∈→true reflectsΣ-= treq ∙ ap just (∷-tail-inj ceq))

couple-uncouple : {@0 n : ℕ} {ts xs ys : Vec Term n}
                → (xs , ys) ∈ uncouple ts
                → couple xs ys ＝ ts
couple-uncouple {ts} {xs} {ys}  m =
  let (xys , e′ , ue) = map-∈Σ unzip m -- mapₘ=just e
      (xe , ye) = ×-path-inv (ue ⁻¹)
    in
    ap² couple (xe ⁻¹) (ye ⁻¹)
  ∙ couple-traverse {ts = ts} {zs = xys} e′

uncouple-couple : {@0 n : ℕ} {xs ys : Vec Term n}
                → (xs , ys) ∈ uncouple (couple xs ys)
uncouple-couple {xs} {ys} =
  let (zs , ej , eu) = traverse-couple in
  =just→∈ $
  ∈→true reflectsΣ-= (any→map {f = unzip} (any-map (ap unzip) ej)) ∙ ap just eu

{-
Reflects-uncouple : {@0 n : ℕ} {ts : Vec Term n}
                  → ReflectsΣ (λ (ps , qs) → ts ＝ couple ps qs) (uncouple ts)
Reflects-uncouple {ts} with uncouple ts | recall uncouple ts
... | just (ps , qs) | ⟪ eq ⟫ = ofʲ (ps , qs) (couple-uncouple eq ⁻¹)
... | nothing        | ⟪ eq ⟫ = ofⁿ λ pqs e → {!!}
-}

uncouple-∷ : ∀ {@0 n : ℕ} {t p q} {ts ps qs : Vec Term n}
           → (p ∷ ps , q ∷ qs) ∈ uncouple (t ∷ ts)
           → (t ＝ p ⟶ q) × ((ps , qs) ∈ uncouple ts)
uncouple-∷ {t} {ts} {ps} {qs} e =
  let e′ = couple-uncouple {ts = t ∷ ts} e ⁻¹ in
    (∷-head-inj e′)
  , (=just→∈ $
     ap uncouple (∷-tail-inj e′) ∙ ∈→true reflectsΣ-= uncouple-couple)

uncouple-sizes>0 : {n : ℕ} {ts ps qs : Vec Term n}
                 → 0 < n
                 → (ps , qs) ∈ uncouple ts
                 → (tm-sizes ps < tm-sizes ts)
                 × (tm-sizes qs < tm-sizes ts)
uncouple-sizes>0 {n = zero}                                            lt _ = false! lt
uncouple-sizes>0 {n = suc n} {ts = t ∷ ts} {ps = p ∷ ps} {qs = q ∷ qs} _  e =
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

-- TODO levels?
-- TODO refactor via maybe membership
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
              let (p< , q<) = uncouple-sizes>0 {ts = ts} z<s (=just→∈ eqj) in
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
