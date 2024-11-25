{-# OPTIONS --safe #-}
module Ribeiro.Infer where

open import Prelude
open import Meta.Effect

open import Data.Empty hiding (_≠_)
open import Data.Bool
open import Data.Reflects
open import Data.Dec as Dec
open import Data.Nat
open import Data.Maybe as Maybe
open import Data.Sum as Sum
open import Data.List
open import Data.List.Correspondences.Unary.All
open import Data.List.Correspondences.Unary.Any
open import Data.List.Operations.Properties

open import Ribeiro.Ty
open import Ribeiro.Unify

private variable
  ℓ : Level
  A B : 𝒰 ℓ

-- terms

data Term : 𝒰 where
  `_   : Id → Term
  _⌽_  : Term → Term → Term
  ƛ_⇒_ : Id → Term → Term
  cst  : Term

TyCtx : 𝒰
TyCtx = List (Id × Ty)

-- typing derivations

-- TODO fixity
data _⊢_⦂_ : TyCtx → Term → Ty → 𝒰 where
  ⊢`_  : ∀ {v τ Γ}
        → (v , τ) ∈ Γ → Γ ⊢ ` v ⦂ τ
  ⊢ƛ_  : ∀ {v τ τ′ t Γ}
        → ((v , τ) ∷ Γ) ⊢ t ⦂ τ′ → Γ ⊢ (ƛ v ⇒ t) ⦂ (τ ⟶ τ′)
  ⊢_⌽_ : ∀ {τ τ′ l r Γ}
        → Γ ⊢ l ⦂ (τ ⟶ τ′) → Γ ⊢ r ⦂ τ → Γ ⊢ l ⌽ r ⦂ τ′
  ⊢cst : ∀ {Γ}
        → Γ ⊢ cst ⦂ con

-- tc monad

record TcState : 𝒰 where
  constructor mkstate
  field
    next-tvar : Id
    used-vars : List Id
    constrs   : List (Ty × Ty)

open TcState public

TcM : 𝒰 ℓ → 𝒰 ℓ
TcM A = TcState → Maybe (TcState × A)

tcm-map : (A → B) → TcM A → TcM B
tcm-map f ta st = second f <$> ta st

tcm-pure : A → TcM A
tcm-pure a st = just (st , a)

tcm-ap : TcM (A → B) → TcM A → TcM B
tcm-ap tf ta st =
  do (st′ , f) ← tf st
     (st″ , a) ← ta st′
     pure (st″ , f a)

tcm-bind : (A → TcM B) → TcM A → TcM B
tcm-bind ft ta st =
  do (st′ , a) ← ta st
     (st″ , b) ← ft a st′
     pure (st″ , b)

instance
  Map-TcM : Map (eff TcM)
  Map-TcM .map = tcm-map

  Idiom-TcM : Idiom (eff TcM)
  Idiom-TcM .pure  = tcm-pure
  Idiom-TcM ._<*>_ = tcm-ap

  Bind-TcM : Bind (eff TcM)
  Bind-TcM ._>>=_ = flip tcm-bind

tcm-fail : TcM A
tcm-fail _ = nothing

fresh : TcM Ty
fresh (mkstate n ts cs) = just (mkstate (suc n) (ts ∷r n) cs , `` n)

add-constr : Ty → Ty → TcM ⊤
add-constr t t′ (mkstate n ts cs) = just (mkstate n ts ((t , t′) ∷ cs) , tt)

-- TODO use more Γρεεκ

-- TODO just use finmaps for ctxts instead of reinventing the wheel?
-- probably can't do that because of ordering guarantees tho
look : Id → TyCtx → TcM Ty
look x []            = tcm-fail
look x ((y , t) ∷ g) = if x =? y then pure t else look x g

look-just : ∀ {x t s s′ g}
          → look x g s ＝ just (s′ , t) → (x , t) ∈ g × (s ＝ s′)
look-just                  {g = []}          e = false! e
look-just {x} {t} {s} {s′} {g = (y , r) ∷ g}   =
  Dec.elim
    {C = λ q → (if ⌊ q ⌋ then tcm-pure r else look x g) s ＝ just (s′ , t) → ((x , t) ∈ₗ ((y , r) ∷ g)) × (s ＝ s′)}
    (λ e eq → let steq = ×-path-inv $ just-inj eq in
              here (×-path e (steq .snd ⁻¹ )) , steq .fst)
    (λ ne eq → first there (look-just {g = g} eq))
    (x ≟ y)

-- typing context properties

wf-tyctx : Varctx → TyCtx → 𝒰
wf-tyctx d g = All (wf-ty d ∘ snd) g

wf-tyctx-weaken : ∀ {d d′ g}
                → wf-tyctx d g → wf-tyctx (d ++ d′) g
wf-tyctx-weaken {d′} = all-map λ {x} → wf-ty-weaken d′ (x .snd)

wf-tyctx-weaken-∷r : ∀ {d t g}
                   → wf-tyctx d g → wf-tyctx (d ∷r t) g
wf-tyctx-weaken-∷r {d} {g} =
  subst (λ q → wf-tyctx q g) (snoc-append d ⁻¹) ∘ wf-tyctx-weaken

apply-ctx : Substitution → TyCtx → TyCtx
apply-ctx s = map (second (apply-subst s))

-- constraint generator

gen-constr : TyCtx → Term → TcM Ty
gen-constr g (` v)     = look v g
gen-constr g (p ⌽ q)   = do t1 ← gen-constr g p
                            t2 ← gen-constr g q
                            t ← fresh
                            _ ← add-constr t1 (t2 ⟶ t)
                            pure t
gen-constr g (ƛ v ⇒ t) = do t1 ← fresh
                            t2 ← gen-constr ((v , t1) ∷ g) t
                            pure (t1 ⟶ t2)
gen-constr g cst       = pure con

gen-constr-wf : ∀ {g s1 s2 t} e
              → gen-constr g e s1 ＝ just (s2 , t)
              → wf-tyctx (s1 .used-vars) g
              → wf-constr-list (s1 .used-vars) (s1 .constrs)
              → (Σ[ d2 ꞉ List Id ] (s2 .used-vars ＝ s1 .used-vars ++ d2))
              × (Σ[ c2 ꞉ List (Ty × Ty) ] (s2 .constrs ＝ c2 ++ s1 .constrs))
              × (wf-constr-list (s2 .used-vars) (s2 .constrs))
              × (wf-ty (s2 .used-vars) t)
gen-constr-wf {g} {s1} {s2} {t} (` v)     gce wt wcl =
  let (mem , seq) = look-just {g = g} gce in
    ([] , ap used-vars (seq ⁻¹) ∙ ++-id-r (s1 .used-vars) ⁻¹)
  , ([] , ap constrs (seq ⁻¹))
  , subst (λ q → wf-constr-list (q .used-vars) (q .constrs)) seq wcl
  , All→∀∈ (subst (λ q → wf-tyctx (q .used-vars) g) seq wt) (v , t) mem
-- this is why we need a Hoare monad, to avoid decomposing TcM into maybes and states + plumbing it back together
gen-constr-wf {g} {s1}          (p ⌽ q)   gce wt wcl with gen-constr g p s1 | recall (gen-constr g p) s1
gen-constr-wf {g} {s1}          (p ⌽ q)   gce wt wcl | just (s′ , t′) | eq1 with gen-constr g q s′ | recall (gen-constr g q) s′
gen-constr-wf {g} {s1} {s2} {t} (p ⌽ q)   gce wt wcl | just (s′ , t′) | ⟪ eq1 ⟫ | just (s″ , t″) | ⟪ eq2 ⟫ =
  let pprf = ×-path-inv $ just-inj gce
      ((ih1d2 , ih1d2e) , (ih1c2 , ih1c2e) , ih13 , ih14) = gen-constr-wf p eq1 wt wcl
      ((ih2d2 , ih2d2e) , (ih2c2 , ih2c2e) , ih23 , ih24) = gen-constr-wf q eq2
                                                              (subst (λ q → wf-tyctx q g) (ih1d2e ⁻¹) (wf-tyctx-weaken wt))
                                                              ih13
    in
    ( ih1d2 ++ ih2d2 ∷r s″ .next-tvar
    , (  ap used-vars (pprf .fst ⁻¹)
       ∙ ap (_∷r s″ .next-tvar) ih2d2e
       ∙ snoc-++ (s′ .used-vars) ih2d2 (s″ .next-tvar)
       ∙ ap (_++ ih2d2 ∷r s″ .next-tvar) ih1d2e
       ∙ ++-assoc (s1 .used-vars) ih1d2 (ih2d2 ∷r s″ .next-tvar)))
  , ( (t′ , (t″ ⟶ (`` s″ .next-tvar))) ∷ ih2c2 ++ ih1c2
    ,   ap constrs (pprf .fst ⁻¹)
      ∙ ap ((t′ , (t″ ⟶ (`` s″ .next-tvar))) ∷_) ih2c2e
      ∙ ap (((t′ , (t″ ⟶ (`` s″ .next-tvar))) ∷ ih2c2) ++_) ih1c2e
      ∙ ++-assoc ((t′ , (t″ ⟶ (`` s″ .next-tvar))) ∷ ih2c2) ih1c2 (s1 .constrs) ⁻¹)
  , (subst (λ q → wf-constr-list (q .used-vars) (q .constrs)) (pprf .fst) $
     ( (wf-ty-end t′ $ subst (λ q → wf-ty q t′) (ih2d2e ⁻¹) $ wf-ty-weaken ih2d2 t′ ih14)
      , wf-ty-end t″ ih24
      , any-∷r-last refl) ∷ wf-constr-weaken-∷r ih23)
  , (subst (wf-ty (s2 .used-vars)) (pprf .snd) $
     subst (λ q → s″ .next-tvar ∈ q .used-vars) (pprf .fst) $
     any-∷r-last refl)
gen-constr-wf {g} {s1}          (p ⌽ q)   gce wt wcl | just (s′ , t′) | eq1 | nothing | _ = false! gce
gen-constr-wf {g} {s1}          (p ⌽ q)   gce wt wcl | nothing | _ = false! gce
gen-constr-wf {g} {s1}          (ƛ v ⇒ e) gce wt wcl with gen-constr ((v , (`` s1 .next-tvar)) ∷ g) e  (mkstate (suc (s1 .next-tvar)) ((s1 .used-vars) ∷r (s1 .next-tvar)) (s1 .constrs))
                                                | recall (gen-constr ((v , (`` s1 .next-tvar)) ∷ g) e) (mkstate (suc (s1 .next-tvar)) ((s1 .used-vars) ∷r (s1 .next-tvar)) (s1 .constrs))
gen-constr-wf {g} {s1} {s2} {t} (ƛ v ⇒ e) gce wt wcl | just (s′ , t′) | ⟪ eq ⟫ =
  let pprf = ×-path-inv $ just-inj gce
      ((ihd2 , ihd2e) , (ihc2 , ihc2e) , ih3 , ih4) = gen-constr-wf e eq
                                                        (any-∷r-last refl ∷ wf-tyctx-weaken-∷r wt)
                                                        (wf-constr-weaken-∷r wcl)
    in
    (  s1 .next-tvar ∷ ihd2
     ,   ap used-vars (pprf .fst ⁻¹)
       ∙ ihd2e
       ∙ ++-snoc (s1 .used-vars) ihd2 (s1 .next-tvar))
  , (  ihc2
     , ap constrs (pprf .fst ⁻¹) ∙ ihc2e)
  , subst (λ q → wf-constr-list (q .used-vars) (q .constrs)) (pprf .fst) ih3
  , (subst (λ q → wf-ty (s2 .used-vars) q) (pprf .snd) $
       (subst (λ q → s1 .next-tvar ∈ q .used-vars) (pprf .fst) $
        subst (λ q → s1 .next-tvar ∈ q) (ihd2e ⁻¹) $
        any-++-l {ys = ihd2} $ any-∷r-last refl)
     , subst (λ q → wf-ty (q .used-vars) t′) (pprf .fst) ih4)
gen-constr-wf                   (ƛ v ⇒ e) gce wt wcl | nothing | eq = false! gce
gen-constr-wf     {s1} {s2}      cst      gce wt wcl =
  let steq = ×-path-inv $ just-inj gce in
    ([] , ap used-vars (steq .fst ⁻¹) ∙ ++-id-r (s1 .used-vars) ⁻¹)
  , ([] , ap constrs (steq .fst ⁻¹))
  , subst (λ q → wf-constr-list (q .used-vars) (q .constrs)) (steq .fst) wcl
  , subst (wf-ty (s2 .used-vars)) (steq .snd) tt

-- TODO code duplication
-- looks like this part can be removed from the previous lemma
gen-constr-extends : ∀ {s1 s2 t g e}
                   → gen-constr g e s1 ＝ just (s2 , t)
                   → Σ[ cs2 ꞉ List (Ty × Ty) ] (s2 .constrs ＝ cs2 ++ s1 .constrs)
gen-constr-extends      {g} {e = ` v}     gce =
  let seq = snd $ look-just {g = g} gce in
  ([] , ap constrs (seq ⁻¹))
gen-constr-extends {s1} {g} {e = p ⌽ q}   gce with gen-constr g p s1 | recall (gen-constr g p) s1
gen-constr-extends {s1} {g} {e = p ⌽ q}   gce | just (s′ , t′) | ⟪ eq1 ⟫ with gen-constr g q s′ | recall (gen-constr g q) s′
gen-constr-extends {s1} {g} {e = p ⌽ q}   gce | just (s′ , t′) | ⟪ eq1 ⟫ | just (s″ , t″) | ⟪ eq2 ⟫ =
  let pprf = ×-path-inv $ just-inj gce
      (ih1c2 , ih1c2e) = gen-constr-extends {e = p} eq1
      (ih2c2 , ih2c2e) = gen-constr-extends {e = q} eq2
   in
  (t′ , (t″ ⟶ (`` s″ .next-tvar))) ∷ ih2c2 ++ ih1c2
  ,   ap constrs (pprf .fst ⁻¹)
    ∙ ap ((t′ , (t″ ⟶ (`` s″ .next-tvar))) ∷_) ih2c2e
    ∙ ap (((t′ , (t″ ⟶ (`` s″ .next-tvar))) ∷ ih2c2) ++_) ih1c2e
    ∙ ++-assoc ((t′ , (t″ ⟶ (`` s″ .next-tvar))) ∷ ih2c2) ih1c2 (s1 .constrs) ⁻¹
gen-constr-extends          {e = p ⌽ q}   gce | just (s′ , t′) | eq1 | nothing | _ = false! gce
gen-constr-extends          {e = p ⌽ q}   gce | nothing | _ = false! gce
gen-constr-extends {s1} {g} {e = ƛ v ⇒ e} gce with gen-constr ((v , (`` s1 .next-tvar)) ∷ g) e  (mkstate (suc (s1 .next-tvar)) ((s1 .used-vars) ∷r (s1 .next-tvar)) (s1 .constrs))
                                         | recall (gen-constr ((v , (`` s1 .next-tvar)) ∷ g) e) (mkstate (suc (s1 .next-tvar)) ((s1 .used-vars) ∷r (s1 .next-tvar)) (s1 .constrs))
gen-constr-extends {s1} {g} {e = ƛ v ⇒ e} gce | just (s′ , t′) | ⟪ eq ⟫ =
  let pprf = ×-path-inv $ just-inj gce
      (ihc2 , ihc2e) = gen-constr-extends {e = e} eq
    in
  ihc2 , ap constrs (pprf .fst ⁻¹) ∙ ihc2e
gen-constr-extends          {e = ƛ v ⇒ e} gce | nothing | eq = false! gce
gen-constr-extends          {e = cst}     gce =
  let seq = fst $ ×-path-inv $ just-inj gce in
  [] , ap constrs (seq ⁻¹)

-- type inference

type-infer : Term → Maybe Ty
type-infer e =
  let x = gen-constr [] e (mkstate 0 [] []) in
  Maybe.elim (λ q → x ＝ q → Maybe Ty)
    (λ _ → nothing)
    (λ where
         (mkstate nv uv cs , t) eq →
            (unify (uv , cs) (gen-constr-wf e eq [] [] .snd .snd .fst)) &
            [ (λ (s , _) → just (apply-subst s t))
            , (λ _ → nothing) ]ᵤ)
    x refl

has-type-subst : ∀ {s Γ e τ}
               → Γ ⊢ e ⦂ τ
               → (apply-ctx s Γ) ⊢ e ⦂ (apply-subst s τ)
has-type-subst {s}     (⊢` vi)   = ⊢` (∈-map (second (apply-subst s)) vi)
has-type-subst {s} {Γ} (⊢ƛ_ {v} {τ} {τ′} {t} e)    =
  subst (apply-ctx s Γ ⊢ ƛ v ⇒ t ⦂_) (apply-subst-app {s = s} ⁻¹) $
  ⊢ƛ (has-type-subst {s} e)
has-type-subst {s} {Γ} (⊢_⌽_ {l} p q) =
  let ih1 = has-type-subst {s = s} p
      ih2 = has-type-subst {s = s} q
    in
  ⊢ subst (apply-ctx s Γ ⊢ l ⦂_) (apply-subst-app {s = s}) ih1 ⌽ ih2
has-type-subst {s} {Γ}  ⊢cst     =
  subst (apply-ctx s Γ ⊢ cst ⦂_) (apply-subst-con {s = s} ⁻¹) ⊢cst

apply-ctx-compose : ∀ {g s1 s2} → apply-ctx (s1 ++ s2) g ＝ apply-ctx s2 (apply-ctx s1 g)
apply-ctx-compose {g} {s1} =
    ap (λ q → map q g) (fun-ext (λ (i , t) → ap (i ,_) (apply-subst-append {s1 = s1})))
  ∙ happly map-pres-comp g

has-type-apply-ctx : ∀ {Γ e τ s1 s2}
                   → (apply-ctx s1 Γ) ⊢ e ⦂ (apply-subst s1 τ)
                   → (apply-ctx (s1 ++ s2) Γ) ⊢ e ⦂ (apply-subst (s1 ++ s2) τ)
has-type-apply-ctx {Γ} {e} {τ} {s1} {s2} =
  subst (_⊢ e ⦂ apply-subst (s1 ++ s2) τ) (apply-ctx-compose {s1 = s1} ⁻¹) ∘
  subst (apply-ctx s2 (apply-ctx s1 Γ) ⊢ e ⦂_) (apply-subst-append {s1 = s1} ⁻¹) ∘
  has-type-subst {s = s2}

-- TODO actually use has-type-subst ?
ti-correct : ∀ {Γ s1 s2 τ e}
           → gen-constr Γ e s1 ＝ just (s2 , τ)
           → ∀ {s} → (∀ {t1 t2} → (t1 , t2) ∈ s2 .constrs → apply-subst s t1 ＝ apply-subst s t2)
           → (apply-ctx s Γ) ⊢ e ⦂ (apply-subst s τ)
ti-correct {Γ}          {e = ` v}     gce {s} h =
  let mem = fst $ look-just {g = Γ} gce in
  ⊢` (∈-map (second (apply-subst s)) mem)
ti-correct {Γ} {s1}     {e = p ⌽ q}   gce {s} h with gen-constr Γ p s1 | recall (gen-constr Γ p) s1
ti-correct {Γ} {s1}     {e = p ⌽ q}   gce {s} h | just (s′ , t′) | ⟪ eq1 ⟫ with gen-constr Γ q s′ | recall (gen-constr Γ q) s′
ti-correct {Γ} {s1} {τ} {e = p ⌽ q}   gce {s} h | just (s′ , t′) | ⟪ eq1 ⟫ | just (s″ , t″) | ⟪ eq2 ⟫ =
  let pprf = ×-path-inv $ just-inj gce
      (cs2 , seq) = gen-constr-extends {s1 = s′} {g = Γ} {e = q} eq2
      ih1 = ti-correct {e = p} eq1 {s = s}
              λ {t1} {t2} mem →
                  h (subst (λ q → (t1 , t2) ∈ q .constrs) (pprf .fst) $
                     subst (λ q → (t1 , t2) ∈ ((t′ , (t″ ⟶ (`` s″ .next-tvar))) ∷ q)) (seq ⁻¹) $
                     any-++-r mem)
      ih2 = ti-correct {e = q} eq2 {s = s}
              λ {t1} {t2} mem →
                  h (subst (λ q → (t1 , t2) ∈ q .constrs) (pprf .fst) (there mem))
   in
  ⊢ subst (apply-ctx s Γ ⊢ p ⦂_)
       (  h (subst (λ q → (t′ , (t″ ⟶ τ)) ∈ q .constrs) (pprf .fst) $
             here (ap (λ q → t′ , (t″ ⟶ q)) (pprf .snd ⁻¹)))
        ∙ apply-subst-app {s = s}) ih1 ⌽ ih2
ti-correct              {e = p ⌽ q}   gce {s} h | just (s′ , t′) | eq1 | nothing | _ = false! gce
ti-correct              {e = p ⌽ q}   gce {s} h | nothing | _ = false! gce
ti-correct {Γ} {s1}     {e = ƛ v ⇒ e} gce {s} h with gen-constr ((v , (`` s1 .next-tvar)) ∷ Γ) e  (mkstate (suc (s1 .next-tvar)) ((s1 .used-vars) ∷r (s1 .next-tvar)) (s1 .constrs))
                                           | recall (gen-constr ((v , (`` s1 .next-tvar)) ∷ Γ) e) (mkstate (suc (s1 .next-tvar)) ((s1 .used-vars) ∷r (s1 .next-tvar)) (s1 .constrs))
ti-correct {Γ} {s1}     {e = ƛ v ⇒ e} gce {s} h | just (s′ , t′) | ⟪ eq ⟫ =
  let pprf = ×-path-inv $ just-inj gce
      ih = ti-correct {e = e} eq {s = s}
             λ {t1} {t2} mem →
                h (subst (λ q → (t1 , t2) ∈ q .constrs) (pprf .fst) mem)
    in
  subst (λ q → apply-ctx s Γ ⊢ ƛ v ⇒ e ⦂ apply-subst s q) (pprf .snd) $
  subst (λ q → apply-ctx s Γ ⊢ ƛ v ⇒ e ⦂ q) (apply-subst-app {s = s} ⁻¹) $
  ⊢ƛ ih
ti-correct {Γ} {s1}     {e = ƛ v ⇒ e} gce {s} h | nothing | eq = false! gce
ti-correct {Γ}          {e = cst}     gce {s} h =
  let teq = snd $ ×-path-inv $ just-inj gce in
  subst (λ q → apply-ctx s Γ ⊢ cst ⦂ apply-subst s q) teq $
  subst (apply-ctx s Γ ⊢ cst ⦂_) (apply-subst-con {s = s} ⁻¹) ⊢cst

unify-eq : ∀ {s t t' cs}
         → unifier cs s
         → (t , t') ∈ cs
         → apply-subst s t ＝ apply-subst s t'
unify-eq {s} {cs = (l , r) ∷ cs} (e ∷ _) (here eq)   =
  let elr = ×-path-inv eq in
  ap (apply-subst s) (elr .fst) ∙ e ∙ ap (apply-subst s) (elr .snd ⁻¹)
unify-eq {s} {cs = (l , r) ∷ cs} (_ ∷ u) (there mem) = unify-eq {s = s} u mem

-- TODO ugh
type-infer-sound : ∀ {e t} → type-infer e ＝ just t → [] ⊢ e ⦂ t
type-infer-sound {e} {t} =
  Maybe.elim (λ q′ → (eq : gen-constr [] e (mkstate 0 [] []) ＝ q′)
                   → Maybe.elim (λ q → gen-constr [] e (mkstate 0 [] []) ＝ q → Maybe Ty)
                       (λ _ → nothing)
                       (λ { (mkstate nv uv cs , t) eq
                                → [ (λ x → just (apply-subst (x .fst) t)) , (λ _ → nothing) ]ᵤ
                                  (unify (uv , cs) (gen-constr-wf e eq [] [] .snd .snd .fst))
                            })
                       q′ eq ＝ just t → [] ⊢ e ⦂ t)
   (λ _ → false!)
   (λ where
        (mkstate nv uv cs , t′) eq →
            (Sum.universal {C = λ q → [ (λ x → just (apply-subst (x .fst) t′)) , (λ _ → nothing) ]ᵤ q ＝ just t → [] ⊢ e ⦂ t} ⁻¹ $
                (λ where
                     (s , us , ws , prf) eq′ →
                       let eq″ = just-inj eq′ in
                       subst ([] ⊢ e ⦂_) eq″ (ti-correct eq {s = s} λ {t1} {t2} → All→∀∈ us (t1 , t2)))
              , (λ _ → false!))
              (unify (uv , cs) (gen-constr-wf e eq [] [] .snd .snd .fst)))
   (gen-constr [] e (mkstate 0 [] []))
   refl

-- TODO completeness?
