{-# OPTIONS --safe #-}
module McBride.Unification where

open import Prelude
open import Meta.Effect

open import Data.Reflects
open import Data.Fin.Inductive
open import Data.Maybe as Maybe
open import Data.Maybe.Correspondences.Unary.Partial
open import Data.Star
open import Data.Sum as Sum
open import Data.List
open import Data.List.Correspondences.Unary.All
open import Data.List.Operations.Properties

open import McBride.Ty
open import McBride.Substitution

check : ∀ {n} → Var (suc n) → Ty (suc n) → Maybe (Ty n)
check x (`` y)    = ``_ <$> thick x y
check x (p ⟶ q) = _⟶_ <$> check x p <*> check x q
check x  con      = just con

-- chain of substitutions

data _//_ : ℕ → ℕ → 𝒰 where
  _／_ : ∀ {m} → Ty m → Var (suc m) → suc m // m

_⇝⋆_ : ℕ → ℕ → 𝒰
m ⇝⋆ n = Star _//_ m n

-- collapse the chain into a mathematical substitution

conv : ∀ {x y} → x // y → x ⇝ y
conv (t′ ／ v) = (v ≔ t′)

sub : ∀ {m n} → m ⇝⋆ n → m ⇝ n
sub = star-foldr {S = _⇝_} ⇝id (flip _◇_ ∘ conv)

_⇝⋆□ : ℕ → 𝒰
m ⇝⋆□ = Σ[ n ꞉ ℕ ] (m ⇝⋆ n)

_／_◅?_ : ∀ {m} → Ty m → Var (suc m) → m ⇝⋆□ → suc m ⇝⋆□
t′ ／ x ◅? (n , σ) = n , (t′ ／ x) ◅ σ

-- unification

flex-flex : ∀ {m} → Var m → Var m → m ⇝⋆□
flex-flex {m = suc m} x y =
  Maybe.rec
    (suc m , ε refl)
    (λ y′ → m , star-sng ((`` y′) ／ x))
    (thick x y)

flex-rigid : ∀ {m} → Var m → Ty m → Maybe (m ⇝⋆□)
flex-rigid {m = suc m} x t =
  map (λ t′ → m , star-sng (t′ ／ x)) (check x t)

amgu : ∀ {m} → Ty m → Ty m → m ⇝⋆□ → Maybe (m ⇝⋆□)
amgu  con         con        acc                            = just acc
amgu  con        (pt ⟶ qt)  acc                            = nothing
amgu (ps ⟶ qs)  con         acc                            = nothing
amgu (ps ⟶ qs) (pt ⟶ qt)  acc                            = amgu ps pt acc >>= amgu qs qt
amgu (`` xs)     (`` xt)    (n , ε e)                       = just (flex-flex xs xt)
amgu (`` xs)      t         (n , ε e)                       = flex-rigid xs t
amgu  s          (`` xt)    (n , ε e)                       = flex-rigid xt s
amgu  s           t         (n , _◅_ {x = suc m} (r ／ z) σ) = -- omitting the match on x triggers a termination error
  map (r ／ z ◅?_) $
  amgu (substitute (z ≔ r) s) (substitute (z ≔ r) t) (n , σ)

mgu : ∀ {m} → Ty m → Ty m → Maybe (m ⇝⋆□)
mgu {m} s t = amgu s t (m , ε refl)

-- TODO is pre-weakening them a good idea?
mgu-list : ∀ {m} → List (Ty m × Ty m) → Maybe (m ⇝⋆□)
mgu-list {m} []             = just (m , ε refl)
mgu-list     ((x , y) ∷ ls) = mgu-list ls >>= amgu x y

-- check properties

Step : ℕ → 𝒰
Step n = Ty n ⊎ Ty n

-- one-hole context
Ctx1 : ℕ → 𝒰
Ctx1 n = List (Step n)

-- plugging the hole
_+:_ : ∀ {n} → Ctx1 n → Ty n → Ty n
[]           +: t = t
(inl r ∷ ps) +: t = (ps +: t) ⟶ r
(inr l ∷ ps) +: t = l ⟶ (ps +: t)

+:-++ : ∀ {n} {ps qs : Ctx1 n} {t} → (ps ++ qs) +: t ＝ ps +: (qs +: t)
+:-++ {ps = []}         = refl
+:-++ {ps = inl r ∷ ps} = ap (_⟶ r) (+:-++ {ps = ps})
+:-++ {ps = inr l ∷ ps} = ap (l ⟶_) (+:-++ {ps = ps})

substitute-steps : {m n : ℕ} → (m ⇝ n) → Ctx1 m → Ctx1 n
substitute-steps f = map (Sum.dmap (substitute f) (substitute f))

+:-subst : ∀ {m n} {f : m ⇝ n} {ps : Ctx1 m} {t}
         → substitute f (ps +: t) ＝ substitute-steps f ps +: substitute f t
+:-subst     {ps = []}         = refl
+:-subst {f} {ps = inl r ∷ ps} = ap (_⟶ substitute f r) (+:-subst {ps = ps})
+:-subst {f} {ps = inr l ∷ ps} = ap (substitute f l ⟶_) (+:-subst {ps = ps})

check-spec : {n : ℕ} → Var (suc n) → Ty (suc n) → Maybe (Ty n) → 𝒰
check-spec {n} x t m =
  Part (Σ[ ps ꞉ List (Step (suc n)) ] (t ＝ ps +: (`` x)))
       (λ t′ → t ＝ substitute (rename (thin x)) t′) m

check-correct : ∀ {n} x t → check-spec x t (check {n} x t)
check-correct x (`` y)    =
  Part-map
    (λ e → [] , ap ``_ e)
    (λ e → ap ``_ e)
    (thick-correct x y)
check-correct x (p ⟶ q) =
  Part-map2
    (λ where (psq , eq) → inl q ∷ psq , ap (_⟶ q) eq)
    (λ where (psp , ep) → inr p ∷ psp , ap (p ⟶_) ep)
    (λ ep eq → ap² _⟶_ ep eq)
    (check-correct x p)
    (check-correct x q)
check-correct x con       = justP refl

-- sub properties

sub-refl : ∀ {m} → sub {m} refl ＝ ⇝id
sub-refl {m} = star-foldr-emp (λ {x} → ⇝id {m = x}) {tr = flip _◇_ ∘ conv}

sub-◅ : ∀ {m n} {p : suc m // m} {s} → sub {m = suc m} {n = n} (p ◅ s) ＝ sub s ◇ conv p
sub-◅ = refl

sub-sng : ∀ {m x t} → sub {n = m} (star-sng (t ／ x)) ＝ (x ≔ t)
sub-sng {x} {t} = ap (_◇ (x ≔ t)) sub-refl ∙ ◇-id-l

sub-◇ : ∀ {m n k} {α : m ⇝⋆ n} {β : n ⇝⋆ k}
       → sub {m} (α ∙ β) ＝ sub β ◇ sub α
sub-◇ {α} {β} =
  star-foldr-trans-morph ⇝id conv (flip _◇_)
    ◇-id-r (λ {x} {y} {z} {w} {a} {b} {c} → ◇-assoc {f = c} {g = b} {h = a})
    α β

-- unifier

unifies : ∀ {m} → Ty m → Ty m → ⇝P m
unifies s t f = substitute f s ＝ substitute f t

unifies-comm : ∀ {m n} {s t : Ty m} {f : m ⇝ n}
             → unifies s t f ≃ unifies t s f
unifies-comm {s} {t} = prop-extₑ! _⁻¹ _⁻¹

unifies-fork : ∀ {m n} {s₁ t₁ s₂ t₂ : Ty m} {f : m ⇝ n}
             → unifies (s₁ ⟶ s₂) (t₁ ⟶ t₂) f ≃ unifies s₁ t₁ f × unifies s₂ t₂ f
unifies-fork {s₁} {t₁} {s₂} {t₂} =
  prop-extₑ! ⟶-inj λ (x , y) → ap² _⟶_ x y

unifies-comp : ∀ {m n k q} {s t : Ty m} {f : n ⇝ k} {g : m ⇝ n} {h : k ⇝ q}
             → ⇝P◇ (unifies s t) (f ◇ g) h ≃ ⇝P◇ (unifies (substitute g s) (substitute g t)) f h
unifies-comp {s} {t} {g} =
  prop-extₑ!
    (λ e → substitute-comp s ⁻¹ ∙ subst (unifies s t) (◇-assoc {h = g} ⁻¹) e ∙ substitute-comp t)
    λ e → subst (unifies s t) (◇-assoc {h = g}) (substitute-comp s ∙ e ∙ substitute-comp t ⁻¹)

DCl-unifies : ∀ {m} {s t : Ty m} → DCl (unifies s t)
DCl-unifies {s} {t} f g (h , e) u =
  subst (unifies s t) e $
  substitute-comp s ∙ ap (substitute h) u ∙ substitute-comp t ⁻¹

unifies-list : ∀ {m} → List (Ty m × Ty m) → ⇝P m
unifies-list ls f = All (λ where (x , y) → unifies x y f) ls

DCl-unifies-list : ∀ {m} {ls : List (Ty m × Ty m)} → DCl (unifies-list ls)
DCl-unifies-list {ls} f g le =
  all-map (λ where {x = x , y} → DCl-unifies {s = x} {t = y} f g le)

-- simple unification problem

trivial-problem-lemma : ∀ {m n} {t : Ty m} {f : m ⇝ n}
                      → Max⇝ (⇝P◇ (unifies t t) f) ⇝id
trivial-problem-lemma = refl , λ f′ _ → ≤⇝-id

variable-elim-lemma : ∀ {m} {x : Var (suc m)} {t : Ty m}
                    → Max⇝ (unifies (`` x) (substitute (rename (thin x)) t)) (x ≔ t)
variable-elim-lemma {x} {t} =
      for-same {x = x} ∙ substitute-id t ⁻¹
    ∙ ap (λ q → substitute q t) (fun-ext λ y → for-thin {x = x} ⁻¹)
    ∙ substitute-comp t
  , λ f′ u → (f′ ∘ thin x)
  , fun-ext λ y →
      Maybe.elim
        (λ q → thick x y ＝ q → thick-spec x y q → (((f′ ∘ thin x) ◇ (x ≔ t)) y) ＝ f′ y)
        (λ et p →   ap (λ q → substitute (f′ ∘ thin x) (Maybe.rec t ``_ q)) et
                  ∙ substitute-comp t ∙ u ⁻¹
                  ∙ ap f′ (Part-nothing p ⁻¹))
        (λ j et p →   ap (λ q → substitute (f′ ∘ thin x) (Maybe.rec t ``_ q)) et
                    ∙ ap f′ (Part-just p ⁻¹))
        (thick x y) refl (thick-correct x y)

no-cycle-lemma : ∀ {n} {ps : Ctx1 n} {t} → ps +: t ＝ t → ps ＝ []
no-cycle-lemma {ps = []}                       e = refl
no-cycle-lemma {ps = inl r ∷ ps} {t = `` x}    e = ⊥.absurd (``≠⟶ (e ⁻¹))
no-cycle-lemma {ps = inr l ∷ ps} {t = `` x}    e = ⊥.absurd (``≠⟶ (e ⁻¹))
no-cycle-lemma {ps = inl r ∷ ps} {t = p ⟶ q} e =
  let (ep , _) = ⟶-inj e in
  false! (no-cycle-lemma {ps = ps ∷r inl q} {t = p}
          (ap (_+: p) (snoc-append ps) ∙ +:-++ {ps = ps}  ∙ ep))
no-cycle-lemma {ps = inr l ∷ ps} {t = p ⟶ q} e =
  let (_ , eq) = ⟶-inj e in
  false! (no-cycle-lemma {ps = ps ∷r inr p} {t = q}
          (ap (_+: q) (snoc-append ps) ∙ +:-++ {ps = ps}  ∙ eq))
no-cycle-lemma {ps = inl r ∷ ps} {t = con}     e = ⊥.absurd (⟶≠con e)
no-cycle-lemma {ps = inr l ∷ ps} {t = con}     e = ⊥.absurd (⟶≠con e)

no-unify-+var : ∀ {m} {x : Var m} {p ps}
             → ⇝P∅ (unifies (`` x) ((p ∷ ps) +: (`` x)))
no-unify-+var {p} {ps} f u =
  false! $ no-cycle-lemma ((u ∙ +:-subst {f = f} {ps = p ∷ ps}) ⁻¹)

flex-flex-correct : ∀ {m} {x y : Var m}
                  → Max⇝ (unifies (`` x) (`` y)) (sub (flex-flex x y .snd))
flex-flex-correct {m = suc m} {x} {y} =
  Maybe.elim
    (λ q → thick-spec x y q
         → Max⇝ (unifies (`` x) (`` y))
                 (sub ((Maybe.rec {B = suc m ⇝⋆□}
                                 (suc m , ε refl)
                                 (λ y′ → m , star-sng ((`` y′) ／ x)) q) .snd)))
    (λ p → subst (Max⇝ (unifies (`` x) (`` y))) (sub-refl ⁻¹) $
              subst (λ q → Max⇝ (unifies (`` x) (`` q)) ⇝id) (Part-nothing p ⁻¹) $
              trivial-problem-lemma {t = `` x} {f = ⇝id})
    (λ j p → subst (Max⇝ (unifies (`` x) (`` y))) (sub-sng {x = x} ⁻¹) $
                subst (λ q → Max⇝ (unifies (`` x) (`` q)) (x ≔ (`` j))) (Part-just p ⁻¹) $
                variable-elim-lemma)
    (thick x y) (thick-correct x y)

amgu-spec : ∀ {m} → Ty m → Ty m → m ⇝⋆□ → Maybe (m ⇝⋆□) → 𝒰
amgu-spec {m} s t (l , ρ) ms =
  Part (⇝P∅ (⇝P◇ (unifies s t) (sub ρ)))
       (λ where (n , σ) → Σ[ τ ꞉ l ⇝⋆ n ] (σ ＝ ρ ∙ τ) × Max⇝ (⇝P◇ (unifies s t) (sub ρ)) (sub τ))
       ms

amgu-correct : ∀ {m} s t ρ → amgu-spec {m} s t ρ (amgu s t ρ)
amgu-correct con          con        (l , ρ)        =
  justP ( ε refl
        , star-trans-id-r ρ ⁻¹
        , subst (Max⇝ (⇝P◇ (unifies con con) (sub ρ)))
                 (sub-refl ⁻¹)
                 (trivial-problem-lemma {t = con} {f = sub ρ}))
amgu-correct con         (pt ⟶ qt)  acc        =
  nothingP (λ f e → ⟶≠con (e ⁻¹))
amgu-correct (ps ⟶ qs)   con        acc        =
  nothingP (λ f e → ⟶≠con e)
amgu-correct (ps ⟶ qs) (pt ⟶ qt)  (l , ρ)   =
  Part-bind
    -- $-notation breaks down
    (λ p {n} → (⇝P∅≃ (⇝P◇≃ {f = sub ρ} λ f →
                    unifies-fork {s₁ = ps} {t₁ = pt} {s₂ = qs} {t₂ = qt} {f = f}) ⁻¹) .fst $
               failure-propagation-lemma1 {n = l} {p = unifies ps pt} {q = unifies qs qt} {a = sub ρ}
                    λ {n = n′} → p {n = n′})
    (λ where {x = k , ζ} →
              λ where (φ , es , mx) →
                       Part-weaken
                        (λ p {n} → (⇝P∅≃ (⇝P◇≃ {f = sub ρ} λ f → unifies-fork {s₁ = ps} {t₁ = pt} {s₂ = qs} {t₂ = qt} {f = f}) ⁻¹) .fst $
                                   failure-propagation-lemma2 {n = l} {k = k} {p = unifies ps pt} {q = unifies qs qt} {a = sub ρ} {f = sub φ} mx $
                                   subst (λ q → ⇝P∅ (⇝P◇ (unifies qs qt) q)) (ap sub es ∙ sub-◇ {α = ρ} {β = φ}) (λ {n = n′} → p {n = n′}) )
                        (λ where {x = o , ψ} →
                                   λ where (τ , eτ , mxτ) →
                                              φ ∙ τ
                                            , eτ ∙ ap (_∙ τ) es ∙ star-trans-assoc ρ φ τ
                                            , (subst (Max⇝ (⇝P◇ (unifies (ps ⟶ qs) (pt ⟶ qt)) (sub ρ))) (sub-◇ {α = φ} {β = τ} ⁻¹) $
                                               (Max⇝≃ (⇝P◇≃ {f = sub ρ} λ f →
                                                  unifies-fork {s₁ = ps} {t₁ = pt} {s₂ = qs} {t₂ = qt} {f = f}) (sub τ ◇ sub φ) ⁻¹) .fst $
                                               optimist-lemma {q = unifies qs qt} {a = sub ρ} {f = sub φ} {g = sub τ}
                                                          (DCl-unifies {s = ps} {t = pt}) mx $
                                               subst (λ q → Max⇝ (⇝P◇ (unifies qs qt) q) (sub τ)) (ap sub es ∙ sub-◇ {α = ρ} {β = φ}) mxτ))
                        (amgu-correct qs qt (k , ζ)))
    (amgu-correct ps pt (l , ρ))
amgu-correct (`` xs) (`` xt) (n , ε e) =
  justP $
  Jₚ (λ k ek → let (l , σ) = flex-flex xs xt in
               Σ[ τ ꞉ k ⇝⋆ l ] (σ ＝ ε ek ∙ τ)
                             × Max⇝ (⇝P◇ (unifies (`` xs) (`` xt)) (sub (ε ek))) (sub τ))
     ( let σ = flex-flex xs xt .snd in
         σ , star-trans-id-l σ ⁻¹
       , subst (λ q → Max⇝ (⇝P◇ (unifies (`` xs) (`` xt)) q) (sub σ))
               (sub-refl ⁻¹)
               flex-flex-correct)
     e
amgu-correct {m = suc m} (`` xs) (pt ⟶ qt) (n , ε e) =
  Part-map
    (λ where
         ([] , eq)             f pu → ``≠⟶ (eq ⁻¹)
         (p ∷ ls , eq) {n = k}      →
            Jₚ (λ y ey → (f : y ⇝ k) → ¬ₜ ⇝P◇ (unifies (`` xs) (pt ⟶ qt)) (sub (ε ey)) f)
                (λ f → no-unify-+var {x = xs} {p = p} {ps = ls} f ∘
                       subst (λ q → unifies (`` xs) q f) eq ∘
                       subst (λ q → ⇝P◇ (unifies (`` xs) (pt ⟶ qt)) q f) sub-refl)
                e)
    (λ {x} eq →
       Jₚ (λ y ey → Σ[ τ ꞉ y ⇝⋆ m ] (star-sng (x ／ xs) ＝ ε ey ∙ τ) × Max⇝ (⇝P◇ (unifies (`` xs) (pt ⟶ qt)) (sub (ε ey))) (sub τ))
          ( star-sng (x ／ xs)
          , star-trans-id-l (star-sng (x ／ xs)) ⁻¹
          , (subst (λ q → Max⇝ (⇝P◇ (unifies (`` xs) (pt ⟶ qt)) q) (sub (star-sng (x ／ xs)))) (sub-refl ⁻¹) $
             subst (λ q → Max⇝ (unifies (`` xs) (pt ⟶ qt)) q) (sub-sng {x = xs} ⁻¹) $
             subst (λ q → Max⇝ (unifies (`` xs) q) (xs ≔ x)) (eq ⁻¹) $
             variable-elim-lemma))
          e)
    (check-correct xs (pt ⟶ qt))
amgu-correct {m = suc m} (`` xs) con (n , ε e) =
  justP $
  Jₚ (λ y ey → Σ[ τ ꞉ y ⇝⋆ m ] (star-sng (con ／ xs) ＝ ε ey ∙ τ) × Max⇝ (⇝P◇ (unifies (`` xs) con) (sub (ε ey))) (sub τ))
          ( star-sng (con ／ xs)
          , star-trans-id-l (star-sng (con ／ xs)) ⁻¹
          , (subst (λ q → Max⇝ (⇝P◇ (unifies (`` xs) con) q) (sub (star-sng (con ／ xs)))) (sub-refl ⁻¹) $
             subst (λ q → Max⇝ (unifies (`` xs) con) q) (sub-sng {x = xs} ⁻¹) $
             variable-elim-lemma))
          e
amgu-correct {m = suc m} (ps ⟶ qs) (`` xt) (n , ε e) =
  Part-map
    (λ where
         ([] , eq)             f pu → ``≠⟶ (eq ⁻¹)
         (p ∷ ls , eq) {n = k}      →
           Jₚ (λ y ey → (f : y ⇝ k) → ¬ₜ ⇝P◇ (unifies (ps ⟶ qs) (`` xt)) (sub (ε ey)) f)
                (λ f x → no-unify-+var {x = xt} {p = p} {ps = ls} f $
                         unifies-comm {s = (p ∷ ls) +: (`` xt)} $
                         subst (λ q → unifies q (`` xt) f) eq $
                         subst (λ q → ⇝P◇ (unifies (ps ⟶ qs) (`` xt)) q f) sub-refl x)
                e)
    (λ {x} eq →
       Jₚ (λ y ey → Σ[ τ ꞉ y ⇝⋆ m ] (star-sng (x ／ xt) ＝ ε ey ∙ τ) × Max⇝ (⇝P◇ (unifies (ps ⟶ qs) (`` xt)) (sub (ε ey))) (sub τ))
          ( star-sng (x ／ xt)
          , star-trans-id-l (star-sng (x ／ xt)) ⁻¹
          , (subst (λ q → Max⇝ (⇝P◇ (unifies (ps ⟶ qs) (`` xt) ) q) (sub (star-sng (x ／ xt)))) (sub-refl ⁻¹) $
             subst (λ q → Max⇝ (unifies (ps ⟶ qs) (`` xt) ) q) (sub-sng {x = xt} ⁻¹) $
             subst (λ q → Max⇝ (unifies q (`` xt)) (xt ≔ x)) (eq ⁻¹) $
             (Max⇝≃ (λ f → unifies-comm {s = substitute (rename (thin xt)) x}) (xt ≔ x) ⁻¹) .fst $
             variable-elim-lemma))
          e)
    (check-correct xt (ps ⟶ qs))
amgu-correct {m = suc m} con (`` xt) (n , ε e) =
  justP $
  Jₚ (λ y ey → Σ[ τ ꞉ y ⇝⋆ m ] (star-sng (con ／ xt) ＝ ε ey ∙ τ) × Max⇝ (⇝P◇ (unifies con (`` xt)) (sub (ε ey))) (sub τ))
     ( star-sng (con ／ xt)
     , star-trans-id-l (star-sng (con ／ xt)) ⁻¹
     , (subst (λ q → Max⇝ (⇝P◇ (unifies con (`` xt)) q) (sub (star-sng (con ／ xt)))) (sub-refl ⁻¹) $
        subst (λ q → Max⇝ (unifies con (`` xt)) q) (sub-sng {x = xt} ⁻¹) $
        (Max⇝≃ (λ f → unifies-comm {s = con} {f = f}) (xt ≔ con) ⁻¹) .fst $
        variable-elim-lemma))
     e
-- this is bullshit
amgu-correct (`` xs)    (`` xt)     (n , _◅_ {x = suc m} (r ／ z) σ) =
  Part-map
    (λ np → ⇝P∅≃ (λ h → unifies-comp {s = `` xs} {t = `` xt} {f = sub σ} {g = z ≔ r} {h = h} ⁻¹) .fst (λ {n = k} → np {n = k}))
    (λ where {x = (k , φ)} →
               λ where (τ , eτ , mx) →
                          τ
                        , ap ((r ／ z) ◅_) eτ
                        , Max⇝≃ (⇝P◇≃ (λ h′ → unifies-comp {s = `` xs} {t = `` xt} {f = sub σ} {g = z ≔ r} {h = h′} ⁻¹)) (sub τ) .fst mx)
    (amgu-correct ((z ≔ r) xs) ((z ≔ r) xt) (n , σ))
amgu-correct (`` xs)    (pt ⟶ qt) (n , _◅_ {x = suc m} (r ／ z) σ) =
  Part-map
    (λ np → ⇝P∅≃ (λ h → unifies-comp {s = `` xs} {t = pt ⟶ qt} {f = sub σ} {g = z ≔ r} {h = h} ⁻¹) .fst (λ {n = k} → np {n = k}))
    (λ where {x = (k , φ)} →
               λ where (τ , eτ , mx) →
                          τ
                        , ap ((r ／ z) ◅_) eτ
                        , Max⇝≃ (⇝P◇≃ (λ h′ → unifies-comp {s = `` xs} {t = pt ⟶ qt} {f = sub σ} {g = z ≔ r} {h = h′} ⁻¹)) (sub τ) .fst mx)
    (amgu-correct ((z ≔ r) xs) (substitute (z ≔ r) pt ⟶ substitute (z ≔ r) qt) (n , σ))
amgu-correct (`` xs)     con        (n , _◅_ {x = suc m} (r ／ z) σ) =
  Part-map
    (λ np → ⇝P∅≃ (λ h → unifies-comp {s = `` xs} {t = con} {f = sub σ} {g = z ≔ r} {h = h} ⁻¹) .fst (λ {n = k} → np {n = k}))
    (λ where {x = (k , φ)} →
               λ where (τ , eτ , mx) →
                          τ
                        , ap ((r ／ z) ◅_) eτ
                        , Max⇝≃ (⇝P◇≃ (λ h′ → unifies-comp {s = `` xs} {t = con} {f = sub σ} {g = z ≔ r} {h = h′} ⁻¹)) (sub τ) .fst mx)
    (amgu-correct ((z ≔ r) xs) con (n , σ))
amgu-correct (ps ⟶ qs) (`` xt)    (n , _◅_ {x = suc m} (r ／ z) σ) =
  Part-map
    (λ np → ⇝P∅≃ (λ h → unifies-comp {s = ps ⟶ qs} {t = `` xt} {f = sub σ} {g = z ≔ r} {h = h} ⁻¹) .fst (λ {n = k} → np {n = k}))
    (λ where {x = (k , φ)} →
               λ where (τ , eτ , mx) →
                          τ
                        , ap ((r ／ z) ◅_) eτ
                        , Max⇝≃ (⇝P◇≃ (λ h′ → unifies-comp {s = ps ⟶ qs} {t = `` xt} {f = sub σ} {g = z ≔ r} {h = h′} ⁻¹)) (sub τ) .fst mx)
    (amgu-correct (substitute (z ≔ r) ps ⟶ substitute (z ≔ r) qs) ((z ≔ r) xt) (n , σ))
amgu-correct  con        (`` xt)    (n , _◅_ {x = suc m} (r ／ z) σ) =
  Part-map
    (λ np → ⇝P∅≃ (λ h → unifies-comp {s = con} {t = `` xt} {f = sub σ} {g = z ≔ r} {h = h} ⁻¹) .fst (λ {n = k} → np {n = k}))
    (λ where {x = (k , φ)} →
               λ where (τ , eτ , mx) →
                          τ
                        , ap ((r ／ z) ◅_) eτ
                        , Max⇝≃ (⇝P◇≃ (λ h′ → unifies-comp {s = con} {t = `` xt} {f = sub σ} {g = z ≔ r} {h = h′} ⁻¹)) (sub τ) .fst mx)
    (amgu-correct con ((z ≔ r) xt) (n , σ))

mgu-spec : ∀ {m} → Ty m → Ty m → Maybe (m ⇝⋆□) → 𝒰
mgu-spec {m} s t ms =
  Part (⇝P∅ (unifies s t))
       (λ where (n , σ) → Max⇝ (unifies s t) (sub σ))
       ms

mgu-correct : ∀ {m} s t → mgu-spec {m} s t (mgu s t)
mgu-correct {m} s t =
  Part-weaken
    (λ np → subst (λ q → ⇝P∅ (⇝P◇ (unifies s t) q)) sub-refl λ {n = k} → np {n = k})
    (λ where {x = (k , φ)} →
               λ where (τ , eτ , mx) →
                         (subst (Max⇝ (unifies s t)) (ap sub (star-trans-id-l τ ⁻¹ ∙ eτ ⁻¹)) $
                          subst (λ q → Max⇝ (⇝P◇ (unifies s t) q) (sub τ)) sub-refl mx))
    (amgu-correct s t (m , ε refl))

mgu-list-spec : ∀ {m} → List (Ty m × Ty m) → Maybe (m ⇝⋆□) → 𝒰
mgu-list-spec {m} ls ms =
  Part (⇝P∅ (unifies-list ls))
       (λ where (n , σ) → Max⇝ (unifies-list ls) (sub σ))
       ms

mgu-list-correct : ∀ {m} ls → mgu-list-spec {m} ls (mgu-list ls)
mgu-list-correct []             =
  justP (subst (Max⇝ (unifies-list [])) (sub-refl ⁻¹) ([] , λ f′ _ → ≤⇝-id))
mgu-list-correct ((x , y) ∷ ls) =
  Part-bind
    (λ np → ⇝P∅≃ (λ f → ×-swap ∙ all-×≃ {P = λ where (x , y) → unifies x y f} ⁻¹) .fst $
            failure-propagation-lemma1 {q = unifies x y}
              λ {n = k} → np {n = k})
    (λ where {x = (k , φ)} mx →
               Part-weaken
                 (λ np → ⇝P∅≃ (λ f → ×-swap ∙ all-×≃ {P = λ where (x , y) → unifies x y f} ⁻¹) .fst $
                         failure-propagation-lemma2 {q = unifies x y}
                           mx λ {n = k} → np {n = k})
                 (λ where {x = (l , ψ)} →
                            λ where (τ , eτ , mx′) →
                                      subst (λ q → Max⇝ (unifies-list ((x , y) ∷ ls)) (sub q)) (eτ ⁻¹) $
                                      subst (Max⇝ (unifies-list ((x , y) ∷ ls))) (sub-◇ {α = φ} ⁻¹) $
                                      Max⇝≃ (λ f → ×-swap ∙ all-×≃ {P = λ where (x , y) → unifies x y f} ⁻¹) (sub τ ◇ sub φ) .fst $
                                      optimist-lemma {a = ⇝id} DCl-unifies-list mx mx′)
                 (amgu-correct x y (k , φ)))
    (mgu-list-correct ls)

