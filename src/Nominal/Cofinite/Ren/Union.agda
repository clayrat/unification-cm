{-# OPTIONS --safe #-}
module Nominal.Cofinite.Ren.Union where

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

open import Nominal.Term
open import Nominal.Cofinite.Base
open import Nominal.Cofinite.Ren

-- compatibility

compat : Ren → Ren → 𝒰
compat s t = (x : Id) → x ∈ s .supr → x ∈ t .supr → (s .eqvr $ x) ＝ (t .eqvr $ x)

compat-prop : ∀ {s t} → is-prop (compat s t)
compat-prop = Π-is-of-hlevel 1 λ x → fun-is-of-hlevel 1 $ fun-is-of-hlevel 1 hlevel!

compat? : Ren → Ren → Bool
compat? s t = allₛ (λ x → (s .eqvr $ x) == (t .eqvr $ x)) (s .supr ∩∷ t .supr)

Reflects-compat : ∀ {s t} → Reflects (compat s t) (compat? s t)
Reflects-compat {s} {t} =
  Reflects.dmap
    (λ f x x∈s x∈t → f x (∈-∩∷ x∈s x∈t))
    (contra λ f x x∈st → let (x∈s , x∈t) = ∩∷-∈ x∈st in f x x∈s x∈t)
    (Reflects-allₛ (λ x → hlevel!) (λ x → Reflects-ℕ-Path {m = s .eqvr $ x}))

Dec-compat : ∀ s t → Dec (compat s t)
Dec-compat s t .does = compat? s t
Dec-compat s t .proof = Reflects-compat {s} {t}

compat-sym : ∀ {s t} → compat s t → compat t s
compat-sym c x x∈t x∈s = c x x∈s x∈t ⁻¹

compat-iter : ∀ {s t} → compat s t
             → (x : Id) → x ∈ s .supr → x ∈ t .supr
             → ∀ n → iter n (s .eqvr $_) x ＝ iter n (t .eqvr $_) x
compat-iter         c x x∈s x∈t  zero   = refl
compat-iter {s} {t} c x x∈s x∈t (suc n) =
  let ih = compat-iter {s = s} {t = t} c x x∈s x∈t n in
    c (iter n (s .eqvr .fst) x)
      (ren-sup-iter→ {r = s} {n = n} x∈s)
      (subst (_∈ t .supr) (ih ⁻¹) (ren-sup-iter→ {r = t} {n = n} x∈t))
  ∙ ap (t .eqvr $_) ih

compat-orbit : ∀ {s t} → compat s t
             → (x : Id) → x ∈ s .supr → x ∈ t .supr → orbit s x ＝ orbit t x
compat-orbit {s} {t} c x x∈s x∈t =
  let e = c x x∈s x∈t in
  set-ext λ z →
    prop-extₑ!
      (λ z∈os →
           let (n , nle , ne) = orbit-mem z∈os in
           subst (_∈ orbit t x) (compat-iter {s = s} {t = t} c x x∈s x∈t n ⁻¹ ∙ ne) (mem-orbit {n = n}))
      λ z∈ot →
           let (n , nle , ne) = orbit-mem z∈ot in
           subst (_∈ orbit s x) (compat-iter {s = s} {t = t} c x x∈s x∈t n ∙ ne) (mem-orbit {n = n})

compat-flp : ∀ {s t} → compat s t → compat (flp s) (flp t)
compat-flp {s} {t} c x x∈s x∈t =
    osize-inv {r = s} {x = x}
  ∙ ap (λ q → iter q (s .eqvr $_) x)
       (  suc-inj $   orbit-size ⁻¹
                    ∙ ap sizeₛ (compat-orbit c x x∈s x∈t)
                    ∙ orbit-size)
  ∙ compat-iter {s = s} {t = t} c x x∈s x∈t (osize t x)
  ∙ osize-inv {r = t} {x = x} ⁻¹

-- TODO adhoc?
compat-∈-→ : ∀ {s t} {x : Id}
     → compat s t
     → (t .eqvr $ x) ∈ s .supr
     → x ∈ s .supr
compat-∈-→ {s} {t} {x} c tx∈s =
  Dec.elim
    {C = λ _ → x ∈ s .supr}
    (λ x∈t → subst (_∈ₛ s .supr)
                    (  compat-flp {s = s} {t = t} c (t .eqvr $ x) tx∈s (ren-sup→ {r = t} x∈t)
                     ∙ is-equiv→unit (t .eqvr .snd) x) $
              ren-sup← {r = s} tx∈s)
    (λ x∉t → subst (_∈ s .supr) (t .cofr x∉t) tx∈s)
    (x ∈? t .supr)

compat-∈-← : ∀ {s t} {x : Id}
    → compat s t
    → (t .eqvr ⁻¹ $ x) ∈ s .supr
    → x ∈ s .supr
compat-∈-← {s} {t} {x} c tx∈s =
  Dec.elim
    {C = λ _ → x ∈ s .supr}
    (λ x∈t → subst (_∈ₛ s .supr)
                    (  c (t .eqvr ⁻¹ $ x) tx∈s (ren-sup← {r = t} x∈t)
                     ∙ is-equiv→counit (t .eqvr .snd) x) $
              ren-sup→ {r = s} tx∈s)
    (λ x∉t → subst (_∈ s .supr) (cofr⁻¹ t x∉t) tx∈s)
    (x ∈? t .supr)

compat-comm : ∀ {s t} → compat s t → s ◇↔ t ＝ t ◇↔ s
compat-comm {s} {t} c =
  ren-ext
    (equiv-ext $ fun-ext λ z →
      Dec.elim
         {C = λ _ → (s .eqvr $ t .eqvr $ z) ＝ (t .eqvr $ s .eqvr $ z)}
         (λ z∈t → Dec.elim
                    {C = λ _ → (s .eqvr $ t .eqvr $ z) ＝ (t .eqvr $ s .eqvr $ z)}
                    (λ z∈s →   ap (s .eqvr $_) (c z z∈s z∈t ⁻¹)
                              ∙ compat-iter {s = s} {t = t} c z z∈s z∈t 2
                              ∙ ap (t .eqvr $_) (c z z∈s z∈t ⁻¹))
                    (λ z∉s →   s .cofr (contra (compat-∈-→ {s = s} {t = t} c) z∉s)
                              ∙ ap (t .eqvr $_) (s .cofr z∉s ⁻¹))
                    (z ∈? s .supr))
         (λ z∉t →   ap (s .eqvr $_) (t .cofr z∉t)
                   ∙ t .cofr (contra (compat-∈-→ {s = t} {t = s} (compat-sym {s = s} {t = t} c)) z∉t) ⁻¹)
         (z ∈? t .supr))
    (∪∷-comm {x = t .supr})

-- union

compat-∪≃ : (s t : Ren) → compat s t
          → Id ≃ Id
compat-∪≃ s t c =
  ≅→≃ $
  make-iso to fro $
  make-inverses (fun-ext se) (fun-ext re)
  where
  to : Id → Id
  to x = if x ∈ₛ? s .supr
            then s .eqvr $ x
            else if x ∈ₛ? t .supr
                   then t .eqvr $ x
                   else x
  fro : Id → Id
  fro x = if x ∈ₛ? s .supr
            then s .eqvr ⁻¹ $ x
            else if x ∈ₛ? t .supr
                   then t .eqvr ⁻¹ $ x
                   else x
  se : ∀ x → to (fro x) ＝ x
  se x =
    Dec.elim
       {C = λ q → (if (if ⌊ q ⌋
                         then s .eqvr ⁻¹ $ x
                         else if x ∈ₛ? t .supr
                                then t .eqvr ⁻¹ $ x
                                else x) ∈ₛ? s .supr
                       then s .eqvr $ (if ⌊ q ⌋
                                         then s .eqvr ⁻¹ $ x
                                         else if x ∈ₛ? t .supr
                                                then t .eqvr ⁻¹ $ x
                                                else x)
                       else if (if ⌊ q ⌋
                                  then s .eqvr ⁻¹ $ x
                                  else if x ∈ₛ? t .supr
                                         then t .eqvr ⁻¹ $ x
                                         else x) ∈ₛ? t .supr
                                 then t .eqvr $ (if ⌊ q ⌋
                                                   then s .eqvr ⁻¹ $ x
                                                   else if x ∈ₛ? t .supr
                                                          then t .eqvr ⁻¹ $ x
                                                          else x)
                              else (if ⌊ q ⌋
                                     then s .eqvr ⁻¹ $ x
                                     else if x ∈ₛ? t .supr
                                            then t .eqvr ⁻¹ $ x
                                            else x))
                ＝ x}
       (λ x∈s →
          given-yes ren-sup← {r = s} x∈s
            return (λ q → (if ⌊ q ⌋
                              then s .eqvr $ (s .eqvr ⁻¹ $ x)
                             else if (s .eqvr ⁻¹ $ x) ∈ₛ? t .supr
                                   then t .eqvr $ (s .eqvr ⁻¹ $ x)
                                   else (s .eqvr ⁻¹ $ x))
                          ＝ x)
            then is-equiv→counit (s .eqvr .snd) x)
       (λ x∉s →
          Dec.elim
             {C = λ q → (if (if ⌊ q ⌋
                           then t .eqvr ⁻¹ $ x
                           else x) ∈ₛ? s .supr
                               then s .eqvr $ (if ⌊ q ⌋
                                                  then t .eqvr ⁻¹ $ x
                                                  else x)
                               else if (if ⌊ q ⌋
                                                 then t .eqvr ⁻¹ $ x
                                                 else x) ∈ₛ? t .supr
                                         then t .eqvr $ (if ⌊ q ⌋
                                                            then t .eqvr ⁻¹ $ x
                                                            else x)
                                      else (if ⌊ q ⌋
                                               then t .eqvr ⁻¹ $ x
                                               else x))
                        ＝ x}
             (λ x∈t →
                   given-no contra (compat-∈-← {s = s} {t = t} c) x∉s
                     return (λ q → (if ⌊ q ⌋
                               then s .eqvr $ (t .eqvr ⁻¹ $ x)
                               else if (t .eqvr ⁻¹ $ x) ∈ₛ? t .supr
                                         then t .eqvr $ (t .eqvr ⁻¹ $ x)
                                      else (t .eqvr ⁻¹ $ x))
                             ＝ x)
                     then (given-yes ren-sup← {r = t} x∈t
                                 return (λ q → (if ⌊ q ⌋
                                                  then t .eqvr $ (t .eqvr ⁻¹ $ x)
                                                  else (t .eqvr ⁻¹ $ x))
                                                ＝ x)
                                 then is-equiv→counit (t .eqvr .snd) x))
             (λ x∉t →
                  given-no x∉s
                     return (λ q → (if ⌊ q ⌋
                                       then s .eqvr $ x
                                       else if x ∈ₛ? t .supr
                                              then t .eqvr $ x
                                              else x)
                                    ＝ x)
                     then (given-no x∉t
                             return (λ q → (if ⌊ q ⌋
                                              then t .eqvr $ x
                                              else x)
                                    ＝ x)
                             then refl))
             (x ∈? t .supr))
       (x ∈? s .supr)
  re : ∀ x → fro (to x) ＝ x
  re x =
     Dec.elim
       {C = λ q → (if (if ⌊ q ⌋
                         then s .eqvr $ x
                         else if x ∈ₛ? t .supr
                                then t .eqvr $ x
                                else x) ∈ₛ? s .supr
                       then s .eqvr ⁻¹ $ (if ⌊ q ⌋
                                         then s .eqvr $ x
                                         else if x ∈ₛ? t .supr
                                                then t .eqvr $ x
                                                else x)
                       else if (if ⌊ q ⌋
                                  then s .eqvr $ x
                                  else if x ∈ₛ? t .supr
                                         then t .eqvr $ x
                                         else x) ∈ₛ? t .supr
                                 then t .eqvr ⁻¹ $ (if ⌊ q ⌋
                                                   then s .eqvr $ x
                                                   else if x ∈ₛ? t .supr
                                                          then t .eqvr $ x
                                                          else x)
                              else (if ⌊ q ⌋
                                     then s .eqvr $ x
                                     else if x ∈ₛ? t .supr
                                            then t .eqvr $ x
                                            else x))
                ＝ x}
      (λ x∈s →
           given-yes ren-sup→ {r = s} x∈s
                   return (λ q → (if ⌊ q ⌋
                                     then s .eqvr ⁻¹ $ (s .eqvr $ x)
                                     else if (s .eqvr $ x) ∈ₛ? t .supr
                                          then t .eqvr ⁻¹ $ (s .eqvr $ x)
                                          else (s .eqvr $ x))
                                 ＝ x)
                   then is-equiv→unit (s .eqvr .snd) x)
      (λ x∉s →
         Dec.elim
             {C = λ q → (if (if ⌊ q ⌋
                           then t .eqvr $ x
                           else x) ∈ₛ? s .supr
                               then s .eqvr ⁻¹ $ (if ⌊ q ⌋
                                                  then t .eqvr $ x
                                                  else x)
                               else if (if ⌊ q ⌋
                                                 then t .eqvr $ x
                                                 else x) ∈ₛ? t .supr
                                         then t .eqvr ⁻¹ $ (if ⌊ q ⌋
                                                            then t .eqvr $ x
                                                            else x)
                                      else (if ⌊ q ⌋
                                               then t .eqvr $ x
                                               else x))
                        ＝ x}
             (λ x∈t →
                   given-no contra (compat-∈-→ {s = s} {t = t} c) x∉s
                      return (λ q → (if ⌊ q ⌋
                               then s .eqvr ⁻¹ $ (t .eqvr $ x)
                               else if (t .eqvr $ x) ∈ₛ? t .supr
                                         then t .eqvr ⁻¹ $ (t .eqvr $ x)
                                      else (t .eqvr $ x))
                             ＝ x)
                     then (given-yes ren-sup→ {r = t} x∈t
                                 return (λ q → (if ⌊ q ⌋
                                                  then t .eqvr ⁻¹ $ (t .eqvr $ x)
                                                  else (t .eqvr $ x))
                                                ＝ x)
                                 then is-equiv→unit (t .eqvr .snd) x))
             (λ x∉t →
                   given-no x∉s
                     return (λ q → (if ⌊ q ⌋
                                       then s .eqvr ⁻¹ $ x
                                       else if x ∈ₛ? t .supr
                                              then t .eqvr ⁻¹ $ x
                                              else x)
                                    ＝ x)
                     then (given-no x∉t
                             return (λ q → (if ⌊ q ⌋
                                              then t .eqvr ⁻¹ $ x
                                              else x)
                                    ＝ x)
                             then refl))
             (x ∈? t .supr))
      (x ∈? s .supr)

∪↔ : (f g : Ren) → compat f g → Ren
∪↔ f g c .eqvr = compat-∪≃ f g c
∪↔ f g c .supr = f .supr ∪∷ g .supr
∪↔ f g c .cofr {x} x∉ =
  let ( x∉f , x∉g ) = ∉ₛ-∪∷ {xs = f .supr} x∉ in
    (given-no x∉f
       return (λ q → (if ⌊ q ⌋
                       then f .eqvr $ x
                       else if x ∈ₛ? g .supr
                              then g .eqvr $ x
                              else x) ＝ x)
       then
         (given-no x∉g
            return (λ q → (if ⌊ q ⌋
                             then g .eqvr $ x
                             else x) ＝ x)
            then refl))

∪↔-compat-l : ∀ {s t} {x : Id} → (c : compat s t) → x ∈ s .supr → ((∪↔ s t c) .eqvr $ x) ＝ (s .eqvr $ x)
∪↔-compat-l {s} {t} {x} c x∈s =
  given-yes x∈s
      return (λ q → (if ⌊ q ⌋
                       then s .eqvr $ x
                       else if x ∈ₛ? t .supr
                              then t .eqvr $ x
                              else x) ＝ (s .eqvr $ x))
      then refl

∪↔-compat-r : ∀ {s t} {x : Id} → (c : compat s t) → x ∈ t .supr → ((∪↔ s t c) .eqvr $ x) ＝ (t .eqvr $ x)
∪↔-compat-r {s} {t} {x} c x∈t =
  Dec.elim
   {C = λ q → (if ⌊ q ⌋
                       then s .eqvr $ x
                       else if x ∈ₛ? t .supr
                              then t .eqvr $ x
                              else x) ＝ (t .eqvr $ x)}
  (λ x∈s → c x x∈s x∈t)
  (λ _ → given-yes x∈t
            return (λ q → (if ⌊ q ⌋
                            then t .eqvr $ x
                            else x) ＝ (t .eqvr $ x))
            then refl)
  (x ∈? s .supr)
