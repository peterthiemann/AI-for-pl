module proof.LR-narrow.PendingUniversal where

-- File Charter:
--   * Eliminates a stored pending-target universal head at a fresh target bind.
--   * Applies the fresh target reveal to recover ordinary value imprecision.
--   * Supplies the semantic core of an imprecise-only universal peel.

open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_; proj₁; proj₂)
import Data.Maybe
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; cong; refl; sym; trans)

open import Types
open import CastTerms
open import Conversion using (replaceTy; 〖_,_↑_〗; makeConceal)
open import Reduction
import Eval as E
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.SlotSequence
open import LR-narrow.PendingTarget using (TargetTransparent)
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.UniversalFamily
open import proof.LR-narrow.PendingTarget
open import proof.LR-narrow.PendingTargetFrame
import proof.LR-narrow.Closure as ClosureProof
open import proof.LR-narrow.ReplaceImprecision using
  (replace-zero-open; open-shifted-body)
open import proof.LR-narrow.TypeApplication using (lift-precise-open)
open import proof.LR-narrow.BindStepExpansion using
  (related-imprecise-bind-step-expand)
open import proof.LR-narrow.UniversalReveal using
  (post-bind-weaken; reveal-type-app-step-question;
   conceal-type-app-step-question)

pending-target-universal-head : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty (suc Δᴵ)}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ} {k : ℕ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    (body : BodyImprecisionᵇ W Bᴾ Bᴵ)
    (r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ)
  → UniversalFamily W (bodyPᵇ body) Bᴾ Bᴵ (suc k) Vᴵ Vᴾ
  → let
      step = future-imprecise {Aᴵ = Rᴵ} (future-refl {W = W})
      W′ = impreciseBindWorld W Rᴵ
      resultᴵ = liftImpreciseBody step Bᴵ [ ＇ Fin.zero ]ᵗ
      related = fresh-target-lifted-open-transparent body r
    in ComputationsRelated W′ (FutureValueRelation related) (suc k)
          ((liftImpreciseTerm step Vᴵ
              ⦂∀ liftImpreciseBody step Bᴵ [ ＇ Fin.zero ])
            ↑ 〖 Fin.zero , ⇑ᵗ Rᴵ ↑ resultᴵ 〗)
          (liftPreciseTerm step Vᴾ
            ⦂∀ liftPreciseBody step Bᴾ [ liftPreciseTy step Rᴾ ])
pending-target-universal-head {W = W} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
    {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    body r fam =
  pending-target-reveal-computations slot result-related pending
  where
  step = future-imprecise {Aᴵ = Rᴵ} (future-refl {W = W})
  W′ = impreciseBindWorld W Rᴵ
  slot = fresh-target-slot W Rᴵ

  argument-related : TargetTransparent W′ slot
      (liftPreciseTy step Rᴾ) (＇ Fin.zero)
  argument-related = fresh-target-variable-transparent r

  result-related : TargetTransparent W′ slot
      (liftPreciseBody step Bᴾ [ liftPreciseTy step Rᴾ ]ᵗ)
      (liftImpreciseBody step Bᴵ [ ＇ Fin.zero ]ᵗ)
  result-related = fresh-target-lifted-open-transparent body r

  pending : ComputationsRelated W′
      (PendingTargetValueRelation slot result-related) (suc k)
      (liftImpreciseTerm step Vᴵ
        ⦂∀ liftImpreciseBody step Bᴵ [ ＇ Fin.zero ])
      (liftPreciseTerm step Vᴾ
        ⦂∀ liftPreciseBody step Bᴾ [ liftPreciseTy step Rᴾ ])
  pending = proj₁ (proj₁ (proj₂ (fam step []))) slot
    (liftPreciseTy step Rᴾ) (＇ Fin.zero)
    argument-related result-related

pending-target-universal-reduct : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty (suc Δᴵ)}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ} {k : ℕ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    (body : BodyImprecisionᵇ W Bᴾ Bᴵ)
    (r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ)
  → UniversalFamily W (bodyPᵇ body) Bᴾ Bᴵ (suc k) Vᴵ Vᴾ
  → let
      step = future-imprecise {Aᴵ = Rᴵ} (future-refl {W = W})
      W′ = impreciseBindWorld W Rᴵ
      resultᴵ = liftImpreciseBody step Bᴵ [ ＇ Fin.zero ]ᵗ
      opened = openRelatedBodyImprecision {W = W} (bodyPᵇ body) r
    in ComputationsRelated W′
          (FutureValueRelation (liftCenterImprecision step opened))
          (suc k)
          ((liftImpreciseTerm step Vᴵ
              ⦂∀ liftImpreciseBody step Bᴵ [ ＇ Fin.zero ])
            ↑ 〖 Fin.zero , ⇑ᵗ Rᴵ ↑ resultᴵ 〗)
          (liftPreciseTerm step Vᴾ
            ⦂∀ liftPreciseBody step Bᴾ [ liftPreciseTy step Rᴾ ])
pending-target-universal-reduct {W = W} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
    {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} body r fam =
  ClosureProof.computations-related-reindex pending normalized
    precise-eq imprecise-eq refl refl
    (pending-target-universal-head body r fam)
  where
  step = future-imprecise {Aᴵ = Rᴵ} (future-refl {W = W})
  W′ = impreciseBindWorld W Rᴵ
  slot = fresh-target-slot W Rᴵ
  resultᴵ = liftImpreciseBody step Bᴵ [ ＇ Fin.zero ]ᵗ
  opened = openRelatedBodyImprecision {W = W} (bodyPᵇ body) r

  related : TargetTransparent W′ slot
      (liftPreciseBody step Bᴾ [ liftPreciseTy step Rᴾ ]ᵗ)
      resultᴵ
  related = fresh-target-lifted-open-transparent body r

  pending : impEnv (core W′) I.⊢
      embedPrecise (core W′)
        (liftPreciseBody step Bᴾ [ liftPreciseTy step Rᴾ ]ᵗ)
      ⊑ embedImprecise (core W′)
          (replaceTy Fin.zero (⇑ᵗ Rᴵ) resultᴵ)
  pending = target-transparent-derivation slot
    {Aᴾ = liftPreciseBody step Bᴾ [ liftPreciseTy step Rᴾ ]ᵗ}
    {Aᴵ = resultᴵ} related

  normalized : impEnv (core W′) I.⊢
      liftCenterTy step
        (embedPrecise (core W) (Bᴾ [ Rᴾ ]ᵗ))
      ⊑ liftCenterTy step
          (embedImprecise (core W) (Bᴵ [ Rᴵ ]ᵗ))
  normalized = liftCenterImprecision step opened

  precise-eq : embedPrecise (core W′)
      (liftPreciseBody step Bᴾ [ liftPreciseTy step Rᴾ ]ᵗ)
      ≡ liftCenterTy step
          (embedPrecise (core W) (Bᴾ [ Rᴾ ]ᵗ))
  precise-eq = trans
    (cong (embedPrecise (core W′))
      (sym (lift-precise-open step Bᴾ Rᴾ)))
    (embedPrecise-lift step (Bᴾ [ Rᴾ ]ᵗ))

  imprecise-eq : embedImprecise (core W′)
      (replaceTy Fin.zero (⇑ᵗ Rᴵ) resultᴵ)
      ≡ liftCenterTy step
          (embedImprecise (core W) (Bᴵ [ Rᴵ ]ᵗ))
  imprecise-eq = trans
    (cong (embedImprecise (core W′))
      (cong (replaceTy Fin.zero (⇑ᵗ Rᴵ))
        (open-shifted-body Bᴵ)))
    (trans
      (cong (embedImprecise (core W′))
        (replace-zero-open Rᴵ Bᴵ))
      (embedImprecise-lift step (Bᴵ [ Rᴵ ]ᵗ)))

pending-target-universal-bind-expand : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty (suc Δᴵ)}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ} {k : ℕ}
    {Vᴵ Mᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    (body : BodyImprecisionᵇ W Bᴾ Bᴵ)
    (r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ)
  → UniversalFamily W (bodyPᵇ body) Bᴾ Bᴵ (suc k) Vᴵ Vᴾ
  → let
      step = future-imprecise {Aᴵ = Rᴵ} (future-refl {W = W})
      resultᴵ = liftImpreciseBody step Bᴵ [ ＇ Fin.zero ]ᵗ
      Nᴵ = (liftImpreciseTerm step Vᴵ
              ⦂∀ liftImpreciseBody step Bᴵ [ ＇ Fin.zero ])
            ↑ 〖 Fin.zero , ⇑ᵗ Rᴵ ↑ resultᴵ 〗
    in Mᴵ ≢ blame
      → E.value? Mᴵ ≡ Data.Maybe.nothing
      → (stepᴵ : Mᴵ —→[ bind Rᴵ ] Nᴵ)
      → E.step? (impreciseStore (core W)) Mᴵ ≡
          Data.Maybe.just (E.step-result (bind Rᴵ) Nᴵ stepᴵ)
      → ComputationsRelated W
          (FutureValueRelation
            (openRelatedBodyImprecision {W = W} (bodyPᵇ body) r))
          (suc k) Mᴵ (Vᴾ ⦂∀ Bᴾ [ Rᴾ ])
pending-target-universal-bind-expand {W = W} {Bᴾ = Bᴾ}
    {Bᴵ = Bᴵ} {Rᴾ = Rᴾ} {Rᴵ = Rᴵ}
    body r fam Mᴵ≢blame value-eqᴵ stepᴵ step-eqᴵ =
  post-bind-weaken step opened
    (related-imprecise-bind-step-expand Mᴵ≢blame value-eqᴵ
      stepᴵ step-eqᴵ
      (pending-target-universal-reduct body r fam))
  where
  step = future-imprecise {Aᴵ = Rᴵ} (future-refl {W = W})
  opened = openRelatedBodyImprecision {W = W} (bodyPᵇ body) r

------------------------------------------------------------------------
-- Exact imprecise-only wrapper peels
------------------------------------------------------------------------

pending-target-imprecise-peel-reduct : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ Bᴵ′ : Ty (suc Δᴵ)}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ} {k : ℕ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    (peel : ImprecisePeelᵇ W Bᴾ Bᴵ Bᴵ′)
    (r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ)
  → UniversalDataᵇ W (bodyPᵇ (imprecise-peel-targetᵇ peel))
      Bᴾ Bᴵ (suc k) Vᴵ Vᴾ
  → let
      step = future-imprecise {Aᴵ = Rᴵ} (future-refl {W = W})
      opened = openRelatedBodyImprecision {W = W}
        (bodyPᵇ (imprecise-peel-targetᵇ peel)) r
    in ComputationsRelated (impreciseBindWorld W Rᴵ)
        (FutureValueRelation (liftCenterImprecision step opened))
        (suc k)
        (imprecise-peel-reductᴵᵇ peel Rᴵ Vᴵ)
        (liftPreciseTerm step Vᴾ
          ⦂∀ liftPreciseBody step Bᴾ [ liftPreciseTy step Rᴾ ])
pending-target-imprecise-peel-reduct {W = W} {Rᴾ = Rᴾ}
    {Rᴵ = Rᴵ} peel r dat =
  proj₂ (proj₁ (data-pendingᵇ dat future-refl)) peel Rᴾ Rᴵ r

pending-target-imprecise-peel-bind-expand : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ Bᴵ′ : Ty (suc Δᴵ)}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ} {k : ℕ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    (peel : ImprecisePeelᵇ W Bᴾ Bᴵ Bᴵ′)
    (r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ)
  → UniversalDataᵇ W (bodyPᵇ (imprecise-peel-targetᵇ peel))
      Bᴾ Bᴵ (suc k) Vᴵ Vᴾ
  → Value Vᴵ
  → ComputationsRelated W
      (FutureValueRelation (openRelatedBodyImprecision {W = W}
        (bodyPᵇ (imprecise-peel-targetᵇ peel)) r))
      (suc k)
      (imprecise-peel-termᴵᵇ peel Vᴵ ⦂∀ Bᴵ′ [ Rᴵ ])
      (Vᴾ ⦂∀ Bᴾ [ Rᴾ ])
pending-target-imprecise-peel-bind-expand {W = W} {Rᴵ = Rᴵ}
    (reveal-imprecise-peelᵇ s C no-occur body avoid) r fam vVᴵ
    with reveal-type-app-step-question
      {Σ = impreciseStore (core W)} {A = Rᴵ}
      〖 Fin.suc (slotXᴵ s) , ⇑ᵗ (slotRᴵ s) ↑ C 〗 vVᴵ
pending-target-imprecise-peel-bind-expand {W = W} {Rᴵ = Rᴵ}
    peel@(reveal-imprecise-peelᵇ s C no-occur body avoid) r fam vVᴵ
    | vVᴵ′ , step-eq =
  post-bind-weaken step opened
    (related-imprecise-bind-step-expand (λ ()) refl
      (β-reveal-∀ vVᴵ′) step-eq
      (pending-target-imprecise-peel-reduct peel r fam))
  where
  step = future-imprecise {Aᴵ = Rᴵ} (future-refl {W = W})
  opened = openRelatedBodyImprecision {W = W} (bodyPᵇ body) r
pending-target-imprecise-peel-bind-expand {W = W} {Rᴵ = Rᴵ}
    (conceal-imprecise-peelᵇ s C no-occur body avoid) r fam vVᴵ
    with conceal-type-app-step-question
      {Σ = impreciseStore (core W)} {A = Rᴵ}
      (makeConceal (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) C) vVᴵ
pending-target-imprecise-peel-bind-expand {W = W} {Rᴵ = Rᴵ}
    peel@(conceal-imprecise-peelᵇ s C no-occur body avoid) r fam vVᴵ
    | vVᴵ′ , step-eq =
  post-bind-weaken step opened
    (related-imprecise-bind-step-expand (λ ()) refl
      (β-conceal-∀ vVᴵ′) step-eq
      (pending-target-imprecise-peel-reduct peel r fam))
  where
  step = future-imprecise {Aᴵ = Rᴵ} (future-refl {W = W})
  opened = openRelatedBodyImprecision {W = W} (bodyPᵇ body) r
