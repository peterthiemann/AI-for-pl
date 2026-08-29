module proof.LR-narrow.PendingUniversal where

-- File Charter:
--   * Eliminates the exact pending head of an imprecise-only universal peel.
--   * Expands the peel's target-only allocation back to its source redex.

open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_; proj₁)
import Data.Maybe
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (refl)

open import Types
open import CastTerms
open import Conversion using (〖_,_↑_〗; makeConceal)
open import Reduction
import Eval as E
open import LR-narrow.World
open import LR-narrow.SlotSequence
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import proof.LR-narrow.BindStepExpansion using
  (related-imprecise-bind-step-expand)
open import proof.LR-narrow.UniversalReveal using
  (post-bind-weaken; reveal-type-app-step-question;
   conceal-type-app-step-question)

pending-target-imprecise-peel-reduct : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ Bᴵ′ : Ty (suc Δᴵ)}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ} {k : ℕ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    (peel : ImprecisePeelᵇ W Bᴾ Bᴵ Bᴵ′)
    (r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ)
  → PendingTargetUniversalsRelated W Bᴾ Bᴵ (suc k) Vᴵ Vᴾ
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
    {Rᴵ = Rᴵ} peel r pending =
  proj₁ pending peel Rᴾ Rᴵ r

pending-target-imprecise-peel-bind-expand : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ Bᴵ′ : Ty (suc Δᴵ)}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ} {k : ℕ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    (peel : ImprecisePeelᵇ W Bᴾ Bᴵ Bᴵ′)
    (r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ)
  → PendingTargetUniversalsRelated W Bᴾ Bᴵ (suc k) Vᴵ Vᴾ
  → Value Vᴵ
  → ComputationsRelated W
      (FutureValueRelation (openRelatedBodyImprecision {W = W}
        (bodyPᵇ (imprecise-peel-targetᵇ peel)) r))
      (suc k)
      (imprecise-peel-termᴵᵇ peel Vᴵ ⦂∀ Bᴵ′ [ Rᴵ ])
      (Vᴾ ⦂∀ Bᴾ [ Rᴾ ])
pending-target-imprecise-peel-bind-expand {W = W} {Rᴵ = Rᴵ}
    (reveal-imprecise-peelᵇ s C no-occur body avoid) r pending vVᴵ
    with reveal-type-app-step-question
      {Σ = impreciseStore (core W)} {A = Rᴵ}
      〖 Fin.suc (slotXᴵ s) , ⇑ᵗ (slotRᴵ s) ↑ C 〗 vVᴵ
pending-target-imprecise-peel-bind-expand {W = W} {Rᴵ = Rᴵ}
    peel@(reveal-imprecise-peelᵇ s C no-occur body avoid) r pending vVᴵ
    | vVᴵ′ , step-eq =
  post-bind-weaken step opened
    (related-imprecise-bind-step-expand (λ ()) refl
      (β-reveal-∀ vVᴵ′) step-eq
      (pending-target-imprecise-peel-reduct peel r pending))
  where
  step = future-imprecise {Aᴵ = Rᴵ} (future-refl {W = W})
  opened = openRelatedBodyImprecision {W = W} (bodyPᵇ body) r
pending-target-imprecise-peel-bind-expand {W = W} {Rᴵ = Rᴵ}
    (conceal-imprecise-peelᵇ s C no-occur body avoid) r pending vVᴵ
    with conceal-type-app-step-question
      {Σ = impreciseStore (core W)} {A = Rᴵ}
      (makeConceal (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) C) vVᴵ
pending-target-imprecise-peel-bind-expand {W = W} {Rᴵ = Rᴵ}
    peel@(conceal-imprecise-peelᵇ s C no-occur body avoid) r pending vVᴵ
    | vVᴵ′ , step-eq =
  post-bind-weaken step opened
    (related-imprecise-bind-step-expand (λ ()) refl
      (β-conceal-∀ vVᴵ′) step-eq
      (pending-target-imprecise-peel-reduct peel r pending))
  where
  step = future-imprecise {Aᴵ = Rᴵ} (future-refl {W = W})
  opened = openRelatedBodyImprecision {W = W} (bodyPᵇ body) r
