module proof.LR-narrow.PendingUniversal where

-- File Charter:
--   * Eliminates the exact pending application of an imprecise-only peel.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types
open import CastTerms
open import LR-narrow.World
open import LR-narrow.SlotSequence
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import proof.LR-narrow.StepExpansion using
  (nonvalue-computations-one)
open import proof.LR-narrow.UniversalReveal using (post-bind-weaken)

pending-target-imprecise-peel-one : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ Bᴵ′ : Ty (suc Δᴵ)}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    (peel : ImprecisePeelᵇ W Bᴾ Bᴵ Bᴵ′)
    (r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ)
  → ComputationsRelated W
      (PostBindValueRelation
        (future-paired (future-refl {W = W}) r)
        (openRelatedBodyImprecision {W = W}
          (bodyPᵇ (imprecise-peel-targetᵇ peel)) r))
      (suc zero)
      (imprecise-peel-termᴵᵇ peel Vᴵ ⦂∀ Bᴵ′ [ Rᴵ ])
      (Vᴾ ⦂∀ Bᴾ [ Rᴾ ])
pending-target-imprecise-peel-one peel r =
  nonvalue-computations-one (λ ()) (λ ()) refl refl

pending-target-imprecise-peel : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ Bᴵ′ : Ty (suc Δᴵ)}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ} {k : ℕ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    (peel : ImprecisePeelᵇ W Bᴾ Bᴵ Bᴵ′)
    (r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ)
  → PendingTargetUniversalsRelated W Bᴾ Bᴵ (suc k) Vᴵ Vᴾ
  → ComputationsRelated W
      (FutureValueRelation (openRelatedBodyImprecision {W = W}
        (bodyPᵇ (imprecise-peel-targetᵇ peel)) r))
      (suc k)
      (imprecise-peel-termᴵᵇ peel Vᴵ ⦂∀ Bᴵ′ [ Rᴵ ])
      (Vᴾ ⦂∀ Bᴾ [ Rᴾ ])
pending-target-imprecise-peel {W = W} {Rᴾ = Rᴾ}
    {Rᴵ = Rᴵ} peel r pending =
  post-bind-weaken (future-paired (future-refl {W = W}) r)
    (openRelatedBodyImprecision {W = W}
      (bodyPᵇ (imprecise-peel-targetᵇ peel)) r)
    (proj₁ pending peel Rᴾ Rᴵ r)

pending-target-imprecise-peel-factored : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ Bᴵ′ : Ty (suc Δᴵ)}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ} {k : ℕ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    (peel : ImprecisePeelᵇ W Bᴾ Bᴵ Bᴵ′)
    (r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ)
  → PendingTargetUniversalsRelated W Bᴾ Bᴵ (suc k) Vᴵ Vᴾ
  → ComputationsRelated W
      (PostBindValueRelation
        (future-paired (future-refl {W = W}) r)
        (openRelatedBodyImprecision {W = W}
          (bodyPᵇ (imprecise-peel-targetᵇ peel)) r))
      (suc k)
      (imprecise-peel-termᴵᵇ peel Vᴵ ⦂∀ Bᴵ′ [ Rᴵ ])
      (Vᴾ ⦂∀ Bᴾ [ Rᴾ ])
pending-target-imprecise-peel-factored peel r pending =
  proj₁ pending peel _ _ r
