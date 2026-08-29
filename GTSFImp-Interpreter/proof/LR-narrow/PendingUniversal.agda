module proof.LR-narrow.PendingUniversal where

-- File Charter:
--   * Eliminates the exact pending application of an imprecise-only peel.

open import Data.Nat using (ℕ; suc)
open import Data.Product using (proj₁)

open import Types
open import CastTerms
open import LR-narrow.World
open import LR-narrow.SlotSequence
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation

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
  proj₁ pending peel Rᴾ Rᴵ r
