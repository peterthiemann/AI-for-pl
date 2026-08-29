module proof.LR-narrow.UniversalFamilyData where

-- File Charter:
--   * Proves structural operations on two-sided universal producer data.
--   * Supplies future-world closure for the ordinary and pending chains.
--   * Depends on the general LR closure lemmas, but not on reveal obligations.

open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (trans)

open import Types
open import CastTerms
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.LogicalRelation
open import LR-narrow.UniversalFamily
import proof.LR-narrow.Closure as Closure

universal-dataᵇ-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Aᴾ Aᴵ : Ty (suc Δᶜ)}
    {p : I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty (suc Δᴵ)} {k : ℕ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    (W≼W′ : Future W W′)
  → UniversalDataᵇ W p Bᴾ Bᴵ k Vᴵ Vᴾ
  → UniversalDataᵇ W′ (liftCenterBodyImprecision W≼W′ p)
      (liftPreciseBody W≼W′ Bᴾ) (liftImpreciseBody W≼W′ Bᴵ) k
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
universal-dataᵇ-future {W′ = W′} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} {p = p}
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    W≼W′ dat = universal-dataᵇ
  structural-endpoints
  (Closure.universals-related-future W≼W′ (data-chainᵇ dat))
  pending
  where
  lifted-endpoints =
    Closure.typed-endpoints-future W≼W′ (data-endpointsᵇ dat)

  structural-endpoints = typed-endpoints
    (impreciseType lifted-endpoints) (preciseType lifted-endpoints)
    (trans (impreciseEmbedded lifted-endpoints)
      (liftCenterTy-universal W≼W′ Aᴵ))
    (trans (preciseEmbedded lifted-endpoints)
      (liftCenterTy-universal W≼W′ Aᴾ))
    (imprecise-value lifted-endpoints) (precise-value lifted-endpoints)
    (imprecise-typed lifted-endpoints) (precise-typed lifted-endpoints)

  pending : ∀ {Δᴾ″ Δᴵ″ Δᶜ″} {K : World Δᴾ″ Δᴵ″ Δᶜ″}
      (W′≼K : Future W′ K)
    → PendingTargetUniversalsRelated K
        (liftPreciseBody W′≼K (liftPreciseBody W≼W′ Bᴾ))
        (liftImpreciseBody W′≼K (liftImpreciseBody W≼W′ Bᴵ)) k
        (liftImpreciseTerm W′≼K (liftImpreciseTerm W≼W′ Vᴵ))
        (liftPreciseTerm W′≼K (liftPreciseTerm W≼W′ Vᴾ))
  pending W′≼K =
    Closure.pending-target-universals-related-transport
      (liftImpreciseTerm-trans W≼W′ W′≼K Vᴵ)
      (liftPreciseTerm-trans W≼W′ W′≼K Vᴾ)
      (Closure.pending-target-universals-related-body-transport
        (liftPreciseBody-trans W≼W′ W′≼K Bᴾ)
        (liftImpreciseBody-trans W≼W′ W′≼K Bᴵ)
        (data-pendingᵇ dat (future-trans W≼W′ W′≼K)))
