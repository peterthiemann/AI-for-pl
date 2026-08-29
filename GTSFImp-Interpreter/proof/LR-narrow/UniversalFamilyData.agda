module proof.LR-narrow.UniversalFamilyData where

-- File Charter:
--   * Proves structural operations on two-sided universal producer data.
--   * Supplies future-world closure for the ordinary and pending chains.
--   * Depends on the general LR closure lemmas, but not on reveal obligations.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Unit.Polymorphic.Base using (tt)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (refl; trans)

open import Types
open import CastTerms
open import Conversion using (replaceTy; 〖_,_↑_〗; makeConceal)
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.SlotSequence
open import LR-narrow.LogicalRelation
open import LR-narrow.UniversalFamily
import proof.LR-narrow.Closure as Closure
open import proof.LR-narrow.AliasAvoid using (AliasAvoidᵖ)
open import proof.LR-narrow.RevealStatements using (OuterBelow)
open import proof.LR-narrow.RevealStructural using
  (statements-all; reveal-universal-head; conceal-universal-head)

------------------------------------------------------------------------
-- Completed structural induction below any step index
------------------------------------------------------------------------

outer-below-all : ∀ (k : ℕ) → OuterBelow k
outer-below-all k j j<k n = statements-all j n

------------------------------------------------------------------------
-- Paired wrapper chain extensions
------------------------------------------------------------------------

reveal-paired-chainᵇ : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty (suc Δᴵ)}
    (source : BodyImprecisionᵇ W Bᴾ Bᴵ)
  → AliasAvoidᵖ (Fin.suc (center s)) (bodyPᵇ source)
  → (target : BodyImprecisionᵇ W
      (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) Bᴾ)
      (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) Bᴵ))
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → UniversalDataᵇ W (bodyPᵇ source) Bᴾ Bᴵ k Vᴵ Vᴾ
  → UniversalsRelated W (bodyPᵇ target)
      (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) Bᴾ)
      (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) Bᴵ) k
      (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ `∀ Bᴵ 〗)
      (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ Bᴾ 〗)
reveal-paired-chainᵇ W s source avoid target {k = zero} dat = tt
reveal-paired-chainᵇ W s source avoid target {k = suc k} dat =
  reveal-universal-head W s (bodyPᵇ source) avoid refl refl
    (outer-below-all (suc k)) dat ,
  reveal-paired-chainᵇ W s source avoid target
    (universal-dataᵇ-downward dat)

conceal-paired-chainᵇ : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty (suc Δᴵ)}
    (target : BodyImprecisionᵇ W Bᴾ Bᴵ)
    (source : BodyImprecisionᵇ W
      (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) Bᴾ)
      (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) Bᴵ))
  → AliasAvoidᵖ (Fin.suc (center s)) (bodyPᵇ target)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → UniversalDataᵇ W (bodyPᵇ source)
      (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) Bᴾ)
      (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) Bᴵ)
      k Vᴵ Vᴾ
  → UniversalsRelated W (bodyPᵇ target) Bᴾ Bᴵ k
      (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (`∀ Bᴵ))
      (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ Bᴾ))
conceal-paired-chainᵇ W s target source avoid {k = zero} dat = tt
conceal-paired-chainᵇ W s target source avoid {k = suc k} dat =
  conceal-universal-head W s (bodyPᵇ target) (bodyPᵇ source) avoid
    refl refl refl refl (outer-below-all (suc k)) dat ,
  conceal-paired-chainᵇ W s target source avoid
    (universal-dataᵇ-downward dat)

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
