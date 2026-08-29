module proof.LR-narrow.PendingUniversal where

-- File Charter:
--   * Eliminates a stored pending-target universal head at a fresh target bind.
--   * Applies the fresh target reveal to recover ordinary value imprecision.
--   * Supplies the semantic core of an imprecise-only universal peel.

open import Data.Nat using (ℕ; suc)
open import Data.Product using (proj₁; proj₂)
import Data.Fin as Fin

open import Types
open import CastTerms
open import Conversion using (〖_,_↑_〗)
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.SlotSequence
open import LR-narrow.PendingTarget using (TargetTransparent)
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import proof.LR-narrow.PendingTarget
open import proof.LR-narrow.PendingTargetFrame

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
  pending = proj₁ (proj₂ (fam step [])) slot
    (liftPreciseTy step Rᴾ) (＇ Fin.zero)
    argument-related result-related
