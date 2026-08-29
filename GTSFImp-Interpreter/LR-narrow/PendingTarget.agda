module LR-narrow.PendingTarget where

-- File Charter:
--   * Defines the scoped target-transparent reading used while a target-only
--     runtime bind is pending its precise-side counterpart.
--   * Normalizes the distinguished target name to its stored representative
--     before applying ordinary type imprecision.
--   * Does not alter the live imprecision relation or its uniqueness laws.

open import Types
open import Conversion using (replaceTy)
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.SlotSequence

targetNormalize : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
  → TargetSlot W → Ty Δᶜ → Ty Δᶜ
targetNormalize W t B = replaceTy (tcenter t)
  (embedImprecise (core W) (tslotRᴵ t)) B

TargetTransparentCenter : ∀ {Δᴾ Δᴵ Δᶜ}
  → (W : World Δᴾ Δᴵ Δᶜ)
  → TargetSlot W → Ty Δᶜ → Ty Δᶜ → Set
TargetTransparentCenter W t A B =
  impEnv (core W) I.⊢ A ⊑ targetNormalize W t B

TargetTransparent : ∀ {Δᴾ Δᴵ Δᶜ}
  → (W : World Δᴾ Δᴵ Δᶜ)
  → TargetSlot W → Ty Δᴾ → Ty Δᴵ → Set
TargetTransparent W t Aᴾ Aᴵ = TargetTransparentCenter W t
  (embedPrecise (core W) Aᴾ) (embedImprecise (core W) Aᴵ)
