module proof.LR-narrow.ScopedRightSealCompatibility where

-- File Charter:
--   * Seals and unseals only the precise computation at a right nominal slot.
--   * Keeps the imprecise program and observation index unchanged, including
--     when either operand allocates and returned values retain private names.
--   * Uses right-frame composition and same-index target-step expansion;
--     no imprecise slot or new compatibility assumption is required.

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; cong; trans) renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import Reduction
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedRightNominal
open import proof.LR-narrow.FramePhases using (Frame)
open import proof.LR-narrow.RevealFrames
  using (revealFrame; concealFrame; reveal-frm; conceal-frm)
open import proof.LR-narrow.ScopedConversionTransport
  using (reveal-frame-transport; conceal-frame-transport;
    scope↑-unseal; scope↓-seal)
open import proof.LR-narrow.ScopedStepExpansion using (observed-right-step)
open import proof.LR-narrow.RevealSteps
  using (unseal-step-question; unseal-value-none)
import proof.LR-narrow.ScopedConversionCompatibility as CC
import proof.LR-narrow.ScopedRightFrameComposition as RF

module Compatibility {Δᴵ₀ Δᴾ₀} (Σᴵ₀ : TyStore Δᴵ₀)
    (Σᴾ₀ : TyStore Δᴾ₀) where

  open Model Σᴵ₀ Σᴾ₀
  open Nominals Σᴵ₀ Σᴾ₀
  open CC.Compatibility Σᴵ₀ Σᴾ₀ using (values-observed)

  private
    module Reveal = RF.Composition revealFrame Σᴵ₀ Σᴾ₀
    module Conceal = RF.Composition concealFrame Σᴵ₀ Σᴾ₀

  private
    right-seal-values : ∀ {Δᴵ Δᴾ} (A : ScopedType) Y
        (entryY : Σᴾ₀ ∋ Y ⦂ preciseTy A)
        {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {k U V}
      → related A S T k U V
      → ObservedComputations (right-nominal A Y entryY) S T k U
          (V ↓ seal (scopeVar T Y) (scopeTy T (preciseTy A)))
    right-seal-values A Y entryY r =
      values-observed (right-nominal A Y entryY)
        (related-right-seal (precise-value A r) r)

    right-unseal-values : ∀ {Δᴵ Δᴾ} (A : ScopedType) Y
        (entryY : Σᴾ₀ ∋ Y ⦂ preciseTy A)
        {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {k U V}
      → related (right-nominal A Y entryY) S T k U V
      → ObservedComputations A S T k U
          (V ↑ unseal (scopeVar T Y) (scopeTy T (preciseTy A)))
    right-unseal-values A Y entryY {T = T} (related-right-seal vV r)
        with unseal-step-question {Σ = scopeStore T}
          (scopeVar T Y) (scopeTy T (preciseTy A)) vV
    right-unseal-values A Y entryY {T = T} (related-right-seal vV r)
        | vV′ , step =
      observed-right-step (λ ())
        (unseal-value-none (scopeVar T Y) (scopeTy T (preciseTy A)) vV′)
        (pure-step (conceal-reveal vV′)) step (values-observed A r)

  observed-right-seal : ∀ {Δᴵ Δᴾ} (A : ScopedType) Y
      (entryY : Σᴾ₀ ∋ Y ⦂ preciseTy A)
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {k M N}
    → ObservedComputations A S T k M N
    → ObservedComputations (right-nominal A Y entryY) S T k M
        (N ↓ seal (scopeVar T Y) (scopeTy T (preciseTy A)))
  observed-right-seal A Y entryY {S = S} {T = T} =
    Conceal.right-frame-observed
      (conceal-frm (seal (scopeVar T Y) (scopeTy T (preciseTy A))))
      (λ χsᴵ χsᴾ {j} {U} {V} j≤k r →
        subst≡ (λ N → ObservedComputations (right-nominal A Y entryY)
          (advance S χsᴵ) (advance T χsᴾ) j U N)
          (sym (cong (λ f → Frame.plug concealFrame f V)
            (trans
              (cong (Frame.transports concealFrame χsᴾ)
                (sym (scope↓-seal T Y (preciseTy A))))
              (trans (conceal-frame-transport T χsᴾ (seal Y (preciseTy A)))
                (scope↓-seal (advance T χsᴾ) Y (preciseTy A))))))
          (right-seal-values A Y entryY r))

  observed-right-unseal : ∀ {Δᴵ Δᴾ} (A : ScopedType) Y
      (entryY : Σᴾ₀ ∋ Y ⦂ preciseTy A)
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {k M N}
    → ObservedComputations (right-nominal A Y entryY) S T k M N
    → ObservedComputations A S T k M
        (N ↑ unseal (scopeVar T Y) (scopeTy T (preciseTy A)))
  observed-right-unseal A Y entryY {S = S} {T = T} =
    Reveal.right-frame-observed
      (reveal-frm (unseal (scopeVar T Y) (scopeTy T (preciseTy A))))
      (λ χsᴵ χsᴾ {j} {U} {V} j≤k r →
        subst≡ (λ N → ObservedComputations A
          (advance S χsᴵ) (advance T χsᴾ) j U N)
          (sym (cong (λ f → Frame.plug revealFrame f V)
            (trans
              (cong (Frame.transports revealFrame χsᴾ)
                (sym (scope↑-unseal T Y (preciseTy A))))
              (trans (reveal-frame-transport T χsᴾ (unseal Y (preciseTy A)))
                (scope↑-unseal (advance T χsᴾ) Y (preciseTy A))))))
          (right-unseal-values A Y entryY r))
