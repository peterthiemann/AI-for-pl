module proof.LR-narrow.ScopedRightBodyCompatibility where

-- File Charter:
--   * Proves precise-only reveal/conceal compatibility for BodyFragment.
--   * The imprecise computation is literally unchanged; only its endpoint
--     typing is transported between the equal imprecise body types.
--   * Arrows convert the precise argument contravariantly, call the original
--     function, and convert its result. Only precise beta steps are expanded.
--   * Preserves the outer index and all three observation clauses with actual
--     independent allocation histories; fresh allocation is a separate step.

open import Data.List using ([])
open import Data.Nat using (_<_)
open import Relation.Binary.PropositionalEquality
  using (sym; cong; trans) renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedBodyInterpretation
  using (BodyFragment; natural-body; variable-body; arrow-body)
open import proof.LR-narrow.ScopedConversionTransport
open import proof.LR-narrow.FramePhases using (Frame)
open import proof.LR-narrow.RevealFrames
  using (revealFrame; concealFrame; reveal-frm; conceal-frm)
open import proof.LR-narrow.ScopedRightNominal
import proof.LR-narrow.ScopedRightFrameComposition as FC
import proof.LR-narrow.ScopedApplication as App
import proof.LR-narrow.ScopedConversionCompatibility as CC
import proof.LR-narrow.ScopedRightSealCompatibility as RS
import proof.LR-narrow.ScopedBodyInterpretation as BI
import proof.LR-narrow.ScopedRightBodyConversion as BC

module Compatibility {Δᴵ₀ Δᴾ₀} (Σᴵ₀ : TyStore Δᴵ₀)
    (Σᴾ₀ : TyStore Δᴾ₀) where

  open Model Σᴵ₀ Σᴾ₀
  open Nominals Σᴵ₀ Σᴾ₀
  open BC.Conversions Σᴵ₀ Σᴾ₀
  open CC.Compatibility Σᴵ₀ Σᴾ₀
  open App.Applications Σᴵ₀ Σᴾ₀
  open RS.Compatibility Σᴵ₀ Σᴾ₀
  private
    module I = BI.Interpretation Σᴵ₀ Σᴾ₀
    module R = FC.Composition revealFrame Σᴵ₀ Σᴾ₀
    module D = FC.Composition concealFrame Σᴵ₀ Σᴾ₀
  open I using (interpret-body)

  mutual

    right-reveal-observed : ∀ {n C Δᴵ Δᴾ} (p : BodyFragment C)
        (η : TyVar n → RightVariableConversion)
        {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {k M N}
      → ObservedComputations (interpret-body p (λ X → abstract-type (η X)))
          S T k M N
      → ObservedComputations (interpret-body p (λ X → public-type (η X)))
          S T k M (N ↑ scope↑ T (revealᴾ p η))
    right-reveal-observed p η {S} {T} = R.right-frame-observed
      (reveal-frm (scope↑ T (revealᴾ p η)))
      (λ χsᴵ χsᴾ {j} {U} {V} j≤k r →
        subst≡ (λ N → ObservedComputations
            (interpret-body p (λ X → public-type (η X)))
            (advance S χsᴵ) (advance T χsᴾ) j U N)
          (sym (cong (λ f → Frame.plug revealFrame f V)
            (reveal-frame-transport T χsᴾ (revealᴾ p η))))
          (right-reveal-values p η r))

    right-conceal-observed : ∀ {n C Δᴵ Δᴾ} (p : BodyFragment C)
        (η : TyVar n → RightVariableConversion)
        {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {k M N}
      → ObservedComputations (interpret-body p (λ X → public-type (η X)))
          S T k M N
      → ObservedComputations (interpret-body p (λ X → abstract-type (η X)))
          S T k M (N ↓ scope↓ T (concealᴾ p η))
    right-conceal-observed p η {S} {T} = D.right-frame-observed
      (conceal-frm (scope↓ T (concealᴾ p η)))
      (λ χsᴵ χsᴾ {j} {U} {V} j≤k r →
        subst≡ (λ N → ObservedComputations
            (interpret-body p (λ X → abstract-type (η X)))
            (advance S χsᴵ) (advance T χsᴾ) j U N)
          (sym (cong (λ f → Frame.plug concealFrame f V)
            (conceal-frame-transport T χsᴾ (concealᴾ p η))))
          (right-conceal-values p η r))

    private

      right-reveal-values : ∀ {n C Δᴵ Δᴾ} (p : BodyFragment C)
          (η : TyVar n → RightVariableConversion)
          {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {k U V}
        → related (interpret-body p (λ X → abstract-type (η X))) S T k U V
        → ObservedComputations (interpret-body p (λ X → public-type (η X)))
            S T k U (V ↑ scope↑ T (revealᴾ p η))
      right-reveal-values natural-body η {S} {T} {k} {U} {V} r =
        subst≡ (ObservedComputations natural S T k U)
          (sym (cong (λ f → Frame.plug revealFrame f V)
            (scope↑-id T (‵ `ℕ))))
          (right-identity-reveals natural r)
      right-reveal-values (variable-body {X}) η r with η X
      right-reveal-values variable-body η {S} {T} {k} {U} {V} r
          | unchanged A =
        subst≡ (ObservedComputations A S T k U)
          (sym (cong (λ f → Frame.plug revealFrame f V)
            (scope↑-id T (preciseTy A)))) (right-identity-reveals A r)
      right-reveal-values variable-body η {S} {T} {k} {U} {V} r
          | right-slot A Y entryY =
        subst≡ (ObservedComputations A S T k U)
          (sym (cong (λ f → Frame.plug revealFrame f V)
            (scope↑-unseal T Y (preciseTy A))))
          (observed-right-unseal A Y entryY
            (values-observed (right-nominal A Y entryY) r))
      right-reveal-values (arrow-body p q) η {S} {T} {k} {F} {G} r =
        values-observed (interpret-body (arrow-body p q)
          (λ X → public-type (η X)))
          (arrow-values (ArrowValues.functionᴵ-value r)
            (subst≡ Value
              (sym (cong (λ f → Frame.plug revealFrame f G)
                (scope↑-arrow T (concealᴾ p η) (revealᴾ q η))))
              (ArrowValues.functionᴾ-value r ↑ fun))
            (subst≡ (λ A → ⟨ _ , scopeStore S , [] ⟩ ⊢ F ⦂ A)
              (cong (scopeTy S) (imprecise-body (arrow-body p q) η))
              (ArrowValues.functionᴵ-typed r))
            (⊢reveal (scope↑-valid T (revealᴾ-typed (arrow-body p q) η))
              (ArrowValues.functionᴾ-typed r)) call)
        where
        call : ∀ {Δᴵ′ Δᴾ′} {S′ : PhysicalScope Σᴵ₀ Δᴵ′}
            {T′ : PhysicalScope Σᴾ₀ Δᴾ′} {j U V}
          → (s : ScopeFuture S S′) → (t : ScopeFuture T T′)
          → j < k → related (interpret-body p (λ X → public-type (η X)))
              S′ T′ j U V
          → ObservedComputations
              (interpret-body q (λ X → public-type (η X))) S′ T′ j
              (liftTerm s F · U)
              (liftTerm t (G ↑ scope↑ T (revealᴾ (arrow-body p q) η)) · V)
        call {S′ = S′} {T′} {j} {U} {V} s t j<k args =
          subst≡ (ObservedComputations
              (interpret-body q (λ X → public-type (η X))) S′ T′ j
              (liftTerm s F · U))
            (sym (cong (_· V)
              (trans (lift-reveal t G (revealᴾ (arrow-body p q) η))
                (cong (λ f → Frame.plug revealFrame f (liftTerm t G))
                  (scope↑-arrow T′ (concealᴾ p η) (revealᴾ q η))))))
            (right-reveal-applications
              (scope↓ T′ (concealᴾ p η)) (scope↑ T′ (revealᴾ q η))
              (lift-value t (ArrowValues.functionᴾ-value r))
              (precise-value
                (interpret-body p (λ X → public-type (η X))) args)
              (right-reveal-observed q η
                (application-observed
                  (interpret-body p (λ X → abstract-type (η X)))
                  (interpret-body q (λ X → abstract-type (η X))) j<k
                  (future-closed (interpret-body (arrow-body p q)
                    (λ X → abstract-type (η X))) s t r)
                  (right-conceal-values p η args))))

      right-conceal-values : ∀ {n C Δᴵ Δᴾ} (p : BodyFragment C)
          (η : TyVar n → RightVariableConversion)
          {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {k U V}
        → related (interpret-body p (λ X → public-type (η X))) S T k U V
        → ObservedComputations
            (interpret-body p (λ X → abstract-type (η X)))
            S T k U (V ↓ scope↓ T (concealᴾ p η))
      right-conceal-values natural-body η {S} {T} {k} {U} {V} r =
        subst≡ (ObservedComputations natural S T k U)
          (sym (cong (λ f → Frame.plug concealFrame f V)
            (scope↓-id T (‵ `ℕ))))
          (right-identity-conceals natural r)
      right-conceal-values (variable-body {X}) η r with η X
      right-conceal-values variable-body η {S} {T} {k} {U} {V} r
          | unchanged A =
        subst≡ (ObservedComputations A S T k U)
          (sym (cong (λ f → Frame.plug concealFrame f V)
            (scope↓-id T (preciseTy A)))) (right-identity-conceals A r)
      right-conceal-values variable-body η {S} {T} {k} {U} {V} r
          | right-slot A Y entryY =
        subst≡ (ObservedComputations (right-nominal A Y entryY) S T k U)
          (sym (cong (λ f → Frame.plug concealFrame f V)
            (scope↓-seal T Y (preciseTy A))))
          (observed-right-seal A Y entryY (values-observed A r))
      right-conceal-values (arrow-body p q) η {S} {T} {k} {F} {G} r =
        values-observed (interpret-body (arrow-body p q)
          (λ X → abstract-type (η X)))
          (arrow-values (ArrowValues.functionᴵ-value r)
            (subst≡ Value
              (sym (cong (λ f → Frame.plug concealFrame f G)
                (scope↓-arrow T (revealᴾ p η) (concealᴾ q η))))
              (ArrowValues.functionᴾ-value r ↓ fun))
            (subst≡ (λ A → ⟨ _ , scopeStore S , [] ⟩ ⊢ F ⦂ A)
              (sym (cong (scopeTy S) (imprecise-body (arrow-body p q) η)))
              (ArrowValues.functionᴵ-typed r))
            (⊢conceal (scope↓-valid T (concealᴾ-typed (arrow-body p q) η))
              (ArrowValues.functionᴾ-typed r)) call)
        where
        call : ∀ {Δᴵ′ Δᴾ′} {S′ : PhysicalScope Σᴵ₀ Δᴵ′}
            {T′ : PhysicalScope Σᴾ₀ Δᴾ′} {j U V}
          → (s : ScopeFuture S S′) → (t : ScopeFuture T T′)
          → j < k → related (interpret-body p (λ X → abstract-type (η X)))
              S′ T′ j U V
          → ObservedComputations
              (interpret-body q (λ X → abstract-type (η X))) S′ T′ j
              (liftTerm s F · U)
              (liftTerm t (G ↓ scope↓ T (concealᴾ (arrow-body p q) η)) · V)
        call {S′ = S′} {T′} {j} {U} {V} s t j<k args =
          subst≡ (ObservedComputations
              (interpret-body q (λ X → abstract-type (η X))) S′ T′ j
              (liftTerm s F · U))
            (sym (cong (_· V)
              (trans (lift-conceal t G (concealᴾ (arrow-body p q) η))
                (cong (λ f → Frame.plug concealFrame f (liftTerm t G))
                  (scope↓-arrow T′ (revealᴾ p η) (concealᴾ q η))))))
            (right-conceal-applications
              (scope↑ T′ (revealᴾ p η)) (scope↓ T′ (concealᴾ q η))
              (lift-value t (ArrowValues.functionᴾ-value r))
              (precise-value
                (interpret-body p (λ X → abstract-type (η X))) args)
              (right-conceal-observed q η
                (application-observed
                  (interpret-body p (λ X → public-type (η X)))
                  (interpret-body q (λ X → public-type (η X))) j<k
                  (future-closed (interpret-body (arrow-body p q)
                    (λ X → public-type (η X))) s t r)
                  (right-reveal-values p η args))))
