module proof.LR-narrow.ScopedBodyCompatibility where

-- File Charter:
--   * Proves structural reveal and conceal compatibility for BodyFragment.
--   * Variable conversions carry syntax and store evidence, not assumed
--     semantic compatibility. Arrows use the opposite direction on domains.
--   * All observations keep their index and their actual allocation histories.
--   * This theorem concerns the compiled conversions, not universal wrappers.

open import Data.List using ([])
open import Data.Nat using (_<_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; cong; trans) renaming (subst to subst≡; subst₂ to subst₂≡)

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
open import proof.LR-narrow.FunctionSealCompatibility using (related-seals)
import proof.LR-narrow.ScopedFrameComposition as FC
import proof.LR-narrow.ScopedApplication as App
import proof.LR-narrow.ScopedFunctionSeal as FS
import proof.LR-narrow.ScopedConversionCompatibility as CC
import proof.LR-narrow.ScopedBodyInterpretation as BI
import proof.LR-narrow.ScopedBodyConversion as BC

module Compatibility {Δᴵ₀ Δᴾ₀} (Σᴵ₀ : TyStore Δᴵ₀)
    (Σᴾ₀ : TyStore Δᴾ₀) where

  open Model Σᴵ₀ Σᴾ₀
  module I = BI.Interpretation Σᴵ₀ Σᴾ₀
  open I using (interpret-body)
  open BC.Conversions Σᴵ₀ Σᴾ₀
  open CC.Compatibility Σᴵ₀ Σᴾ₀
  open App.Applications Σᴵ₀ Σᴾ₀
  open FS.Compatibility Σᴵ₀ Σᴾ₀ using (observed-unseals)
  module R = FC.Composition revealFrame revealFrame Σᴵ₀ Σᴾ₀
  module D = FC.Composition concealFrame concealFrame Σᴵ₀ Σᴾ₀

  mutual

    reveal-observed : ∀ {n C Δᴵ Δᴾ} (p : BodyFragment C)
        (η : TyVar n → VariableConversion)
        {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {k M N}
      → ObservedComputations (interpret-body p (λ X → abstract-type (η X)))
          S T k M N
      → ObservedComputations (interpret-body p (λ X → public-type (η X)))
          S T k (M ↑ scope↑ S (revealᴵ p η)) (N ↑ scope↑ T (revealᴾ p η))
    reveal-observed p η {S} {T} c = R.frame-observed
      (reveal-frm (scope↑ S (revealᴵ p η)))
      (reveal-frm (scope↑ T (revealᴾ p η)))
      (λ { χsᴵ χsᴾ {j} {U} {V} j≤k r →
        subst₂≡ (ObservedComputations
            (interpret-body p (λ X → public-type (η X)))
            (advance S χsᴵ) (advance T χsᴾ) j)
          (sym (cong (λ f → Frame.plug revealFrame f U)
            (reveal-frame-transport S χsᴵ (revealᴵ p η))))
          (sym (cong (λ f → Frame.plug revealFrame f V)
            (reveal-frame-transport T χsᴾ (revealᴾ p η))))
          (reveal-values p η r) }) c

    conceal-observed : ∀ {n C Δᴵ Δᴾ} (p : BodyFragment C)
        (η : TyVar n → VariableConversion)
        {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {k M N}
      → ObservedComputations (interpret-body p (λ X → public-type (η X)))
          S T k M N
      → ObservedComputations (interpret-body p (λ X → abstract-type (η X)))
          S T k (M ↓ scope↓ S (concealᴵ p η)) (N ↓ scope↓ T (concealᴾ p η))
    conceal-observed p η {S} {T} c = D.frame-observed
      (conceal-frm (scope↓ S (concealᴵ p η)))
      (conceal-frm (scope↓ T (concealᴾ p η)))
      (λ { χsᴵ χsᴾ {j} {U} {V} j≤k r →
        subst₂≡ (ObservedComputations
            (interpret-body p (λ X → abstract-type (η X)))
            (advance S χsᴵ) (advance T χsᴾ) j)
          (sym (cong (λ f → Frame.plug concealFrame f U)
            (conceal-frame-transport S χsᴵ (concealᴵ p η))))
          (sym (cong (λ f → Frame.plug concealFrame f V)
            (conceal-frame-transport T χsᴾ (concealᴾ p η))))
          (conceal-values p η r) }) c

    reveal-values : ∀ {n C Δᴵ Δᴾ} (p : BodyFragment C)
        (η : TyVar n → VariableConversion)
        {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {k U V}
      → related (interpret-body p (λ X → abstract-type (η X))) S T k U V
      → ObservedComputations (interpret-body p (λ X → public-type (η X)))
          S T k (U ↑ scope↑ S (revealᴵ p η)) (V ↑ scope↑ T (revealᴾ p η))
    reveal-values natural-body η {S} {T} {k} {U} {V} r =
      subst₂≡ (ObservedComputations natural S T k)
        (sym (cong (λ f → Frame.plug revealFrame f U) (scope↑-id S (‵ `ℕ))))
        (sym (cong (λ f → Frame.plug revealFrame f V) (scope↑-id T (‵ `ℕ))))
        (identity-reveals natural r)
    reveal-values (variable-body {X}) η r with η X
    reveal-values variable-body η {S} {T} {k} {U} {V} r | unchanged A =
      subst₂≡ (ObservedComputations A S T k)
        (sym (cong (λ f → Frame.plug revealFrame f U)
          (scope↑-id S (impreciseTy A))))
        (sym (cong (λ f → Frame.plug revealFrame f V)
          (scope↑-id T (preciseTy A))))
        (identity-reveals A r)
    reveal-values variable-body η {S} {T} {k} {U} {V} r | slot A X Y p q =
      subst₂≡ (ObservedComputations A S T k)
        (sym (cong (λ f → Frame.plug revealFrame f U)
          (scope↑-unseal S X (impreciseTy A))))
        (sym (cong (λ f → Frame.plug revealFrame f V)
          (scope↑-unseal T Y (preciseTy A))))
        (observed-unseals A X Y p q
          (subst≡ (λ C → ⟨ _ , scopeStore S , [] ⟩ ⊢ U ⦂ C)
            (scope-variable S X) (imprecise-typed (nominal A X Y p q) r))
          (subst≡ (λ C → ⟨ _ , scopeStore T , [] ⟩ ⊢ V ⦂ C)
            (scope-variable T Y) (precise-typed (nominal A X Y p q) r))
          (values-observed (nominal A X Y p q) r))
    reveal-values (arrow-body p q) η {S} {T} {k} {F} {G} r =
      values-observed (interpret-body (arrow-body p q)
        (λ X → public-type (η X)))
        (arrow-values
          (subst≡ Value
            (sym (cong (λ f → Frame.plug revealFrame f F)
              (scope↑-arrow S (concealᴵ p η) (revealᴵ q η))))
            (ArrowValues.functionᴵ-value r ↑ fun))
          (subst≡ Value
            (sym (cong (λ f → Frame.plug revealFrame f G)
              (scope↑-arrow T (concealᴾ p η) (revealᴾ q η))))
            (ArrowValues.functionᴾ-value r ↑ fun))
          (⊢reveal (scope↑-valid S (revealᴵ-typed (arrow-body p q) η))
            (ArrowValues.functionᴵ-typed r))
          (⊢reveal (scope↑-valid T (revealᴾ-typed (arrow-body p q) η))
            (ArrowValues.functionᴾ-typed r)) call)
      where
      call : ∀ {Δᴵ′ Δᴾ′} {S′ : PhysicalScope Σᴵ₀ Δᴵ′}
          {T′ : PhysicalScope Σᴾ₀ Δᴾ′} {j U V}
        → (s : ScopeFuture S S′) → (t : ScopeFuture T T′)
        → j < k → related (interpret-body p (λ X → public-type (η X)))
            S′ T′ j U V
        → ObservedComputations (interpret-body q (λ X → public-type (η X)))
            S′ T′ j
            (liftTerm s (F ↑ scope↑ S (revealᴵ (arrow-body p q) η)) · U)
            (liftTerm t (G ↑ scope↑ T (revealᴾ (arrow-body p q) η)) · V)
      call {S′ = S′} {T′} {j} {U} {V} s t j<k args =
        subst₂≡ (ObservedComputations
            (interpret-body q (λ X → public-type (η X))) S′ T′ j)
          (sym (cong (_· U)
            (trans (lift-reveal s F (revealᴵ (arrow-body p q) η))
              (cong (λ f → Frame.plug revealFrame f (liftTerm s F))
                (scope↑-arrow S′ (concealᴵ p η) (revealᴵ q η))))))
          (sym (cong (_· V)
            (trans (lift-reveal t G (revealᴾ (arrow-body p q) η))
              (cong (λ f → Frame.plug revealFrame f (liftTerm t G))
                (scope↑-arrow T′ (concealᴾ p η) (revealᴾ q η))))))
          (reveal-applications
          (scope↓ S′ (concealᴵ p η)) (scope↑ S′ (revealᴵ q η))
          (scope↓ T′ (concealᴾ p η)) (scope↑ T′ (revealᴾ q η))
          (lift-value s (ArrowValues.functionᴵ-value r))
          (lift-value t (ArrowValues.functionᴾ-value r))
          (imprecise-value (interpret-body p (λ X → public-type (η X))) args)
          (precise-value (interpret-body p (λ X → public-type (η X))) args)
          (reveal-observed q η
            (application-observed (interpret-body p (λ X → abstract-type (η X)))
              (interpret-body q (λ X → abstract-type (η X))) j<k
              (future-closed (interpret-body (arrow-body p q)
                (λ X → abstract-type (η X))) s t r)
              (conceal-values p η args))))

    conceal-values : ∀ {n C Δᴵ Δᴾ} (p : BodyFragment C)
        (η : TyVar n → VariableConversion)
        {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {k U V}
      → related (interpret-body p (λ X → public-type (η X))) S T k U V
      → ObservedComputations (interpret-body p (λ X → abstract-type (η X)))
          S T k (U ↓ scope↓ S (concealᴵ p η)) (V ↓ scope↓ T (concealᴾ p η))
    conceal-values natural-body η {S} {T} {k} {U} {V} r =
      subst₂≡ (ObservedComputations natural S T k)
        (sym (cong (λ f → Frame.plug concealFrame f U) (scope↓-id S (‵ `ℕ))))
        (sym (cong (λ f → Frame.plug concealFrame f V) (scope↓-id T (‵ `ℕ))))
        (identity-conceals natural r)
    conceal-values (variable-body {X}) η r with η X
    conceal-values variable-body η {S} {T} {k} {U} {V} r | unchanged A =
      subst₂≡ (ObservedComputations A S T k)
        (sym (cong (λ f → Frame.plug concealFrame f U)
          (scope↓-id S (impreciseTy A))))
        (sym (cong (λ f → Frame.plug concealFrame f V)
          (scope↓-id T (preciseTy A))))
        (identity-conceals A r)
    conceal-values variable-body η {S} {T} {k} {U} {V} r | slot A X Y p q =
      subst₂≡ (ObservedComputations (nominal A X Y p q) S T k)
        (sym (cong (λ f → Frame.plug concealFrame f U)
          (scope↓-seal S X (impreciseTy A))))
        (sym (cong (λ f → Frame.plug concealFrame f V)
          (scope↓-seal T Y (preciseTy A))))
        (values-observed (nominal A X Y p q)
          (related-seals (imprecise-value A r) (precise-value A r) r))
    conceal-values (arrow-body p q) η {S} {T} {k} {F} {G} r =
      values-observed (interpret-body (arrow-body p q)
        (λ X → abstract-type (η X)))
        (arrow-values
          (subst≡ Value
            (sym (cong (λ f → Frame.plug concealFrame f F)
              (scope↓-arrow S (revealᴵ p η) (concealᴵ q η))))
            (ArrowValues.functionᴵ-value r ↓ fun))
          (subst≡ Value
            (sym (cong (λ f → Frame.plug concealFrame f G)
              (scope↓-arrow T (revealᴾ p η) (concealᴾ q η))))
            (ArrowValues.functionᴾ-value r ↓ fun))
          (⊢conceal (scope↓-valid S (concealᴵ-typed (arrow-body p q) η))
            (ArrowValues.functionᴵ-typed r))
          (⊢conceal (scope↓-valid T (concealᴾ-typed (arrow-body p q) η))
            (ArrowValues.functionᴾ-typed r)) call)
      where
      call : ∀ {Δᴵ′ Δᴾ′} {S′ : PhysicalScope Σᴵ₀ Δᴵ′}
          {T′ : PhysicalScope Σᴾ₀ Δᴾ′} {j U V}
        → (s : ScopeFuture S S′) → (t : ScopeFuture T T′)
        → j < k → related (interpret-body p (λ X → abstract-type (η X)))
            S′ T′ j U V
        → ObservedComputations (interpret-body q (λ X → abstract-type (η X)))
            S′ T′ j
            (liftTerm s (F ↓ scope↓ S (concealᴵ (arrow-body p q) η)) · U)
            (liftTerm t (G ↓ scope↓ T (concealᴾ (arrow-body p q) η)) · V)
      call {S′ = S′} {T′} {j} {U} {V} s t j<k args =
        subst₂≡ (ObservedComputations
            (interpret-body q (λ X → abstract-type (η X))) S′ T′ j)
          (sym (cong (_· U)
            (trans (lift-conceal s F (concealᴵ (arrow-body p q) η))
              (cong (λ f → Frame.plug concealFrame f (liftTerm s F))
                (scope↓-arrow S′ (revealᴵ p η) (concealᴵ q η))))))
          (sym (cong (_· V)
            (trans (lift-conceal t G (concealᴾ (arrow-body p q) η))
              (cong (λ f → Frame.plug concealFrame f (liftTerm t G))
                (scope↓-arrow T′ (revealᴾ p η) (concealᴾ q η))))))
          (conceal-applications
          (scope↑ S′ (revealᴵ p η)) (scope↓ S′ (concealᴵ q η))
          (scope↑ T′ (revealᴾ p η)) (scope↓ T′ (concealᴾ q η))
          (lift-value s (ArrowValues.functionᴵ-value r))
          (lift-value t (ArrowValues.functionᴾ-value r))
          (imprecise-value (interpret-body p (λ X → abstract-type (η X))) args)
          (precise-value (interpret-body p (λ X → abstract-type (η X))) args)
          (conceal-observed q η
            (application-observed (interpret-body p (λ X → public-type (η X)))
              (interpret-body q (λ X → public-type (η X))) j<k
              (future-closed (interpret-body (arrow-body p q)
                (λ X → public-type (η X))) s t r)
              (reveal-values p η args))))
