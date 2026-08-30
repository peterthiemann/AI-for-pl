module proof.LR-narrow.ScopedRightFreshBodyCompatibility where

-- File Charter:
--   * Specializes structural precise-only body conversion to a fresh target
--     slot, preserving the original imprecise physical root and program.
--   * Re-roots old visible meanings, identifies public bodies with rebased
--     instantiations, and proves canonical generator agreement at all futures.
--   * Derives same-index canonical reveal/conceal observations and expands
--     the actual allocating type-beta step from a related value body.
--   * Does not construct admissible universal arguments or wrapper closure.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans) renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
open import Conversion using (〖_,_↑_〗; makeConceal)
open import Reduction using (β-Λ)
open import Consistency using (toRenameᵗ)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopeRebase
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedRightNominal
open import proof.LR-narrow.ScopedConversionTransport
  using (scope↑; scope↓; scope↑-cong; scope↓-cong;
         scope↑-generated; scope↓-generated)
open import proof.LR-narrow.ScopedBodyInterpretation
  using (BodyFragment; natural-body; variable-body; arrow-body)
open import proof.LR-narrow.TypeRenamingComposition
  using (pack↑; pack↓; pack-↦↑; pack-↦↓; apply↑; apply↓)
open import proof.LR-narrow.VisibleEnvironment
open import proof.LR-narrow.ScopedStepExpansion using (observed-right-step)
open import proof.LR-narrow.TypeBetaExpansion using (type-beta-step-question)
import proof.LR-narrow.ScopedTypeEquivalence as Eq
import proof.LR-narrow.ScopedRightBodyCompatibility as SBC
import proof.LR-narrow.ScopedRightBodyConversion as SBCv
import proof.LR-narrow.ScopedBodyInterpretation as BI

module Fresh {Δᴵ Δᴾ n} {Σᴵ : TyStore Δᴵ} {Σᴾ : TyStore Δᴾ}
    (env : VisibleEnvironment Σᴵ Σᴾ n)
    (A : Model.ScopedType Σᴵ Σᴾ) where

  module R = Rebase {Σᴵ₀ = Σᴵ} {Σᴾ₀ = Σᴾ}
    root (allocate root (Model.preciseTy A))

  private
    module Old = BI.Interpretation Σᴵ Σᴾ
    module New = BI.Interpretation Σᴵ (store-bind Σᴾ (Model.preciseTy A))
    module N = Nominals Σᴵ (store-bind Σᴾ (Model.preciseTy A))
    module C = SBCv.Conversions Σᴵ (store-bind Σᴾ (Model.preciseTy A))
    module K = SBC.Compatibility Σᴵ (store-bind Σᴾ (Model.preciseTy A))
    module EqNew = Eq.Equivalence Σᴵ (store-bind Σᴾ (Model.preciseTy A))
    module BR = BI.BodyRebase {Σᴵ₀ = Σᴵ} {Σᴾ₀ = Σᴾ}
      root (allocate root (Model.preciseTy A))

  -- This is a semantic assignment, not a paired VisibleEnvironment: its
  -- fresh variable has no imprecise nominal name or lookup.

  extended-meaning : TyVar (suc n) → R.New.ScopedType
  extended-meaning Fin.zero = N.right-nominal (R.rebase A) Fin.zero (Z∋ refl)
  extended-meaning (Fin.suc X) =
    meaning (rerootEnvironment root (allocate root (Model.preciseTy A)) env) X

  assignment : TyVar (suc n) → C.RightVariableConversion
  assignment Fin.zero = C.right-slot (R.rebase A) Fin.zero (Z∋ refl)
  assignment (Fin.suc X) = C.unchanged (R.rebase (meaning env X))

  private
    mutual
      root-revealᴾ : ∀ {Cᵀ : Ty (suc n)} (p : BodyFragment Cᵀ)
        → pack↑ (C.revealᴾ p assignment)
          ≡ pack↑ 〖 Fin.zero , ⇑ᵗ (Model.preciseTy A)
              ↑ renameᵗ (extᵗ (toRenameᵗ (preciseNames env))) Cᵀ 〗
      root-revealᴾ natural-body = refl
      root-revealᴾ (variable-body {Fin.zero}) = refl
      root-revealᴾ (variable-body {Fin.suc X}) = refl
      root-revealᴾ (arrow-body p q) =
        cong₂ pack-↦↑ (root-concealᴾ p) (root-revealᴾ q)

      root-concealᴾ : ∀ {Cᵀ : Ty (suc n)} (p : BodyFragment Cᵀ)
        → pack↓ (C.concealᴾ p assignment)
          ≡ pack↓ (makeConceal Fin.zero (⇑ᵗ (Model.preciseTy A))
              (renameᵗ (extᵗ (toRenameᵗ (preciseNames env))) Cᵀ))
      root-concealᴾ natural-body = refl
      root-concealᴾ (variable-body {Fin.zero}) = refl
      root-concealᴾ (variable-body {Fin.suc X}) = refl
      root-concealᴾ (arrow-body p q) =
        cong₂ pack-↦↓ (root-revealᴾ p) (root-concealᴾ q)

  revealᴾ-generated : ∀ {Cᵀ : Ty (suc n)} (p : BodyFragment Cᵀ) {Δᴾ′}
      (T : PhysicalScope (store-bind Σᴾ (Model.preciseTy A)) Δᴾ′)
    → pack↑ (scope↑ T (C.revealᴾ p assignment))
      ≡ pack↑ 〖 scopeVar T Fin.zero , scopeTy T (⇑ᵗ (Model.preciseTy A))
          ↑ scopeTy T
              (renameᵗ (extᵗ (toRenameᵗ (preciseNames env))) Cᵀ) 〗
  revealᴾ-generated {Cᵀ} p T = trans (scope↑-cong T (root-revealᴾ p))
    (scope↑-generated T Fin.zero (⇑ᵗ (Model.preciseTy A))
      (renameᵗ (extᵗ (toRenameᵗ (preciseNames env))) Cᵀ))

  concealᴾ-generated : ∀ {Cᵀ : Ty (suc n)} (p : BodyFragment Cᵀ) {Δᴾ′}
      (T : PhysicalScope (store-bind Σᴾ (Model.preciseTy A)) Δᴾ′)
    → pack↓ (scope↓ T (C.concealᴾ p assignment))
      ≡ pack↓ (makeConceal (scopeVar T Fin.zero)
          (scopeTy T (⇑ᵗ (Model.preciseTy A)))
          (scopeTy T
            (renameᵗ (extᵗ (toRenameᵗ (preciseNames env))) Cᵀ)))
  concealᴾ-generated {Cᵀ} p T = trans (scope↓-cong T (root-concealᴾ p))
    (scope↓-generated T Fin.zero (⇑ᵗ (Model.preciseTy A))
      (renameᵗ (extᵗ (toRenameᵗ (preciseNames env))) Cᵀ))

  private
    abstract-assignment-equivalent : ∀ X
      → EqNew.Equivalent (C.abstract-type (assignment X)) (extended-meaning X)
    abstract-assignment-equivalent Fin.zero = EqNew.eq-refl
    abstract-assignment-equivalent (Fin.suc X) = record
      { imprecise-type = refl
      ; precise-type = refl
      ; to = λ { {S = S} {T} {k} {U} {V} r →
          subst≡ (λ P → P)
            (reroot-meaning root (allocate root (Model.preciseTy A)) env X
              S T k U V) r }
      ; from = λ { {S = S} {T} {k} {U} {V} r →
          subst≡ (λ P → P)
            (sym (reroot-meaning root (allocate root (Model.preciseTy A))
              env X S T k U V)) r }
      }

  abstract-equivalent : ∀ {Cᵀ : Ty (suc n)} (p : BodyFragment Cᵀ)
    → EqNew.Equivalent
        (New.interpret-body p (λ X → C.abstract-type (assignment X)))
        (New.interpret-body p extended-meaning)
  abstract-equivalent p = New.interpret-cong p abstract-assignment-equivalent

  private
    public-assignment-equivalent : ∀ X
      → EqNew.Equivalent (C.public-type (assignment X))
          (R.rebase (Old.extend-meaning A (meaning env) X))
    public-assignment-equivalent Fin.zero = EqNew.eq-refl
    public-assignment-equivalent (Fin.suc X) = EqNew.eq-refl

  public-equivalent : ∀ {Cᵀ : Ty (suc n)} (p : BodyFragment Cᵀ)
    → EqNew.Equivalent
        (New.interpret-body p (λ X → C.public-type (assignment X)))
        (R.rebase (Old.interpret-body p (Old.extend-meaning A (meaning env))))
  public-equivalent p = EqNew.eq-trans
    (New.interpret-cong p public-assignment-equivalent)
    (EqNew.eq-sym (BR.interpret-rebase p (Old.extend-meaning A (meaning env))))

  canonical-reveal-observed : ∀ {Cᵀ : Ty (suc n)} (p : BodyFragment Cᵀ)
      {Δᴵ′ Δᴾ′} {S : PhysicalScope Σᴵ Δᴵ′}
      {T : PhysicalScope (store-bind Σᴾ (Model.preciseTy A)) Δᴾ′} {k M N}
    → R.New.ObservedComputations (New.interpret-body p extended-meaning)
        S T k M N
    → R.New.ObservedComputations
        (R.rebase (Old.interpret-body p (Old.extend-meaning A (meaning env))))
        S T k M
        (N ↑ 〖 scopeVar T Fin.zero , scopeTy T (⇑ᵗ (Model.preciseTy A))
          ↑ scopeTy T
              (renameᵗ (extᵗ (toRenameᵗ (preciseNames env))) Cᵀ) 〗)
  canonical-reveal-observed p {S = S} {T} {k} {M} {N} c =
    subst≡ (R.New.ObservedComputations
        (R.rebase (Old.interpret-body p (Old.extend-meaning A (meaning env))))
        S T k M)
      (cong (apply↑ N) (revealᴾ-generated p T))
      (EqNew.observed-to (public-equivalent p)
        (K.right-reveal-observed p assignment
          (EqNew.observed-to (EqNew.eq-sym (abstract-equivalent p)) c)))

  canonical-conceal-observed : ∀ {Cᵀ : Ty (suc n)} (p : BodyFragment Cᵀ)
      {Δᴵ′ Δᴾ′} {S : PhysicalScope Σᴵ Δᴵ′}
      {T : PhysicalScope (store-bind Σᴾ (Model.preciseTy A)) Δᴾ′} {k M N}
    → R.New.ObservedComputations
        (R.rebase (Old.interpret-body p (Old.extend-meaning A (meaning env))))
        S T k M N
    → R.New.ObservedComputations (New.interpret-body p extended-meaning)
        S T k M
        (N ↓ makeConceal (scopeVar T Fin.zero)
          (scopeTy T (⇑ᵗ (Model.preciseTy A)))
          (scopeTy T
            (renameᵗ (extᵗ (toRenameᵗ (preciseNames env))) Cᵀ)))
  canonical-conceal-observed p {S = S} {T} {k} {M} {N} c =
    subst≡ (R.New.ObservedComputations (New.interpret-body p extended-meaning)
        S T k M)
      (cong (apply↓ N) (concealᴾ-generated p T))
      (EqNew.observed-to (abstract-equivalent p)
        (K.right-conceal-observed p assignment
          (EqNew.observed-to (EqNew.eq-sym (public-equivalent p)) c)))

  instantiate-observed : ∀ {Cᵀ : Ty (suc n)} (p : BodyFragment Cᵀ) {k M V}
    → Value V
    → R.New.ObservedComputations (New.interpret-body p extended-meaning)
        root root k M V
    → R.Old.ObservedComputations
        (Old.interpret-body p (Old.extend-meaning A (meaning env)))
        root root k M
        ((Λ V) ⦂∀ renameᵗ (extᵗ (toRenameᵗ (preciseNames env))) Cᵀ
          [ Model.preciseTy A ])
  instantiate-observed p vV c with type-beta-step-question {Σ = Σᴾ} vV
  instantiate-observed p vV c | vV′ , step =
    observed-right-step (λ ()) refl (β-Λ vV′) step
      (R.observed-from
        (Old.interpret-body p (Old.extend-meaning A (meaning env)))
        (canonical-reveal-observed p c))
