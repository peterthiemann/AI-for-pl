module proof.LR-narrow.ScopedFreshBodyCompatibility where

-- File Charter:
--   * Specializes body conversion/compatibility to the fresh visible binder
--     introduced by VisibleEnvironment.Extend.
--   * Relates the fresh nominal-body interpretation to the extended visible
--     environment and the public-body interpretation to the rebased original
--     body with the semantic argument substituted.
--   * Identifies compiled conversions with the canonical runtime generators,
--     then derives canonical reveal/conceal observations. Universal-wrapper
--     compatibility, in particular its one-sided case, is not claimed here.

import Data.Fin as Fin

open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans) renaming (subst₂ to subst₂≡)
open import Types
open import TyStore
open import CastTerms
open import Conversion using (〖_,_↑_〗; makeConceal)
open import Consistency using (toRenameᵗ)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedConversionTransport
  using (scope↑; scope↓; scope↑-cong; scope↓-cong;
         scope↑-generated; scope↓-generated)
open import proof.LR-narrow.ScopedBodyInterpretation
  using (BodyFragment; natural-body; variable-body; arrow-body)
open import proof.LR-narrow.TypeRenamingComposition
  using (pack↑; pack↓; pack-↦↑; pack-↦↓; apply↑; apply↓)
open import proof.LR-narrow.ScopedTypeEquivalence as Eq
open import proof.LR-narrow.VisibleEnvironment
open import proof.LR-narrow.ScopedBodyCompatibility as SBC
open import proof.LR-narrow.ScopedBodyConversion as SBCv
import proof.LR-narrow.ScopedBodyInterpretation as BI

module Fresh {Δᴵ Δᴾ n} {Σᴵ : TyStore Δᴵ} {Σᴾ : TyStore Δᴾ}
    (env : VisibleEnvironment Σᴵ Σᴾ n)
    (A : Model.ScopedType Σᴵ Σᴾ) where

  private
    module E = Extend env A
    module Old = BI.Interpretation Σᴵ Σᴾ
    module New = BI.Interpretation
      (store-bind Σᴵ (Model.impreciseTy A))
      (store-bind Σᴾ (Model.preciseTy A))
    module C = SBCv.Conversions
      (store-bind Σᴵ (Model.impreciseTy A))
      (store-bind Σᴾ (Model.preciseTy A))
    module K = SBC.Compatibility
      (store-bind Σᴵ (Model.impreciseTy A))
      (store-bind Σᴾ (Model.preciseTy A))
    module EqNew = Eq.Equivalence
      (store-bind Σᴵ (Model.impreciseTy A))
      (store-bind Σᴾ (Model.preciseTy A))
    module V = BI.VisibleBodyExtension env A
    module R = BI.BodyRebase {Σᴵ₀ = Σᴵ} {Σᴾ₀ = Σᴾ}
      (allocate root (Model.impreciseTy A))
      (allocate root (Model.preciseTy A))

  assignment : TyVar (suc n) → C.VariableConversion
  assignment Fin.zero =
    C.slot (E.R.rebase A) Fin.zero Fin.zero (Z∋ refl) (Z∋ refl)
  assignment (Fin.suc X) = C.unchanged (E.R.rebase (meaning env X))

  private
    mutual
      root-revealᴵ : ∀ {Cᵀ : Ty (suc n)} (p : BodyFragment Cᵀ)
        → pack↑ (C.revealᴵ p assignment)
          ≡ pack↑ 〖 Fin.zero , ⇑ᵗ (Model.impreciseTy A)
              ↑ renameᵗ (extᵗ (toRenameᵗ (impreciseNames env))) Cᵀ 〗
      root-revealᴵ natural-body = refl
      root-revealᴵ (variable-body {Fin.zero}) = refl
      root-revealᴵ (variable-body {Fin.suc X}) = refl
      root-revealᴵ (arrow-body p q) =
        cong₂ pack-↦↑ (root-concealᴵ p) (root-revealᴵ q)

      root-concealᴵ : ∀ {Cᵀ : Ty (suc n)} (p : BodyFragment Cᵀ)
        → pack↓ (C.concealᴵ p assignment)
          ≡ pack↓ (makeConceal Fin.zero (⇑ᵗ (Model.impreciseTy A))
              (renameᵗ (extᵗ (toRenameᵗ (impreciseNames env))) Cᵀ))
      root-concealᴵ natural-body = refl
      root-concealᴵ (variable-body {Fin.zero}) = refl
      root-concealᴵ (variable-body {Fin.suc X}) = refl
      root-concealᴵ (arrow-body p q) =
        cong₂ pack-↦↓ (root-revealᴵ p) (root-concealᴵ q)

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

  revealᴵ-generated : ∀ {Cᵀ : Ty (suc n)} (p : BodyFragment Cᵀ) {Δᴵ′}
      (S : PhysicalScope (store-bind Σᴵ (Model.impreciseTy A)) Δᴵ′)
    → pack↑ (scope↑ S (C.revealᴵ p assignment))
      ≡ pack↑ 〖 scopeVar S Fin.zero , scopeTy S (⇑ᵗ (Model.impreciseTy A))
          ↑ scopeTy S
              (renameᵗ (extᵗ (toRenameᵗ (impreciseNames env))) Cᵀ) 〗
  revealᴵ-generated {Cᵀ} p S = trans (scope↑-cong S (root-revealᴵ p))
    (scope↑-generated S Fin.zero (⇑ᵗ (Model.impreciseTy A))
      (renameᵗ (extᵗ (toRenameᵗ (impreciseNames env))) Cᵀ))

  concealᴵ-generated : ∀ {Cᵀ : Ty (suc n)} (p : BodyFragment Cᵀ) {Δᴵ′}
      (S : PhysicalScope (store-bind Σᴵ (Model.impreciseTy A)) Δᴵ′)
    → pack↓ (scope↓ S (C.concealᴵ p assignment))
      ≡ pack↓ (makeConceal (scopeVar S Fin.zero)
          (scopeTy S (⇑ᵗ (Model.impreciseTy A)))
          (scopeTy S
            (renameᵗ (extᵗ (toRenameᵗ (impreciseNames env))) Cᵀ)))
  concealᴵ-generated {Cᵀ} p S = trans (scope↓-cong S (root-concealᴵ p))
    (scope↓-generated S Fin.zero (⇑ᵗ (Model.impreciseTy A))
      (renameᵗ (extᵗ (toRenameᵗ (impreciseNames env))) Cᵀ))

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
      → EqNew.Equivalent (C.abstract-type (assignment X))
          (New.extend-meaning
            (E.R.New.nominal (E.R.rebase A) Fin.zero Fin.zero
              (Z∋ refl) (Z∋ refl))
            (λ Y → E.R.rebase (meaning env Y)) X)
    abstract-assignment-equivalent Fin.zero = EqNew.eq-refl
    abstract-assignment-equivalent (Fin.suc X) = EqNew.eq-refl

  abstract-equivalent : ∀ {Cᵀ : Ty (suc n)} (p : BodyFragment Cᵀ)
    → EqNew.Equivalent
        (New.interpret-body p (λ X → C.abstract-type (assignment X)))
        (New.interpret-body p (meaning E.extended))
  abstract-equivalent p = EqNew.eq-trans
    (New.interpret-cong p abstract-assignment-equivalent)
    (V.interpret-extended p)

  private
    public-assignment-equivalent : ∀ X
      → EqNew.Equivalent (C.public-type (assignment X))
          (E.R.rebase (Old.extend-meaning A (meaning env) X))
    public-assignment-equivalent Fin.zero = EqNew.eq-refl
    public-assignment-equivalent (Fin.suc X) = EqNew.eq-refl

  public-equivalent : ∀ {Cᵀ : Ty (suc n)} (p : BodyFragment Cᵀ)
    → EqNew.Equivalent
        (New.interpret-body p (λ X → C.public-type (assignment X)))
        (E.R.rebase
          (Old.interpret-body p (Old.extend-meaning A (meaning env))))
  public-equivalent p = EqNew.eq-trans
    (New.interpret-cong p public-assignment-equivalent)
    (EqNew.eq-sym (R.interpret-rebase p (Old.extend-meaning A (meaning env))))

  canonical-reveal-observed : ∀ {Cᵀ : Ty (suc n)} (p : BodyFragment Cᵀ)
      {Δᴵ′ Δᴾ′}
      {S : PhysicalScope (store-bind Σᴵ (Model.impreciseTy A)) Δᴵ′}
      {T : PhysicalScope (store-bind Σᴾ (Model.preciseTy A)) Δᴾ′}
      {k M N}
    → Model.ObservedComputations
        (store-bind Σᴵ (Model.impreciseTy A))
        (store-bind Σᴾ (Model.preciseTy A))
        (New.interpret-body p (meaning E.extended)) S T k M N
    → Model.ObservedComputations
        (store-bind Σᴵ (Model.impreciseTy A))
        (store-bind Σᴾ (Model.preciseTy A))
        (E.R.rebase
          (Old.interpret-body p (Old.extend-meaning A (meaning env))))
        S T k
        (M ↑ 〖 scopeVar S Fin.zero , scopeTy S (⇑ᵗ (Model.impreciseTy A))
          ↑ scopeTy S
              (renameᵗ (extᵗ (toRenameᵗ (impreciseNames env))) Cᵀ) 〗)
        (N ↑ 〖 scopeVar T Fin.zero , scopeTy T (⇑ᵗ (Model.preciseTy A))
          ↑ scopeTy T
              (renameᵗ (extᵗ (toRenameᵗ (preciseNames env))) Cᵀ) 〗)
  canonical-reveal-observed p {S = S} {T} {k} {M} {N} c =
    subst₂≡ (Model.ObservedComputations
        (store-bind Σᴵ (Model.impreciseTy A))
        (store-bind Σᴾ (Model.preciseTy A))
        (E.R.rebase
          (Old.interpret-body p (Old.extend-meaning A (meaning env)))) S T k)
      (cong (apply↑ M) (revealᴵ-generated p S))
      (cong (apply↑ N) (revealᴾ-generated p T))
      (EqNew.observed-to (public-equivalent p)
        (K.reveal-observed p assignment
          (EqNew.observed-to (EqNew.eq-sym (abstract-equivalent p)) c)))

  canonical-conceal-observed : ∀ {Cᵀ : Ty (suc n)} (p : BodyFragment Cᵀ)
      {Δᴵ′ Δᴾ′}
      {S : PhysicalScope (store-bind Σᴵ (Model.impreciseTy A)) Δᴵ′}
      {T : PhysicalScope (store-bind Σᴾ (Model.preciseTy A)) Δᴾ′}
      {k M N}
    → Model.ObservedComputations
        (store-bind Σᴵ (Model.impreciseTy A))
        (store-bind Σᴾ (Model.preciseTy A))
        (E.R.rebase
          (Old.interpret-body p (Old.extend-meaning A (meaning env))))
        S T k M N
    → Model.ObservedComputations
        (store-bind Σᴵ (Model.impreciseTy A))
        (store-bind Σᴾ (Model.preciseTy A))
        (New.interpret-body p (meaning E.extended)) S T k
        (M ↓ makeConceal (scopeVar S Fin.zero)
          (scopeTy S (⇑ᵗ (Model.impreciseTy A)))
          (scopeTy S
            (renameᵗ (extᵗ (toRenameᵗ (impreciseNames env))) Cᵀ)))
        (N ↓ makeConceal (scopeVar T Fin.zero)
          (scopeTy T (⇑ᵗ (Model.preciseTy A)))
          (scopeTy T
            (renameᵗ (extᵗ (toRenameᵗ (preciseNames env))) Cᵀ)))
  canonical-conceal-observed p {S = S} {T} {k} {M} {N} c =
    subst₂≡ (Model.ObservedComputations
        (store-bind Σᴵ (Model.impreciseTy A))
        (store-bind Σᴾ (Model.preciseTy A))
        (New.interpret-body p (meaning E.extended)) S T k)
      (cong (apply↓ M) (concealᴵ-generated p S))
      (cong (apply↓ N) (concealᴾ-generated p T))
      (EqNew.observed-to (abstract-equivalent p)
        (K.conceal-observed p assignment
          (EqNew.observed-to (EqNew.eq-sym (public-equivalent p)) c)))
