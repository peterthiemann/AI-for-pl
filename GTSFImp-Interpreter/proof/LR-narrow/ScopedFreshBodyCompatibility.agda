module proof.LR-narrow.ScopedFreshBodyCompatibility where

-- File Charter:
--   * Specializes body conversion/compatibility to the fresh visible binder
--     introduced by VisibleEnvironment.Extend.
--   * Relates the fresh nominal-body interpretation to the extended visible
--     environment and the public-body interpretation to the rebased original
--     body with the semantic argument substituted.
--   * Provides reveal/conceal observation wrappers only; it does not claim
--     canonical generator equality or universal-wrapper compatibility.

import Data.Fin as Fin

open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (refl)
open import Types
open import TyStore
open import CastTerms
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedConversionTransport
  using (scope↑; scope↓)
open import proof.LR-narrow.ScopedBodyInterpretation
  using (BodyFragment)
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

  fresh-reveal-observed : ∀ {Cᵀ : Ty (suc n)} (p : BodyFragment Cᵀ)
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
        (M ↑ scope↑ S (C.revealᴵ p assignment))
        (N ↑ scope↑ T (C.revealᴾ p assignment))
  fresh-reveal-observed p c =
    EqNew.observed-to (public-equivalent p)
      (K.reveal-observed p assignment
        (EqNew.observed-to (EqNew.eq-sym (abstract-equivalent p)) c))

  fresh-conceal-observed : ∀ {Cᵀ : Ty (suc n)} (p : BodyFragment Cᵀ)
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
        (M ↓ scope↓ S (C.concealᴵ p assignment))
        (N ↓ scope↓ T (C.concealᴾ p assignment))
  fresh-conceal-observed p c =
    EqNew.observed-to (abstract-equivalent p)
      (K.conceal-observed p assignment
        (EqNew.observed-to (EqNew.eq-sym (public-equivalent p)) c))
