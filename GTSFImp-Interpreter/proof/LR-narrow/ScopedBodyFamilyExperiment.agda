module proof.LR-narrow.ScopedBodyFamilyExperiment where

-- File Charter:
--   * Reuses the polymorphic identity instantiation proof for derived
--     families. Its typed data-ending trace stays in ScopedUniversalExperiment.
--   * Exercises a higher-order body using both its bound argument and an
--     old environment entry under arbitrary independent physical scopes.
--   * No compatibility property is assumed of the derived result family.

open import Data.Nat using (ℕ; suc)
open import Data.Nat.Properties using (≤-refl)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import TyStore
open import CastTerms
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopeRebase
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedUniversal
import proof.LR-narrow.ScopedIdentity as SI
open import proof.LR-narrow.ScopedBodyInterpretation
open import proof.LR-narrow.ScopedBodyFamily
import proof.LR-narrow.ScopedUniversalExperiment as SU

module DerivedFamilies {Δᴵ₀ Δᴾ₀} (Σᴵ₀ : TyStore Δᴵ₀) (Σᴾ₀ : TyStore Δᴾ₀)
    (Code : ∀ {Δᴵ Δᴾ}
      → PhysicalScope Σᴵ₀ Δᴵ → PhysicalScope Σᴾ₀ Δᴾ → Set)
    (denote : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
        {T : PhysicalScope Σᴾ₀ Δᴾ}
      → Code S T → Model.ScopedType (scopeStore S) (scopeStore T)) where

  module B = Model Σᴵ₀ Σᴾ₀
  module U = Universals Σᴵ₀ Σᴾ₀
  module OldIdentity = SU.IdentityFamily Σᴵ₀ Σᴾ₀ Code denote
  module Identity = BodyFamily {n = 0} Σᴵ₀ Σᴾ₀
    (arrow-body {A = ＇ Fin.zero} {B = ＇ Fin.zero}
      variable-body variable-body) (λ ()) Code denote

  -- Reuses the actual instantiation proof, not just the family endpoints.
  identity-related : ∀ k → B.related (U.universal Identity.family)
    root root k SU.polymorphic-identity SU.polymorphic-identity
  identity-related k = U.universal-values
    (U.UniversalValues.valueᴵ r) (U.UniversalValues.valueᴾ r)
    (U.UniversalValues.typedᴵ r) (U.UniversalValues.typedᴾ r)
    (U.UniversalValues.instantiate r)
    where
    r = OldIdentity.related k

  module Higher = BodyFamily {n = 1} Σᴵ₀ Σᴾ₀
    (arrow-body
      (arrow-body {A = ＇ Fin.zero} {B = ＇ (Fin.suc Fin.zero)}
        variable-body variable-body)
      (arrow-body {A = ＇ Fin.zero} {B = ＇ (Fin.suc Fin.zero)}
        variable-body variable-body))
    (λ _ → B.natural) Code denote

  higher-result-related : ∀ {Δᴵ Δᴾ}
      (S : PhysicalScope Σᴵ₀ Δᴵ) (T : PhysicalScope Σᴾ₀ Δᴾ)
      (a : Code S T) k
    → Model.related (U.PairedFamily.result Higher.family a)
        root root k (ƛ (` 0)) (ƛ (` 0))
  higher-result-related S T a k =
    SI.identity-related
      (Model.arrow (scopeStore S) (scopeStore T)
        (denote a) (Rebase.rebase S T B.natural)) k

-- A syntactic substitution must interpret identically, even when its range
-- contains arrows and both occurrences become function arguments/results.

substituted-endofunction : ∀ {Δᴵ Δᴾ} {Σᴵ : TyStore Δᴵ} {Σᴾ : TyStore Δᴾ}
    (A : Model.ScopedType Σᴵ Σᴾ)
  → Interpretation.interpret-body Σᴵ Σᴾ
      (subst-body {n = 1} {m = 1} (λ _ → ＇ Fin.zero ⇒ ＇ Fin.zero)
        (λ _ → arrow-body variable-body variable-body)
        (arrow-body {A = ＇ Fin.zero} {B = ＇ Fin.zero}
          variable-body variable-body))
      (λ _ → A)
    ≡ Model.arrow Σᴵ Σᴾ (Model.arrow Σᴵ Σᴾ A A) (Model.arrow Σᴵ Σᴾ A A)
substituted-endofunction {Σᴵ = Σᴵ} {Σᴾ} A =
  Interpretation.interpret-substitution Σᴵ Σᴾ {n = 1} {m = 1}
    (λ _ → ＇ Fin.zero ⇒ ＇ Fin.zero)
    (λ _ → arrow-body variable-body variable-body)
    (arrow-body {A = ＇ Fin.zero} {B = ＇ Fin.zero}
      variable-body variable-body) (λ _ → A)

module Tower = DerivedFamilies store-empty store-empty (λ S T → ℕ)
  (λ { {S = S} {T} a → Rebase.rebase S T (SU.argument-tower a) })

derived-tower-instantiations : ∀ a k → SU.Empty.ObservedComputations
  (Tower.U.PairedFamily.result Tower.Identity.family {S = root} {T = root} a)
  root root k
  (SU.polymorphic-identity ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero)
    [ SU.Empty.impreciseTy (SU.argument-tower a) ])
  (SU.polymorphic-identity ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero)
    [ SU.Empty.preciseTy (SU.argument-tower a) ])
derived-tower-instantiations a k = Tower.U.UniversalValues.instantiate
  (Tower.identity-related (suc k)) stay stay ≤-refl a
