module proof.LR-narrow.ScopedRightUniversalIdentity where

-- File Charter:
--   * Builds the concrete right-only universal identity inhabitant for the
--     body-derived family generated from the empty body environment and
--     body α⇒α.
--   * The imprecise endpoint is a fixed source type Aᴵ; admissible argument
--     codes only have to denote scoped types whose imprecise endpoint is Aᴵ
--     at the current source scope.
--   * Instantiation uses the fresh-right body compatibility theorem at each
--     current argument world, retaining the allocating target type-beta step.

import Consistency as Emb
import Data.Fin as Fin
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import TyStore
open import TermCtx using (Z)
open import CastTerms
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedBodyInterpretation
open import proof.LR-narrow.ScopedBodyFamily
open import proof.LR-narrow.ScopedConversionCompatibility as SCC
open import proof.LR-narrow.ScopedRightFreshBodyCompatibility as Fresh
open import proof.LR-narrow.ScopedUniversal
import proof.LR-narrow.ScopedIdentity as SI
import proof.LR-narrow.ScopedUniversalExperiment as SU
open import proof.LR-narrow.VisibleEnvironment

emptyEnvironment : ∀ {Δᴵ Δᴾ} (Σᴵ : TyStore Δᴵ) (Σᴾ : TyStore Δᴾ)
  → VisibleEnvironment Σᴵ Σᴾ zero
emptyEnvironment Σᴵ Σᴾ = record
  { impreciseNames = Emb.empty
  ; preciseNames = Emb.empty
  ; representation = λ ()
  ; impreciseEntry = λ ()
  ; preciseEntry = λ ()
  }

identity-body : BodyFragment {n = suc zero} (＇ Fin.zero ⇒ ＇ Fin.zero)
identity-body = arrow-body variable-body variable-body

module Identity {Δᴵ₀ Δᴾ₀} (Σᴵ₀ : TyStore Δᴵ₀)
    (Σᴾ₀ : TyStore Δᴾ₀) (Aᴵ : Ty Δᴵ₀)
    (Code : ∀ {Δᴵ Δᴾ}
      → PhysicalScope Σᴵ₀ Δᴵ → PhysicalScope Σᴾ₀ Δᴾ → Set)
    (denote : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
        {T : PhysicalScope Σᴾ₀ Δᴾ}
      → Code S T → Model.ScopedType (scopeStore S) (scopeStore T))
    (denote-left : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
        {T : PhysicalScope Σᴾ₀ Δᴾ} (a : Code S T)
      → Model.impreciseTy (denote a) ≡ scopeTy S Aᴵ) where

  module Root = Model Σᴵ₀ Σᴾ₀
  module U = Universals Σᴵ₀ Σᴾ₀

  module F = RightBodyFamily {n = zero} Σᴵ₀ Σᴾ₀ identity-body
    (meaning (emptyEnvironment Σᴵ₀ Σᴾ₀)) Aᴵ Code denote denote-left

  related : ∀ k → Root.related (U.rightUniversal F.family) root root k
    (ƛ (` zero)) SU.polymorphic-identity
  related k = U.right-universal-values
    (ƛ (` zero)) (Λ (ƛ (` zero)))
    (⊢ƛ (⊢` Z)) SU.polymorphic-identity-⊢ call
    where
    call : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
        {T : PhysicalScope Σᴾ₀ Δᴾ} {j}
      → (p : ScopeFuture root S) → (q : ScopeFuture root T)
      → j ≤ k → (a : Code S T)
      → Model.ObservedComputations (scopeStore S) (scopeStore T)
          (U.RightFamily.result F.family {S = S} {T = T} a) root root j
          (liftTerm p (ƛ (` zero)))
          (liftTerm q SU.polymorphic-identity
            ⦂∀ scopeBody T (＇ Fin.zero ⇒ ＇ Fin.zero)
              [ Model.preciseTy (denote a) ])
    call {S = S} {T} {j} p q j≤k a
        rewrite SI.lift-identity p | SU.lift-polymorphic-identity q
          | scope-body-arrow T (＇ Fin.zero) (＇ Fin.zero)
          | scope-body-bound T =
      G.instantiate-observed identity-body (ƛ (` zero))
        (Values.values-observed
          (I.interpret-body identity-body G.extended-meaning)
          (SI.identity-related (G.extended-meaning Fin.zero) j))
      where
      module G = Fresh.Fresh (emptyEnvironment (scopeStore S) (scopeStore T))
        (denote a)
      module I = Interpretation (scopeStore S)
        (store-bind (scopeStore T) (Model.preciseTy (denote a)))
      module Values = SCC.Compatibility (scopeStore S)
        (store-bind (scopeStore T) (Model.preciseTy (denote a)))
