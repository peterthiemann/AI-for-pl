module proof.LR-narrow.ScopedBodyFamily where

-- File Charter:
--   * Derives paired universal result families from a body interpretation
--     and a semantic environment, instead of arbitrary result assignments.
--   * Argument codes stay small; their denotations may use every current
--     physical slot. Old environment meanings are rebased, not lowered.
--   * Endpoint coherence follows from scoped substitution/opening laws.
--     This is not yet compatibility of the universal conversion wrapper.

open import Data.Nat using (suc)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (refl; trans)

open import Types
open import TyStore
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopeRebase
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedUniversal
open import proof.LR-narrow.ScopedTypeSubstitution
open import proof.LR-narrow.ScopedBodyInterpretation

module BodyFamily {Δᴵ₀ Δᴾ₀ n} (Σᴵ₀ : TyStore Δᴵ₀) (Σᴾ₀ : TyStore Δᴾ₀)
    {C : Ty (suc n)} (body : BodyFragment C)
    (η : TyVar n → Model.ScopedType Σᴵ₀ Σᴾ₀)
    (Code : ∀ {Δᴵ Δᴾ}
      → PhysicalScope Σᴵ₀ Δᴵ → PhysicalScope Σᴾ₀ Δᴾ → Set)
    (denote : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
        {T : PhysicalScope Σᴾ₀ Δᴾ}
      → Code S T → Model.ScopedType (scopeStore S) (scopeStore T)) where

  module U = Universals Σᴵ₀ Σᴾ₀

  family : U.PairedFamily
    (substᵗ (extsᵗ (λ X → Model.impreciseTy (η X))) C)
    (substᵗ (extsᵗ (λ X → Model.preciseTy (η X))) C)
  family = record
    { Argument = Code
    ; argumentᴵ = λ a → Model.impreciseTy (denote a)
    ; argumentᴾ = λ a → Model.preciseTy (denote a)
    ; result = λ { {S = S} {T} a →
        Interpretation.interpret-body (scopeStore S) (scopeStore T) body
          (Interpretation.extend-meaning (scopeStore S) (scopeStore T)
            (denote a) (λ X → Rebase.rebase S T (η X))) }
    ; resultᴵ = λ { {S = S} {T} a → trans
        (Interpretation.endpointᴵ (scopeStore S) (scopeStore T) body
          (Interpretation.extend-meaning (scopeStore S) (scopeStore T)
            (denote a) (λ X → Rebase.rebase S T (η X))))
        (trans
          (substᵗ-cong C (λ { Fin.zero → refl ; (Fin.suc X) → refl }))
          (scope-instantiate S (λ X → Model.impreciseTy (η X)) C
            (Model.impreciseTy (denote a)))) }
    ; resultᴾ = λ { {S = S} {T} a → trans
        (Interpretation.endpointᴾ (scopeStore S) (scopeStore T) body
          (Interpretation.extend-meaning (scopeStore S) (scopeStore T)
            (denote a) (λ X → Rebase.rebase S T (η X))))
        (trans
          (substᵗ-cong C (λ { Fin.zero → refl ; (Fin.suc X) → refl }))
          (scope-instantiate T (λ X → Model.preciseTy (η X)) C
            (Model.preciseTy (denote a)))) }
    }
