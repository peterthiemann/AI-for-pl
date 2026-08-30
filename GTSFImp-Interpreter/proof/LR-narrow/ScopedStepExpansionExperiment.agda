module proof.LR-narrow.ScopedStepExpansionExperiment where

-- File Charter:
--   * Regression exercises for scoped right-only step expansion.
--   * Covers a keep beta prefix, a keep beta prefix whose target blames, and
--     an allocating type-beta prefix with the imprecise computation unchanged.
--   * Keeps the continuation observation at the allocated physical target
--     scope, so the target allocation is retained explicitly.

open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ; zero)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import Primitives using (κℕ)
open import Reduction
import Eval as E
open import Interpreter
open import LR-narrow.LogicalRelation using (same-natural)
open import proof.LR-narrow.Application using
  (prepend-return; value-return-exact)
open import proof.LR-narrow.Blame using (blame-now)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedStepExpansion
import proof.LR-narrow.ScopedUniversalExperiment as SU

module Empty = Model store-empty store-empty

id-reveal-natural-return : ∀ {Δ} {Σ : TyStore Δ} n
  → interpretFrom Σ 1 ($ (κℕ n) ↑ id↑ (‵ `ℕ))
      ≡ returned (E.result Δ (keep ∷ []) ($ (κℕ n))
        (($ (κℕ n) ↑ id↑ (‵ `ℕ))
          —→[ keep ]⟨ pure-step (id-reveal ($ (κℕ n))) ⟩
          $ (κℕ n) ∎[]) ($ (κℕ n)))
id-reveal-natural-return {Σ = Σ} n =
  prepend-return {Σ = Σ} {gas = 0} refl
    (value-return-exact {Σ = Σ} 0 ($ (κℕ n)))

keep-beta-return-observed : ∀ n k
  → Empty.ObservedComputations Empty.natural root root k
      ($ (κℕ n)) ((ƛ (` 0)) · $ (κℕ n))
keep-beta-return-observed n k =
  observed-right-step {Σᴵ₀ = store-empty} {Σᴾ₀ = store-empty}
    {B = Empty.natural} {S = root} {T = root}
    (λ ()) refl (pure-step (β ($ (κℕ n)))) refl
    (Empty.observed-from-returns {S = root} {T = root}
      {gasᴵ = 0} {gasᴾ = 0}
      (value-return-exact {Σ = store-empty} 0 ($ (κℕ n)))
      (value-return-exact {Σ = store-empty} 0 ($ (κℕ n)))
      (same-natural n))

keep-beta-target-blame-observed : ∀ n m k
  → Empty.ObservedComputations Empty.natural root root k
      ($ (κℕ n)) ((ƛ blame) · $ (κℕ m))
keep-beta-target-blame-observed n m k =
  observed-right-step {Σᴵ₀ = store-empty} {Σᴾ₀ = store-empty}
    {B = Empty.natural} {S = root} {T = root}
    (λ ()) refl (pure-step (β ($ (κℕ m)))) refl
    (Empty.observed-from-right-blame {gas = zero}
      (blame-now {Σ = store-empty}))

type-beta-target-scope : ∀ R
  → step-scope (bind R) (root {Σ₀ = store-empty})
      ≡ allocate root R
type-beta-target-scope R = refl

type-beta-continuation-observed : ∀ R n k
  → Empty.ObservedComputations Empty.natural root (allocate root R) k
      ($ (κℕ n)) ($ (κℕ n) ↑ id↑ (‵ `ℕ))
type-beta-continuation-observed R n k =
  Empty.observed-from-returns {S = root} {T = allocate root R}
    {gasᴵ = 0} {gasᴾ = 1}
    (value-return-exact {Σ = store-empty} 0 ($ (κℕ n)))
    (id-reveal-natural-return {Σ = store-bind store-empty R} n)
    (same-natural n)

type-beta-bind-observed : ∀ R n k
  → Empty.ObservedComputations Empty.natural root root k
      ($ (κℕ n))
      (SU.constant-polymorphic n ⦂∀ (‵ `ℕ) [ R ])
type-beta-bind-observed R n k =
  observed-right-step {Σᴵ₀ = store-empty} {Σᴾ₀ = store-empty}
    {B = Empty.natural} {S = root} {T = root}
    (λ ()) refl (β-Λ ($ (κℕ n))) refl
    (type-beta-continuation-observed R n k)
