module proof.LR-narrow.ScopedRightFreshInstantiationExperiment where

-- File Charter:
--   * Regression for right-fresh body instantiation through an allocating
--     target-only type-beta step.
--   * Reuses the right-fresh compatibility theorem, the prior source/target
--     runtime fixture, and the existing nine-step target trace.
--   * Checks semantic higher-order observation and concrete data-ending
--     execution without introducing new operational aliases.

import Data.Fin as Fin
open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ; zero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TermCtx using (Z)
open import CastTerms
open import Conversion using (unseal; ⊢↑-unseal)
open import Reduction
open import Primitives using (κℕ)
open import Interpreter
import Eval as Eval
open import LR-narrow.LogicalRelation using (same-natural)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.VisibleEnvironment
import proof.LR-narrow.ScopedRightBodyCompatibilityExperiment as Prior
import proof.LR-narrow.ScopedRightFreshBodyCompatibilityExperiment as Fixture

module Old = Fixture.Old
module OldI = Fixture.OldI


higherpoly : Term 1
higherpoly = Λ (ƛ (` zero))

higherpoly-value : Value higherpoly
higherpoly-value = Λ (ƛ (` zero))

higherpoly-⊢ : ⟨ 1 , Prior.source-store , [] ⟩
  ⊢ higherpoly ⦂ `∀ Prior.fixtureTy
higherpoly-⊢ = ⊢Λ (ƛ (` zero)) (⊢ƛ (⊢` Z))

higherpoly-instantiated : Term 1
higherpoly-instantiated =
  higherpoly ⦂∀ Prior.fixtureTy [ ‵ `ℕ ]

higherpoly-instantiated-⊢ : ⟨ 1 , Prior.source-store , [] ⟩
  ⊢ higherpoly-instantiated ⦂
    ((‵ `ℕ ⇒ ＇ Fin.zero) ⇒ (‵ `ℕ ⇒ ＇ Fin.zero))
higherpoly-instantiated-⊢ = ⊢• higherpoly-⊢

higherpoly-instantiated-observed : ∀ k
  → Old.ObservedComputations
      (OldI.interpret-body Prior.fixture-body
        (OldI.extend-meaning Old.natural (meaning Fixture.initialEnvironment)))
      root root k (ƛ (` zero)) higherpoly-instantiated
higherpoly-instantiated-observed k =
  Fixture.Fresh.instantiate-observed Prior.fixture-body (ƛ (` zero))
    (Fixture.abstract-identity-observed stay stay k)

instantiation-runtime : ℕ → Term 1
instantiation-runtime n =
  (((higherpoly-instantiated · Prior.source-argument) · $ (κℕ n))
    ↑ unseal Prior.source-var (‵ `ℕ))

instantiation-runtime-⊢ : ∀ n → ⟨ 1 , Prior.source-store , [] ⟩
  ⊢ instantiation-runtime n ⦂ ‵ `ℕ
instantiation-runtime-⊢ n = ⊢reveal (⊢↑-unseal Prior.source-entry)
  (⊢· (⊢· higherpoly-instantiated-⊢ Prior.source-argument-⊢)
    (⊢$ (κℕ n)))

instantiation-runtime-↠ : ∀ n → instantiation-runtime n
  —↠[ bind (‵ `ℕ) ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷
       keep ∷ keep ∷ keep ∷ [] ] $ (κℕ n)
instantiation-runtime-↠ n =
    instantiation-runtime n
  —→[ bind (‵ `ℕ) ]⟨ ξ-reveal
      (ξ-·₁ (ξ-·₁ (β-Λ (ƛ (` zero))) refl) refl) refl ⟩
    Prior.target-runtime n
  —↠[ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷
       keep ∷ [] ]⟨ Prior.target-runtime-↠ n ⟩
    $ (κℕ n) ∎[]

instantiation-runtime-return : ∀ n
  → interpretFrom Prior.source-store 10 (instantiation-runtime n)
      ≡ returned (Eval.result 2
        (bind (‵ `ℕ) ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷
          keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ n)) (instantiation-runtime-↠ n) ($ (κℕ n)))
instantiation-runtime-return n = refl

instantiation-runtime-observed : ∀ n k
  → Old.ObservedComputations Old.natural root root k
      (Prior.source-runtime n) (instantiation-runtime n)
instantiation-runtime-observed n k =
  Old.observed-from-returns {gasᴵ = 3} {gasᴾ = 10}
    (Prior.source-runtime-return n) (instantiation-runtime-return n)
    (same-natural n)
