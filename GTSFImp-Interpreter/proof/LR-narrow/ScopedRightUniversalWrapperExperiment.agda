module proof.LR-narrow.ScopedRightUniversalWrapperExperiment where

-- File Charter:
--   * Runtime regression for the identity universal reveal wrapper at empty
--     stores.
--   * Pins the source one-step identity application and the target allocating
--     universal wrapper application to the same first-order natural result.
--   * Exercises semantic wrapper closure, repeated wrapping, constants, and
--     instantiation after unequal physical growth with nested nominal codes.
--   * Includes exact evaluator witnesses and all three data observations.

import Data.Fin as Fin
open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import TermCtx using (Z)
open import CastTerms
open import Conversion
open import Reduction
open import Primitives using (κℕ)
open import Interpreter
import Eval as E
import proof.LR-narrow.ScopedUniversalExperiment as SU
open import LR-narrow.LogicalRelation using (same-natural)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedBodyInterpretation
import proof.LR-narrow.ScopedRightUniversalIdentity as RI
import proof.LR-narrow.ScopedRightUniversalWrapper as RW
import proof.LR-narrow.ScopedRightArgumentExperiment as ArgsFixture

source-runtime : ℕ → Term 0
source-runtime n = (ƛ (` zero)) · $ (κℕ n)

source-runtime-⊢ : ∀ n
  → ⟨ 0 , store-empty , [] ⟩ ⊢ source-runtime n ⦂ ‵ `ℕ
source-runtime-⊢ n = ⊢· (⊢ƛ (⊢` Z)) (⊢$ (κℕ n))

source-runtime-↠ : ∀ n
  → source-runtime n —↠[ keep ∷ [] ] $ (κℕ n)
source-runtime-↠ n =
    source-runtime n
  —→[ keep ]⟨ pure-step (β ($ (κℕ n))) ⟩
    $ (κℕ n) ∎[]

source-runtime-return : ∀ n
  → interpretFrom store-empty 1 (source-runtime n)
      ≡ returned (E.result 0 (keep ∷ []) ($ (κℕ n))
        (source-runtime-↠ n) ($ (κℕ n)))
source-runtime-return n = refl

wrapped-universal : Term 0
wrapped-universal =
  SU.polymorphic-identity ↑ `∀↑ id↑ (＇ Fin.zero ⇒ ＇ Fin.zero)

wrapped-universal-value : Value wrapped-universal
wrapped-universal-value = (Λ (ƛ (` zero))) ↑ all

wrapped-universal-⊢ : ⟨ 0 , store-empty , [] ⟩
  ⊢ wrapped-universal ⦂ `∀ (＇ Fin.zero ⇒ ＇ Fin.zero)
wrapped-universal-⊢ =
  ⊢reveal (⊢↑-∀ ⊢↑-id) SU.polymorphic-identity-⊢

target-runtime : ℕ → Term 0
target-runtime n =
  (wrapped-universal ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ‵ `ℕ ])
    · $ (κℕ n)

target-runtime-⊢ : ∀ n
  → ⟨ 0 , store-empty , [] ⟩ ⊢ target-runtime n ⦂ ‵ `ℕ
target-runtime-⊢ n = ⊢· (⊢• wrapped-universal-⊢) (⊢$ (κℕ n))

target-runtime-↠ : ∀ n → target-runtime n
  —↠[ bind (‵ `ℕ) ∷ bind (＇ Fin.zero) ∷ keep ∷ keep ∷
       keep ∷ keep ∷ keep ∷ keep ∷ [] ] $ (κℕ n)
target-runtime-↠ n =
    target-runtime n
  —→[ bind (‵ `ℕ) ]⟨
      ξ-·₁ (β-reveal-∀ (Λ (ƛ (` zero)))) refl ⟩
    ((((SU.polymorphic-identity ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero)
        [ ＇ Fin.zero ])
        ↑ id↑ (＇ Fin.zero ⇒ ＇ Fin.zero))
        ↑ (seal Fin.zero (‵ `ℕ) ↦↑ unseal Fin.zero (‵ `ℕ)))
      · $ (κℕ n))
  —→[ bind (＇ Fin.zero) ]⟨
      ξ-·₁ (ξ-reveal (ξ-reveal (β-Λ (ƛ (` zero))) refl) refl) refl ⟩
    (((((ƛ (` zero)) ↑
          (seal Fin.zero (＇ Fin.suc Fin.zero)
            ↦↑ unseal Fin.zero (＇ Fin.suc Fin.zero)))
        ↑ id↑ (＇ Fin.suc Fin.zero ⇒ ＇ Fin.suc Fin.zero))
        ↑ (seal (Fin.suc Fin.zero) (‵ `ℕ)
          ↦↑ unseal (Fin.suc Fin.zero) (‵ `ℕ)))
      · $ (κℕ n))
  —→[ keep ]⟨ ξ-·₁
      (ξ-reveal
        (pure-step (id-reveal ((ƛ (` zero)) ↑ fun))) refl) refl ⟩
    ((((ƛ (` zero)) ↑
        (seal Fin.zero (＇ Fin.suc Fin.zero)
          ↦↑ unseal Fin.zero (＇ Fin.suc Fin.zero)))
        ↑ (seal (Fin.suc Fin.zero) (‵ `ℕ)
          ↦↑ unseal (Fin.suc Fin.zero) (‵ `ℕ)))
      · $ (κℕ n))
  —→[ keep ]⟨ pure-step
      (β-reveal-⇒ ((ƛ (` zero)) ↑ fun) ($ (κℕ n))) ⟩
    ((((ƛ (` zero)) ↑
        (seal Fin.zero (＇ Fin.suc Fin.zero)
          ↦↑ unseal Fin.zero (＇ Fin.suc Fin.zero)))
        · ($ (κℕ n) ↓ seal (Fin.suc Fin.zero) (‵ `ℕ)))
      ↑ unseal (Fin.suc Fin.zero) (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (pure-step
        (β-reveal-⇒ (ƛ (` zero)) (($ (κℕ n)) ↓ seal)))
      refl ⟩
    (((ƛ (` zero)) ·
        (($ (κℕ n) ↓ seal (Fin.suc Fin.zero) (‵ `ℕ))
          ↓ seal Fin.zero (＇ Fin.suc Fin.zero)))
      ↑ unseal Fin.zero (＇ Fin.suc Fin.zero))
      ↑ unseal (Fin.suc Fin.zero) (‵ `ℕ)
  —→[ keep ]⟨ ξ-reveal
      (ξ-reveal
        (pure-step (β ((($ (κℕ n)) ↓ seal) ↓ seal))) refl)
      refl ⟩
    ((($ (κℕ n) ↓ seal (Fin.suc Fin.zero) (‵ `ℕ))
        ↓ seal Fin.zero (＇ Fin.suc Fin.zero))
      ↑ unseal Fin.zero (＇ Fin.suc Fin.zero))
      ↑ unseal (Fin.suc Fin.zero) (‵ `ℕ)
  —→[ keep ]⟨ ξ-reveal
      (pure-step (conceal-reveal (($ (κℕ n)) ↓ seal))) refl ⟩
    ($ (κℕ n) ↓ seal (Fin.suc Fin.zero) (‵ `ℕ))
      ↑ unseal (Fin.suc Fin.zero) (‵ `ℕ)
  —→[ keep ]⟨ pure-step (conceal-reveal ($ (κℕ n))) ⟩
    $ (κℕ n) ∎[]

target-runtime-return : ∀ n
  → interpretFrom store-empty 8 (target-runtime n)
      ≡ returned (E.result 2
        (bind (‵ `ℕ) ∷ bind (＇ Fin.zero) ∷ keep ∷ keep ∷
          keep ∷ keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ n)) (target-runtime-↠ n) ($ (κℕ n)))
target-runtime-return n = refl

module Root = Model store-empty store-empty
module Wrapper = RW.Compatibility store-empty store-empty Root.natural
  (RI.emptyEnvironment store-empty store-empty) RI.identity-body
module Identity = RI.Identity store-empty store-empty (‵ `ℕ)
  Wrapper.Args.Code Wrapper.Args.denote Wrapper.Args.imprecise-denote

wrapped-related : ∀ k
  → Root.related (Wrapper.U.rightUniversal Wrapper.F.family)
      root root k (ƛ (` zero)) wrapped-universal
wrapped-related k = Wrapper.wrapper-related (Identity.related k)

-- Reapplying the theorem tests a target value that is itself a wrapper,
-- rather than a syntactic type abstraction.

twice-wrapped-related : ∀ k
  → Root.related (Wrapper.U.rightUniversal Wrapper.F.family)
      root root k (ƛ (` zero))
      (wrapped-universal ↑ `∀↑ id↑ (＇ Fin.zero ⇒ ＇ Fin.zero))
twice-wrapped-related k = Wrapper.wrapper-related (wrapped-related k)

wrapped-instantiated : ∀ k
  → Root.ObservedComputations
      (Wrapper.U.RightFamily.result Wrapper.F.family
        (Wrapper.Args.base {S = root} {T = root}))
      root root k (ƛ (` zero))
      (wrapped-universal ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ‵ `ℕ ])
wrapped-instantiated k = Wrapper.U.RightUniversalValues.instantiate
  (wrapped-related k) stay stay ≤-refl Wrapper.Args.base

future-instantiated : ∀ k
  → Model.ObservedComputations (scopeStore ArgsFixture.grown-source)
      (scopeStore ArgsFixture.grown-target)
      (Wrapper.U.RightFamily.result Wrapper.F.family ArgsFixture.grown-code)
      root root k (ƛ (` zero))
      ((SU.polymorphic-identity ↑ `∀↑ id↑ (＇ Fin.zero ⇒ ＇ Fin.zero))
        ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ＇ Fin.suc Fin.zero ])
future-instantiated k = Wrapper.U.RightUniversalValues.instantiate
  (wrapped-related k) (grow stay) (grow (grow (grow stay)))
  ≤-refl ArgsFixture.grown-code

runtime-observed : ∀ n k → Root.ObservedComputations Root.natural
  root root k (source-runtime n) (target-runtime n)
runtime-observed n k = Root.observed-from-returns {gasᴵ = 1} {gasᴾ = 8}
  (source-runtime-return n) (target-runtime-return n) (same-natural n)

-- Constant universals exercise a different body constructor and source
-- value shape. Reuse their proved instantiation behavior with our codes.

module ConstantWrapper = RW.Compatibility store-empty store-empty
  Root.natural (RI.emptyEnvironment store-empty store-empty) natural-body
module Constants = SU.ConstantFamilies store-empty store-empty

constant-wrapped-related : ∀ n k
  → Root.related (ConstantWrapper.U.rightUniversal ConstantWrapper.F.family)
      root root k ($ (κℕ n)) (SU.wrapped-constant n ↑ `∀↑ id↑ (‵ `ℕ))
constant-wrapped-related n k = ConstantWrapper.wrapper-related
  (ConstantWrapper.U.right-universal-values
    (ConstantWrapper.U.RightUniversalValues.valueᴵ r)
    (ConstantWrapper.U.RightUniversalValues.valueᴾ r)
    (ConstantWrapper.U.RightUniversalValues.typedᴵ r)
    (ConstantWrapper.U.RightUniversalValues.typedᴾ r)
    (λ p q j≤k a → ConstantWrapper.U.RightUniversalValues.instantiate r
      p q j≤k (Model.preciseTy (ConstantWrapper.Args.denote a))))
  where
  r = Constants.right-related n k

constant-instantiated : ∀ n k → Root.ObservedComputations Root.natural
  root root k ($ (κℕ n))
  ((SU.wrapped-constant n ↑ `∀↑ id↑ (‵ `ℕ)) ⦂∀ (‵ `ℕ) [ ‵ `ℕ ])
constant-instantiated n k = ConstantWrapper.U.RightUniversalValues.instantiate
  (constant-wrapped-related n k) stay stay ≤-refl
  (ConstantWrapper.Args.base {S = root} {T = root})
