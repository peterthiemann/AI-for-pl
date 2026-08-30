module proof.LR-narrow.ScopedVisibleUniversalWrapperExperiment where

-- File Charter:
--   * Regression for a universal identity wrapper over a body with one
--     old visible natural name and one freshly instantiated type parameter.
--   * Reuses the existing right-fresh instantiation source/runtime fixture and
--     adds the wrapped target term, typing, exact eval, and extracted trace.
--   * Inhabits the mixed-body universal family at every index, then tests
--     wrapper closure and instantiation after unequal private allocations.

import Data.Fin as Fin
open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ; zero; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (∃; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym) renaming (subst to subst≡)

open import Types
open import TyStore
open import TermCtx using (Z)
open import CastTerms
open import Conversion
open import Reduction
open import Primitives using (κℕ)
open import Interpreter
import Eval as E
open import LR-narrow.LogicalRelation using (same-natural)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopeRebase
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedBodyInterpretation
open import proof.LR-narrow.ScopedTypeEquivalence
open import proof.LR-narrow.VisibleEnvironment
import proof.LR-narrow.ScopedConversionCompatibility as CC
import proof.LR-narrow.ScopedRightFreshBodyCompatibility as Fresh
import proof.LR-narrow.ScopedIdentity as SI
import proof.LR-narrow.ScopedUniversalExperiment as SU
import proof.LR-narrow.ScopedRightUniversalWrapper as RW
import proof.LR-narrow.ScopedRightFreshBodyCompatibilityExperiment as Fixture
import proof.LR-narrow.ScopedRightBodyCompatibilityExperiment as Prior
import proof.LR-narrow.ScopedRightFreshInstantiationExperiment as Inst

wrapped-higherpoly : Term 1
wrapped-higherpoly =
  Inst.higherpoly ↑ `∀↑ id↑ Prior.fixtureTy

wrapped-higherpoly-value : Value wrapped-higherpoly
wrapped-higherpoly-value = Inst.higherpoly-value ↑ all

wrapped-higherpoly-⊢ : ⟨ 1 , Prior.source-store , [] ⟩
  ⊢ wrapped-higherpoly ⦂ `∀ Prior.fixtureTy
wrapped-higherpoly-⊢ =
  ⊢reveal (⊢↑-∀ ⊢↑-id) Inst.higherpoly-⊢

target-runtime : ℕ → Term 1
target-runtime n =
  (((wrapped-higherpoly ⦂∀ Prior.fixtureTy [ ‵ `ℕ ])
    · Prior.source-argument) · $ (κℕ n))
    ↑ unseal Prior.source-var (‵ `ℕ)

target-runtime-⊢ : ∀ n → ⟨ 1 , Prior.source-store , [] ⟩
  ⊢ target-runtime n ⦂ ‵ `ℕ
target-runtime-⊢ n = ⊢reveal (⊢↑-unseal Prior.source-entry)
  (⊢· (⊢· (⊢• wrapped-higherpoly-⊢) Prior.source-argument-⊢)
    (⊢$ (κℕ n)))

-- The evaluator already carries the complete trace. Expose its exact
-- history and data endpoint, then reuse that trace as a reduction segment.
-- This keeps the runtime test independent of a hand-reconstructed proof.

target-runtime-return : ∀ n
  → ∃ λ (trace : target-runtime n
      —↠[ bind (‵ `ℕ) ∷ bind (＇ Fin.zero) ∷
           keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷
           keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ]
        $ (κℕ n))
    → interpretFrom Prior.source-store 18 (target-runtime n)
      ≡ returned (E.result 3
        (bind (‵ `ℕ) ∷ bind (＇ Fin.zero) ∷
          keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷
          keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ n)) trace ($ (κℕ n)))
target-runtime-return n = _ , refl

target-runtime-↠ : ∀ n → target-runtime n
  —↠[ bind (‵ `ℕ) ∷ bind (＇ Fin.zero) ∷
       keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷
       keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ] $ (κℕ n)
target-runtime-↠ n =
    target-runtime n
  —↠[ bind (‵ `ℕ) ∷ bind (＇ Fin.zero) ∷
       keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷
       keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ []
    ]⟨ proj₁ (target-runtime-return n) ⟩
    $ (κℕ n) ∎[]

module Root = Model Prior.source-store Prior.source-store
module Wrapper = RW.Compatibility Prior.source-store Prior.source-store
  Root.natural Fixture.initialEnvironment Prior.fixture-body
module Args = Wrapper.Args
module U = Wrapper.U
module F = Wrapper.F

private
  instantiated : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Prior.source-store Δᴵ}
      {T : PhysicalScope Prior.source-store Δᴾ} (a : Args.Code S T) j
    → Model.ObservedComputations (scopeStore S) (scopeStore T)
        (U.RightFamily.result F.family a) root root j (ƛ (` zero))
        ((Λ (ƛ (` zero))) ⦂∀ scopeBody T Prior.fixtureTy
          [ Model.preciseTy (Args.denote a) ])
  instantiated {S = S} {T} a j =
    subst≡ (λ C → Model.ObservedComputations (scopeStore S) (scopeStore T)
        (U.RightFamily.result F.family a) root root j (ƛ (` zero))
        ((Λ (ƛ (` zero))) ⦂∀ C [ Model.preciseTy (Args.denote a) ]))
      (sym (scoped-body-visible T
        (preciseNames Fixture.initialEnvironment) Prior.fixture-body))
      (Eq.observed-to public-result
        (G.instantiate-observed Prior.fixture-body (ƛ (` zero))
          (Values.values-observed
            (New.interpret-body Prior.fixture-body G.extended-meaning)
            (SI.identity-related
              (New.interpret-body Prior.argument-body G.extended-meaning) j))))
    where
    module G = Fresh.Fresh (rerootEnvironment S T Fixture.initialEnvironment)
      (Args.denote a)
    module Old = Interpretation (scopeStore S) (scopeStore T)
    module New = Interpretation (scopeStore S)
      (store-bind (scopeStore T) (Model.preciseTy (Args.denote a)))
    module Eq = Equivalence (scopeStore S) (scopeStore T)
    module Values = CC.Compatibility (scopeStore S)
      (store-bind (scopeStore T) (Model.preciseTy (Args.denote a)))

    public-result : Eq.Equivalent
      (Old.interpret-body Prior.fixture-body
        (Old.extend-meaning (Args.denote a)
          (meaning (rerootEnvironment S T Fixture.initialEnvironment))))
      (U.RightFamily.result F.family a)
    public-result = Old.interpret-cong Prior.fixture-body
      {η = Old.extend-meaning (Args.denote a)
        (meaning (rerootEnvironment S T Fixture.initialEnvironment))}
      {θ = Old.extend-meaning (Args.denote a)
        (λ X → Rebase.rebase S T (meaning Fixture.initialEnvironment X))}
      (λ { Fin.zero → Eq.eq-refl ; (Fin.suc X) → Eq.eq-sym
        (reroot-meaning-equivalent S T Fixture.initialEnvironment X) })

higherpoly-related : ∀ k → Root.related (U.rightUniversal F.family)
  root root k (ƛ (` zero)) Inst.higherpoly
higherpoly-related k = U.right-universal-values
  (ƛ (` zero)) Inst.higherpoly-value
  (⊢ƛ (⊢` Z)) Inst.higherpoly-⊢ call
  where
  call : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Prior.source-store Δᴵ}
      {T : PhysicalScope Prior.source-store Δᴾ} {j}
    → (p : ScopeFuture root S) → (q : ScopeFuture root T)
    → j ≤ k → (a : Args.Code S T)
    → Model.ObservedComputations (scopeStore S) (scopeStore T)
        (U.RightFamily.result F.family a) root root j
        (liftTerm p (ƛ (` zero)))
        (liftTerm q Inst.higherpoly ⦂∀ scopeBody T Prior.fixtureTy
          [ Model.preciseTy (Args.denote a) ])
  call {j = j} p q j≤k a
      rewrite SI.lift-identity p | SU.lift-polymorphic-identity q =
    instantiated a j

wrapped-related : ∀ k → Root.related (U.rightUniversal F.family)
  root root k (ƛ (` zero)) wrapped-higherpoly
wrapped-related k = Wrapper.wrapper-related (higherpoly-related k)

twice-wrapped-related : ∀ k → Root.related (U.rightUniversal F.family)
  root root k (ƛ (` zero))
    (wrapped-higherpoly ↑ `∀↑ id↑ Prior.fixtureTy)
twice-wrapped-related k = Wrapper.wrapper-related (wrapped-related k)

wrapped-instantiated : ∀ k → Root.ObservedComputations
  (U.RightFamily.result F.family (Args.base {S = root} {T = root}))
  root root k (ƛ (` zero))
    (wrapped-higherpoly ⦂∀ Prior.fixtureTy [ ‵ `ℕ ])
wrapped-instantiated k = U.RightUniversalValues.instantiate
  (wrapped-related k) stay stay ≤-refl Args.base

grown-source : PhysicalScope Prior.source-store 2
grown-source = allocate root (‵ `ℕ)

grown-target : PhysicalScope Prior.source-store 3
grown-target = allocate (allocate root (‵ `ℕ)) (‵ `ℕ)

grown-code : Args.Code grown-source grown-target
grown-code = Args.grow-right (Args.fresh
  (Args.grow-left (Args.base {S = root} {T = root})))

future-wrapped-related : ∀ k → Root.related (U.rightUniversal F.family)
  grown-source grown-target k (ƛ (` zero))
    ((Λ (ƛ (` zero))) ↑ `∀↑ id↑ (scopeBody grown-target Prior.fixtureTy))
future-wrapped-related k = Wrapper.wrapper-related
  (Root.future-closed (U.rightUniversal F.family)
    (grow stay) (grow (grow stay)) (higherpoly-related k))

future-instantiated : ∀ k
  → Model.ObservedComputations (scopeStore grown-source)
      (scopeStore grown-target) (U.RightFamily.result F.family grown-code)
      root root k (ƛ (` zero))
      (((Λ (ƛ (` zero))) ↑ `∀↑ id↑ (scopeBody grown-target Prior.fixtureTy))
        ⦂∀ scopeBody grown-target Prior.fixtureTy [ ＇ Fin.suc Fin.zero ])
future-instantiated k = U.RightUniversalValues.instantiate
  (future-wrapped-related k) stay stay ≤-refl grown-code

runtime-observed : ∀ n k → Root.ObservedComputations Root.natural
  root root k (Prior.source-runtime n) (target-runtime n)
runtime-observed n k = Root.observed-from-returns {gasᴵ = 3} {gasᴾ = 18}
  (Prior.source-runtime-return n) (proj₂ (target-runtime-return n))
  (same-natural n)
