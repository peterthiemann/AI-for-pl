module proof.LR-narrow.ScopedIdentity where

-- File Charter:
--   * Proves identity behavior for every scoped semantic type, including
--     nominal and higher-order types, at every index and physical future.
--   * Supplies the abstract identity for fresh-name universal instantiation.
--     Uses the actual beta evaluator and the three-way observation theorem.

open import Data.List using ([])
open import Data.Nat using (_<_)
open import Data.Product using (_,_; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import TermCtx using (Z)
open import CastTerms
open import Reduction
import Eval as E
open import Interpreter
open import proof.LR-narrow.Application using (value-return-exact)
open import proof.LR-narrow.BetaExpansion using (beta-return-expand)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior

lift-identity : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′} (p : ScopeFuture S T)
  → liftTerm p (ƛ (` 0)) ≡ ƛ (` 0)
lift-identity stay = refl
lift-identity (grow p) = lift-identity p

identity-return : ∀ {Δ} (Σ : TyStore Δ) {V : Term Δ} (vV : Value V)
  → ∃ λ (vV′ : Value V) → interpretFrom Σ 1 ((ƛ (` 0)) · V)
      ≡ returned (E.result Δ (keep ∷ []) V
        (((ƛ (` 0)) · V) —→[ keep ]⟨ pure-step (β vV′) ⟩ V ∎[]) vV)
identity-return Σ vV = beta-return-expand {Σ = Σ} {gas = 0} {N = ` 0}
  vV (value-return-exact {Σ = Σ} 0 vV)

identity-related : ∀ {Δᴵ₀ Δᴾ₀} {Σᴵ₀ : TyStore Δᴵ₀}
    {Σᴾ₀ : TyStore Δᴾ₀} (A : Model.ScopedType Σᴵ₀ Σᴾ₀) k
  → Model.related (Model.arrow Σᴵ₀ Σᴾ₀ A A) root root k (ƛ (` 0)) (ƛ (` 0))
identity-related {Σᴵ₀ = Σᴵ₀} {Σᴾ₀} A k =
  B.arrow-values (ƛ (` 0)) (ƛ (` 0)) (⊢ƛ (⊢` Z)) (⊢ƛ (⊢` Z)) call
  where
  module B = Model Σᴵ₀ Σᴾ₀

  call : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
      {T : PhysicalScope Σᴾ₀ Δᴾ} {j U V}
    → (p : ScopeFuture root S) → (q : ScopeFuture root T)
    → j < k → B.related A S T j U V
    → B.ObservedComputations A S T j
        (liftTerm p (ƛ (` 0)) · U) (liftTerm q (ƛ (` 0)) · V)
  call {S = S} {T} p q j<k args rewrite lift-identity p | lift-identity q
      with identity-return (scopeStore S) (B.imprecise-value A args)
         | identity-return (scopeStore T) (B.precise-value A args)
  call {S = S} {T} p q j<k args | vU , retU | vV , retV =
    B.observed-from-returns {S = S} {T = T} {gasᴵ = 1} {gasᴾ = 1}
      retU retV args
