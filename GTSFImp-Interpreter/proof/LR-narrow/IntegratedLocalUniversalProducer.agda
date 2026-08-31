module proof.LR-narrow.IntegratedLocalUniversalProducer where

-- File Charter:
--   * Constant natural producer inhabitants for the local universal interface.
--   * The family ignores every admissible argument code and returns Nat.
--   * Bare and identity-universal-reveal wrapper inhabitants quantify over
--     arbitrary anchors, future worlds, admissible codes, and indices.
--   * This is a bounded constant-body witness, not general body compatibility.

open import Data.List using ([])
open import Data.Nat using (_<_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym) renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
open import Primitives using (κℕ)
open import Reduction
open import LR-narrow.LogicalRelation using (same-natural)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.IntegratedLocal
open import proof.LR-narrow.IntegratedLocalCodes
open import proof.LR-narrow.IntegratedLocalUniversal
import proof.LR-narrow.ScopedUniversalExperiment as SU

module ConstantProducer {ΔI0 ΔP0} (ΣI0 : TyStore ΔI0)
    (ΣP0 : TyStore ΔP0) where

  module L = Local ΣI0 ΣP0
  module C = Codes ΣI0 ΣP0
  module U = Universals ΣI0 ΣP0

  open L
  open Worlds
  open C
  open U

  private
    lift-body-natural : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
        {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
      → (p : ScopeFuture S T) → liftBody p (‵ `ℕ) ≡ ‵ `ℕ
    lift-body-natural stay = refl
    lift-body-natural (grow p) = lift-body-natural p

    lift-universal-natural : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
        {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
      → (p : ScopeFuture S T) → liftTy p (`∀ (‵ `ℕ)) ≡ `∀ (‵ `ℕ)
    lift-universal-natural stay = refl
    lift-universal-natural (grow p) = lift-universal-natural p

  constant-family : ∀ {ΔI ΔP}
      {S₀ : PhysicalScope ΣI0 ΔI} {T₀ : PhysicalScope ΣP0 ΔP}
    → Family S₀ T₀ (‵ `ℕ) (‵ `ℕ)
  constant-family = record { result = result }
    where
    result : ∀ {ΔA ΔB ΔI ΔP}
        {S₀ : PhysicalScope ΣI0 ΔA} {T₀ : PhysicalScope ΣP0 ΔB}
        {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      → (p : ScopeFuture S₀ S) → (q : ScopeFuture T₀ T)
      → ∀ {RI RP} → Code S T RI RP
      → Code S T (liftBody p (‵ `ℕ) [ RI ]ᵗ)
                 (liftBody q (‵ `ℕ) [ RP ]ᵗ)
    result p q {RI} {RP} a
        rewrite lift-body-natural p | lift-body-natural q = base-code `ℕ

  wrapped-instantiation-future : ∀ {ΔI ΔP}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {RI : Ty ΔI} {RP : Ty ΔP} (W : World S T)
    → Future (grow (grow stay)) (grow stay) W
        (extend-paired (extend-privateI W RI) (＇ Fin.zero) RP)
  wrapped-instantiation-future W = record
    { matched-future = λ m → old-paired (old-privateI m)
    ; only-future = λ o → old-only-paired (old-only-privateI o)
    }

  constant-instantiation-observed : ∀ {ΔI ΔP}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {W : World S T} {RI : Ty ΔI} {RP : Ty ΔP} n k
    → Observed (base `ℕ) stay stay W k
        (SU.constant-polymorphic n ⦂∀ (‵ `ℕ) [ RI ])
        (SU.constant-polymorphic n ⦂∀ (‵ `ℕ) [ RP ])
  constant-instantiation-observed {S = S} {T} {W} {RI} {RP} n k =
    observed-from-returns {gasI = 2} {gasP = 2}
      {W′ = extend-paired W RI RP}
      (SU.constant-return (scopeStore S) RI n)
      (SU.constant-return (scopeStore T) RP n)
      (extend-paired-future W)
      (same-natural n)

  wrapped-instantiation-observed : ∀ {ΔI ΔP}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {W : World S T} {RI : Ty ΔI} {RP : Ty ΔP} n k
    → Observed (base `ℕ) stay stay W k
        (SU.wrapped-constant n ⦂∀ (‵ `ℕ) [ RI ])
        (SU.constant-polymorphic n ⦂∀ (‵ `ℕ) [ RP ])
  wrapped-instantiation-observed {S = S} {T} {W} {RI} {RP} n k =
    observed-from-returns {gasI = 5} {gasP = 2}
      {W′ = extend-paired (extend-privateI W RI) (＇ Fin.zero) RP}
      (SU.wrapped-constant-return (scopeStore S) RI n)
      (SU.constant-return (scopeStore T) RP n)
      (wrapped-instantiation-future W)
      (same-natural n)

  constant-related : ∀ {ΔA ΔB ΔI ΔP}
      {S₀ : PhysicalScope ΣI0 ΔA} {T₀ : PhysicalScope ΣP0 ΔB}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {p : ScopeFuture S₀ S} {q : ScopeFuture T₀ T}
      {W : World S T} n k
    → related (universal constant-family) p q W k
        (SU.constant-polymorphic n) (SU.constant-polymorphic n)
  constant-related {S = S} {T} {p = p} {q} {W} n k =
    universal-values (Λ ($ (κℕ n))) (Λ ($ (κℕ n)))
      (subst≡ (λ A → ⟨ _ , scopeStore S , [] ⟩
        ⊢ SU.constant-polymorphic n ⦂ A)
        (sym (lift-universal-natural p)) (SU.constant-polymorphic-⊢ n))
      (subst≡ (λ A → ⟨ _ , scopeStore T , [] ⟩
        ⊢ SU.constant-polymorphic n ⦂ A)
        (sym (lift-universal-natural q)) (SU.constant-polymorphic-⊢ n))
      instantiate
    where
    instantiate : ∀ {ΔI′ ΔP′}
        {S′ : PhysicalScope ΣI0 ΔI′} {T′ : PhysicalScope ΣP0 ΔP′}
        {W′ : World S′ T′} {j RI RP}
      → (r : ScopeFuture S S′) → (s : ScopeFuture T T′)
      → Future r s W W′ → j < k → (a : Code S′ T′ RI RP)
      → Observed (denote (Family.result constant-family
          (scope-trans p r) (scope-trans q s) a)) stay stay W′ j
          (liftTerm r (SU.constant-polymorphic n)
            ⦂∀ liftBody (scope-trans p r) (‵ `ℕ) [ RI ])
          (liftTerm s (SU.constant-polymorphic n)
            ⦂∀ liftBody (scope-trans q s) (‵ `ℕ) [ RP ])
    instantiate {S′ = S′} {T′} {W′} {j = j} {RI} {RP} r s ext j<k a
        rewrite SU.lift-constant-polymorphic r n
              | SU.lift-constant-polymorphic s n
              | lift-body-natural (scope-trans p r)
              | lift-body-natural (scope-trans q s) =
      constant-instantiation-observed {S = S′} {T = T′}
        {W = W′} {RI = RI} {RP = RP} n j

  wrapped-related : ∀ {ΔA ΔB ΔI ΔP}
      {S₀ : PhysicalScope ΣI0 ΔA} {T₀ : PhysicalScope ΣP0 ΔB}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {p : ScopeFuture S₀ S} {q : ScopeFuture T₀ T}
      {W : World S T} n k
    → related (universal constant-family) p q W k
        (SU.wrapped-constant n) (SU.constant-polymorphic n)
  wrapped-related {S = S} {T} {p = p} {q} {W} n k =
    universal-values ((Λ ($ (κℕ n))) ↑ all) (Λ ($ (κℕ n)))
      (subst≡ (λ A → ⟨ _ , scopeStore S , [] ⟩
        ⊢ SU.wrapped-constant n ⦂ A)
        (sym (lift-universal-natural p)) (SU.wrapped-constant-⊢ n))
      (subst≡ (λ A → ⟨ _ , scopeStore T , [] ⟩
        ⊢ SU.constant-polymorphic n ⦂ A)
        (sym (lift-universal-natural q)) (SU.constant-polymorphic-⊢ n))
      instantiate
    where
    instantiate : ∀ {ΔI′ ΔP′}
        {S′ : PhysicalScope ΣI0 ΔI′} {T′ : PhysicalScope ΣP0 ΔP′}
        {W′ : World S′ T′} {j RI RP}
      → (r : ScopeFuture S S′) → (s : ScopeFuture T T′)
      → Future r s W W′ → j < k → (a : Code S′ T′ RI RP)
      → Observed (denote (Family.result constant-family
          (scope-trans p r) (scope-trans q s) a)) stay stay W′ j
          (liftTerm r (SU.wrapped-constant n)
            ⦂∀ liftBody (scope-trans p r) (‵ `ℕ) [ RI ])
          (liftTerm s (SU.constant-polymorphic n)
            ⦂∀ liftBody (scope-trans q s) (‵ `ℕ) [ RP ])
    instantiate {S′ = S′} {T′} {W′} {j = j} {RI} {RP} r s ext j<k a
        rewrite SU.lift-wrapped-constant r n
              | SU.lift-constant-polymorphic s n
              | lift-body-natural (scope-trans p r)
              | lift-body-natural (scope-trans q s) =
      wrapped-instantiation-observed {S = S′} {T = T′}
        {W = W′} {RI = RI} {RP = RP} n j
