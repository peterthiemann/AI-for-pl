module proof.LR-narrow.IntegratedLocalUniversalIdentity where

-- File Charter:
--   * Occurring-binder identity family for the scope-local universal model.
--   * Results use the argument code in both arrow positions, including codes
--     formed after the initial roots. No arbitrary semantic record is chosen.
--   * Identity-specific membership does not imply general body compatibility.

open import Data.List using ([])
open import Data.Nat using (_<_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym) renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
open import Reduction
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.IntegratedLocal
open import proof.LR-narrow.IntegratedLocalCodes
open import proof.LR-narrow.IntegratedLocalUniversal
open import proof.LR-narrow.IntegratedLocalIdentity
import proof.LR-narrow.ScopedUniversalExperiment as SU

module IdentityUniversal {ΔI0 ΔP0} (ΣI0 : TyStore ΔI0)
    (ΣP0 : TyStore ΔP0) where

  open Local ΣI0 ΣP0
  open Worlds
  open Codes ΣI0 ΣP0
  open Universals ΣI0 ΣP0
  open IdentityAdapters ΣI0 ΣP0

  private
    lift-identity-body : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
        {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
      → (p : ScopeFuture S T)
      → liftBody p (＇ Fin.zero ⇒ ＇ Fin.zero)
          ≡ (＇ Fin.zero ⇒ ＇ Fin.zero)
    lift-identity-body stay = refl
    lift-identity-body (grow p) = lift-identity-body p

    lift-identity-type : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
        {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
      → (p : ScopeFuture S T)
      → liftTy p (`∀ (＇ Fin.zero ⇒ ＇ Fin.zero))
          ≡ `∀ (＇ Fin.zero ⇒ ＇ Fin.zero)
    lift-identity-type stay = refl
    lift-identity-type (grow p) = lift-identity-type p

  identity-family : ∀ {ΔA ΔB} {S₀ : PhysicalScope ΣI0 ΔA}
      {T₀ : PhysicalScope ΣP0 ΔB}
    → Family S₀ T₀ (＇ Fin.zero ⇒ ＇ Fin.zero)
        (＇ Fin.zero ⇒ ＇ Fin.zero)
  identity-family = record { result = result }
    where
    result : ∀ {ΔA ΔB ΔI ΔP}
        {S₀ : PhysicalScope ΣI0 ΔA} {T₀ : PhysicalScope ΣP0 ΔB}
        {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      → (p : ScopeFuture S₀ S) → (q : ScopeFuture T₀ T)
      → ∀ {RI RP} → Code S T RI RP
      → Code S T (liftBody p (＇ Fin.zero ⇒ ＇ Fin.zero) [ RI ]ᵗ)
                 (liftBody q (＇ Fin.zero ⇒ ＇ Fin.zero) [ RP ]ᵗ)
    result p q a rewrite lift-identity-body p | lift-identity-body q =
      arrow-code a a

  identity-instantiation-observed : ∀ {ΔI ΔP}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {W : World S T} {RI RP} (a : Code S T RI RP) k
    → Observed (denote (arrow-code a a)) stay stay W k
        (SU.polymorphic-identity ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ RI ])
        (SU.polymorphic-identity ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ RP ])
  identity-instantiation-observed {S = S} {T} {W} {RI} {RP} a k =
    observed-from-returns {gasI = 1} {gasP = 1}
      {W′ = extend-paired W RI RP}
      (SU.polymorphic-identity-return (scopeStore S) RI)
      (SU.polymorphic-identity-return (scopeStore T) RP)
      (extend-paired-future W)
      (identity-adapters-related (denote a) (Z∋ refl) (Z∋ refl) k)

  polymorphic-identity-related : ∀ {ΔA ΔB ΔI ΔP}
      {S₀ : PhysicalScope ΣI0 ΔA} {T₀ : PhysicalScope ΣP0 ΔB}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {p : ScopeFuture S₀ S} {q : ScopeFuture T₀ T}
      {W : World S T} k
    → related (universal identity-family) p q W k
        SU.polymorphic-identity SU.polymorphic-identity
  polymorphic-identity-related {S = S} {T} {p = p} {q} {W} k =
    universal-values (Λ (ƛ (` 0))) (Λ (ƛ (` 0)))
      (subst≡ (λ C → ⟨ _ , scopeStore S , [] ⟩
        ⊢ SU.polymorphic-identity ⦂ C)
        (sym (lift-identity-type p)) SU.polymorphic-identity-⊢)
      (subst≡ (λ C → ⟨ _ , scopeStore T , [] ⟩
        ⊢ SU.polymorphic-identity ⦂ C)
        (sym (lift-identity-type q)) SU.polymorphic-identity-⊢) instantiate
    where
    instantiate : ∀ {ΔI′ ΔP′} {S′ : PhysicalScope ΣI0 ΔI′}
        {T′ : PhysicalScope ΣP0 ΔP′} {W′ : World S′ T′} {j RI RP}
      → (r : ScopeFuture S S′) → (s : ScopeFuture T T′)
      → Future r s W W′ → j < k → (a : Code S′ T′ RI RP)
      → Observed (denote (Family.result identity-family
          (scope-trans p r) (scope-trans q s) a)) stay stay W′ j
          (liftTerm r SU.polymorphic-identity
            ⦂∀ liftBody (scope-trans p r) (＇ Fin.zero ⇒ ＇ Fin.zero)
              [ RI ])
          (liftTerm s SU.polymorphic-identity
            ⦂∀ liftBody (scope-trans q s) (＇ Fin.zero ⇒ ＇ Fin.zero)
              [ RP ])
    instantiate {W′ = W′} {j = j} r s ext j<k a
        rewrite SU.lift-polymorphic-identity r
              | SU.lift-polymorphic-identity s
              | lift-identity-body (scope-trans p r)
              | lift-identity-body (scope-trans q s) =
      identity-instantiation-observed {W = W′} a j
