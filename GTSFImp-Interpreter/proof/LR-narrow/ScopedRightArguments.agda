module proof.LR-narrow.ScopedRightArguments where

-- File Charter:
--   * Small argument codes with one fixed imprecise endpoint and independently
--     growing physical scopes. Fresh precise names are admissible by
--     construction.
--   * Interprets codes as scoped semantic types, proves their endpoints, and
--     preserves related values through growth and precise-only sealing.
--   * Fresh denotations agree with the right-nominal constructor used by body
--     compatibility. This is an experimental code family, not a live LR change.

import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopeRebase
open import proof.LR-narrow.ScopedRightNominal
open import proof.LR-narrow.ScopedTypeEquivalence

private
  fresh-entry : ∀ {Δ} {Σ : TyStore Δ} {B R : Ty Δ}
    → B ≡ R → store-bind Σ R ∋ Fin.zero ⦂ ⇑ᵗ B
  fresh-entry refl = Z∋ refl

module Arguments {Δᴵ₀ Δᴾ₀} (Σᴵ₀ : TyStore Δᴵ₀)
    (Σᴾ₀ : TyStore Δᴾ₀) (A : Model.ScopedType Σᴵ₀ Σᴾ₀) where

  private
    module M = Model Σᴵ₀ Σᴾ₀

  mutual
    data Code : ∀ {Δᴵ Δᴾ}
      → PhysicalScope Σᴵ₀ Δᴵ → PhysicalScope Σᴾ₀ Δᴾ → Set where
      base : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
          {T : PhysicalScope Σᴾ₀ Δᴾ}
        → Code S T
      grow-left : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
          {T : PhysicalScope Σᴾ₀ Δᴾ} {R : Ty Δᴵ}
        → Code S T → Code (allocate S R) T
      grow-right : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
          {T : PhysicalScope Σᴾ₀ Δᴾ} {R : Ty Δᴾ}
        → Code S T → Code S (allocate T R)
      seal-code : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
          {T : PhysicalScope Σᴾ₀ Δᴾ} {R : Ty Δᴾ}
        → (a : Code S T) → targetTy a ≡ R → Code S (allocate T R)

    targetTy : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
        {T : PhysicalScope Σᴾ₀ Δᴾ}
      → Code S T → Ty Δᴾ
    targetTy {T = T} base = scopeTy T (M.preciseTy A)
    targetTy (grow-left a) = targetTy a
    targetTy (grow-right a) = ⇑ᵗ (targetTy a)
    targetTy (seal-code a eq) = ＇ Fin.zero

  mutual
    denote : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
        {T : PhysicalScope Σᴾ₀ Δᴾ}
      → Code S T → Model.ScopedType (scopeStore S) (scopeStore T)
    denote {S = S} {T} base = Rebase.rebase S T A
    denote (grow-left {R = R} a) =
      Rebase.rebase (allocate root R) root (denote a)
    denote (grow-right {R = R} a) =
      Rebase.rebase root (allocate root R) (denote a)
    denote {S = S} {T = allocate T R} (seal-code a eq) =
      Nominals.right-nominal (scopeStore S) (store-bind (scopeStore T) R)
        (Rebase.rebase root (allocate root R) (denote a)) Fin.zero
        (fresh-entry (trans (precise-denote a) eq))

    precise-denote : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
        {T : PhysicalScope Σᴾ₀ Δᴾ} (a : Code S T)
      → Model.preciseTy (denote a) ≡ targetTy a
    precise-denote base = refl
    precise-denote (grow-left a) = precise-denote a
    precise-denote (grow-right a) = cong ⇑ᵗ (precise-denote a)
    precise-denote (seal-code a eq) = refl

  imprecise-denote : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
      {T : PhysicalScope Σᴾ₀ Δᴾ} (a : Code S T)
    → Model.impreciseTy (denote a) ≡ scopeTy S (M.impreciseTy A)
  imprecise-denote base = refl
  imprecise-denote (grow-left a) = cong ⇑ᵗ (imprecise-denote a)
  imprecise-denote (grow-right a) = imprecise-denote a
  imprecise-denote (seal-code a eq) = imprecise-denote a

  fresh : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
      {T : PhysicalScope Σᴾ₀ Δᴾ} (a : Code S T)
    → Code S (allocate T (Model.preciseTy (denote a)))
  fresh a = seal-code a (sym (precise-denote a))

  fresh-denotation : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
      {T : PhysicalScope Σᴾ₀ Δᴾ} (a : Code S T)
    → Equivalence.Equivalent (scopeStore S)
        (store-bind (scopeStore T) (Model.preciseTy (denote a)))
        (denote (fresh a))
        (Nominals.right-nominal (scopeStore S)
          (store-bind (scopeStore T) (Model.preciseTy (denote a)))
          (Rebase.rebase root
            (allocate root (Model.preciseTy (denote a))) (denote a))
          Fin.zero (Z∋ refl))
  fresh-denotation a = record
    { imprecise-type = refl
    ; precise-type = refl
    ; to = λ r → r
    ; from = λ r → r
    }

  future-code : ∀ {Δᴵ Δᴾ Δᴵ′ Δᴾ′}
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ}
      {S′ : PhysicalScope Σᴵ₀ Δᴵ′} {T′ : PhysicalScope Σᴾ₀ Δᴾ′}
    → ScopeFuture S S′ → ScopeFuture T T′ → Code S T → Code S′ T′
  future-code stay stay a = a
  future-code (grow p) q a = future-code p q (grow-left a)
  future-code stay (grow q) a = future-code stay q (grow-right a)

  future-related : ∀ {Δᴵ Δᴾ Δᴵ′ Δᴾ′}
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ}
      {S′ : PhysicalScope Σᴵ₀ Δᴵ′} {T′ : PhysicalScope Σᴾ₀ Δᴾ′}
      (p : ScopeFuture S S′) (q : ScopeFuture T T′) (a : Code S T)
      {k U V}
    → Model.related (denote a) root root k U V
    → Model.related (denote (future-code p q a)) root root k
        (liftTerm p U) (liftTerm q V)
  future-related stay stay a r = r
  future-related (grow p) q a r = future-related p q (grow-left a)
    (Model.future-closed (denote a) (grow stay) stay r)
  future-related stay (grow q) a r = future-related stay q (grow-right a)
    (Model.future-closed (denote a) stay (grow stay) r)

  fresh-related : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
      {T : PhysicalScope Σᴾ₀ Δᴾ} (a : Code S T) {k U V}
    → Model.related (denote a) root root k U V
    → Model.related (denote (fresh a)) root root k U
        (⇑ᵗᵐ V ↓ seal Fin.zero (⇑ᵗ (Model.preciseTy (denote a))))
  fresh-related {T = T} a r = related-right-seal
    (lift-value {S = T}
      {T = allocate T (Model.preciseTy (denote a))}
      (grow stay) (Model.precise-value (denote a) r))
    (Model.future-closed (denote a) stay (grow stay) r)
