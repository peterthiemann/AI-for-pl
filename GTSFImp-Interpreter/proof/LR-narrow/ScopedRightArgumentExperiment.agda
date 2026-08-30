module proof.LR-narrow.ScopedRightArgumentExperiment where

-- File Charter:
--   * Concrete operational regression for a nested right-only argument code.
--   * The source endpoint is the literal natural `n`; the precise endpoint
--     instantiates the polymorphic identity at a fresh nominal name, applies
--     it to a doubly sealed natural, then unseals twice back to `n`.
--   * Records exact typing, the six-step target reduction chain, and the
--     corresponding evaluator equations. No semantic code or family theorem
--     is assumed: the final regressions instantiate the proved small-code
--     construction and body-derived right-universal identity theorem.

open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (≤-refl)
import Data.Fin as Fin
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
open import proof.LR-narrow.Application using (value-return-exact)
import proof.LR-narrow.ScopedUniversalExperiment as SU
open import LR-narrow.LogicalRelation using (same-natural)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedRightArguments
open import proof.LR-narrow.ScopedTypeEquivalence
open import proof.LR-narrow.ScopedBodyInterpretation
import proof.LR-narrow.ScopedRightUniversalIdentity as RI
import proof.LR-narrow.ScopedRightFreshBodyCompatibility as Fresh

source-store : TyStore 0
source-store = store-empty

target-store : TyStore 2
target-store = store-bind (store-bind store-empty (‵ `ℕ)) (＇ Fin.zero)

new-name : TyVar 2
new-name = Fin.zero

old-name : TyVar 2
old-name = Fin.suc Fin.zero

new-entry : target-store ∋ new-name ⦂ ＇ old-name
new-entry = Z∋ refl

old-entry : target-store ∋ old-name ⦂ ‵ `ℕ
old-entry = S-bind∋ (Z∋ refl) refl

source-natural : ℕ → Term 0
source-natural n = $ (κℕ n)

source-natural-⊢ : ∀ n → ⟨ 0 , source-store , [] ⟩ ⊢ source-natural n ⦂ ‵ `ℕ
source-natural-⊢ n = ⊢$ (κℕ n)

source-natural-eval : ∀ n
  → interpretFrom source-store 0 (source-natural n)
      ≡ returned (E.result 0 [] ($ (κℕ n))
        (($ (κℕ n)) ∎[]) ($ (κℕ n)))
source-natural-eval n =
  value-return-exact {Σ = source-store} 0 ($ (κℕ n))

doubly-sealed : ℕ → Term 2
doubly-sealed n =
  (($ (κℕ n)) ↓ seal old-name (‵ `ℕ))
    ↓ seal new-name (＇ old-name)

doubly-sealed-value : ∀ n → Value (doubly-sealed n)
doubly-sealed-value n = (($ (κℕ n)) ↓ seal) ↓ seal

doubly-sealed-⊢ : ∀ n
  → ⟨ 2 , target-store , [] ⟩ ⊢ doubly-sealed n ⦂ ＇ new-name
doubly-sealed-⊢ n =
  ⊢conceal (⊢↓-seal new-entry)
    (⊢conceal (⊢↓-seal old-entry) (⊢$ (κℕ n)))

instantiated-identity : Term 2
instantiated-identity =
  SU.polymorphic-identity ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ＇ Fin.zero ]

instantiated-identity-⊢ : ⟨ 2 , target-store , [] ⟩
  ⊢ instantiated-identity ⦂ (＇ new-name ⇒ ＇ new-name)
instantiated-identity-⊢ = ⊢• SU.polymorphic-identity-⊢

target-runtime : ℕ → Term 2
target-runtime n =
  (((instantiated-identity · doubly-sealed n)
      ↑ unseal new-name (＇ old-name))
      ↑ unseal old-name (‵ `ℕ))

target-runtime-⊢ : ∀ n → ⟨ 2 , target-store , [] ⟩ ⊢ target-runtime n ⦂ ‵ `ℕ
target-runtime-⊢ n = ⊢reveal (⊢↑-unseal old-entry)
  (⊢reveal (⊢↑-unseal new-entry)
    (⊢· instantiated-identity-⊢ (doubly-sealed-⊢ n)))

target-runtime-↠ : ∀ n → target-runtime n
  —↠[ bind (＇ Fin.zero) ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ]
      $ (κℕ n)
target-runtime-↠ n =
    target-runtime n
  —→[ bind (＇ Fin.zero) ]⟨ ξ-reveal
      (ξ-reveal (ξ-·₁ (β-Λ (ƛ (` 0))) refl) refl) refl ⟩
    (((((ƛ (` 0)) ↑ (seal Fin.zero (＇ (Fin.suc Fin.zero))
          ↦↑ unseal Fin.zero (＇ (Fin.suc Fin.zero))))
        · ((($ (κℕ n)) ↓ seal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ))
            ↓ seal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero)))))
        ↑ unseal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero))))
      ↑ unseal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (ξ-reveal
        (pure-step (β-reveal-⇒ (ƛ (` 0)) ((($ (κℕ n)) ↓ seal) ↓ seal))) refl)
      refl ⟩
    ((((((ƛ (` 0))
        · (((($ (κℕ n)) ↓ seal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ))
              ↓ seal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero))))
              ↓ seal Fin.zero (＇ (Fin.suc Fin.zero))))
        ↑ unseal Fin.zero (＇ (Fin.suc Fin.zero))))
      ↑ unseal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero))))
      ↑ unseal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (ξ-reveal (ξ-reveal
        (pure-step (β (((($ (κℕ n)) ↓ seal) ↓ seal) ↓ seal))) refl) refl)
        refl ⟩
    ((((((($ (κℕ n)) ↓ seal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ))
        ↓ seal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero))))
        ↓ seal Fin.zero (＇ (Fin.suc Fin.zero)))
        ↑ unseal Fin.zero (＇ (Fin.suc Fin.zero)))
      ↑ unseal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero))))
      ↑ unseal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (ξ-reveal (pure-step (conceal-reveal
        ((($ (κℕ n)) ↓ seal) ↓ seal))) refl) refl ⟩
    ((((($ (κℕ n)) ↓ seal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ))
        ↓ seal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero))))
      ↑ unseal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero))))
      ↑ unseal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (pure-step (conceal-reveal (($ (κℕ n)) ↓ seal))) refl ⟩
    (($ (κℕ n)) ↓ seal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ))
      ↑ unseal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ)
  —→[ keep ]⟨ pure-step (conceal-reveal ($ (κℕ n))) ⟩
    $ (κℕ n) ∎[]

target-runtime-eval : ∀ n
  → interpretFrom target-store 6 (target-runtime n)
      ≡ returned (E.result 3
        (bind (＇ Fin.zero) ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ n)) (target-runtime-↠ n) ($ (κℕ n)))
target-runtime-eval n = refl

runtime-observed : ∀ n k
  → Model.ObservedComputations source-store target-store
      (Model.natural source-store target-store) root root k
      (source-natural n) (target-runtime n)
runtime-observed n k = Model.observed-from-returns source-store target-store
  {gasᴵ = 0} {gasᴾ = 6} (source-natural-eval n) (target-runtime-eval n)
  (same-natural n)

-- The runtime's two nominal names come from two successive admissible codes.

module Seed = Model source-store source-store
module Codes = Arguments source-store source-store Seed.natural
module Identity = RI.Identity source-store source-store (‵ `ℕ)
  Codes.Code Codes.denote Codes.imprecise-denote

target-scope : PhysicalScope source-store 2
target-scope = allocate (allocate root (‵ `ℕ)) (＇ Fin.zero)

nested-code : Codes.Code root target-scope
nested-code = Codes.fresh (Codes.fresh Codes.base)

nested-source-type : Model.impreciseTy (Codes.denote nested-code) ≡ ‵ `ℕ
nested-source-type = refl

nested-target-type :
  Identity.U.RightFamily.argumentᴾ Identity.F.family nested-code ≡ ＇ new-name
nested-target-type = refl

nested-values-related : ∀ n k
  → Model.related (Codes.denote nested-code) root root k
      (source-natural n) (doubly-sealed n)
nested-values-related n k = Codes.fresh-related
  (Codes.fresh (Codes.base {S = root} {T = root})) {k = k}
  (Codes.fresh-related (Codes.base {S = root} {T = root})
    {k = k} (same-natural n))

grown-source : PhysicalScope source-store 1
grown-source = allocate root (‵ `ℕ)

grown-target : PhysicalScope source-store 3
grown-target = allocate target-scope (‵ `ℕ)

grown-code : Codes.Code grown-source grown-target
grown-code = Codes.future-code (grow stay) (grow stay) nested-code

grown-values-related : ∀ n k
  → Model.related (Codes.denote grown-code) root root k
      (⇑ᵗᵐ (source-natural n)) (⇑ᵗᵐ (doubly-sealed n))
grown-values-related n k = Codes.future-related
  {S′ = grown-source} {T′ = grown-target} (grow stay) (grow stay)
  nested-code {k = k} (nested-values-related n k)

identity-instantiated : ∀ k
  → Model.ObservedComputations source-store target-store
      (Identity.U.RightFamily.result Identity.F.family nested-code)
      root root k (ƛ (` 0)) instantiated-identity
identity-instantiated k = Identity.U.RightUniversalValues.instantiate
  (Identity.related k) stay (grow (grow stay)) ≤-refl nested-code

-- The family tested at a fresh code is precisely the abstract body needed
-- by the canonical fresh-body compatibility theorem, not its public body.

module FreshResult {Δᴵ Δᴾ} {S : PhysicalScope source-store Δᴵ}
    {T : PhysicalScope source-store Δᴾ} (a : Codes.Code S T) where

  module G = Fresh.Fresh (RI.emptyEnvironment (scopeStore S) (scopeStore T))
    (Codes.denote a)
  module New = Interpretation (scopeStore S)
    (store-bind (scopeStore T) (Model.preciseTy (Codes.denote a)))
  module Eq = Equivalence (scopeStore S)
    (store-bind (scopeStore T) (Model.preciseTy (Codes.denote a)))

  coherent : Eq.Equivalent
    (Identity.U.RightFamily.result Identity.F.family (Codes.fresh a))
    (New.interpret-body RI.identity-body G.extended-meaning)
  coherent = Eq.arrow-cong (Codes.fresh-denotation a)
    (Codes.fresh-denotation a)
