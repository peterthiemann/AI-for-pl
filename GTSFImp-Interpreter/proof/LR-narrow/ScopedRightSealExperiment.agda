module proof.LR-narrow.ScopedRightSealExperiment where

-- File Charter:
--   * Concrete regression for precise-only right sealing at a singleton
--     precise root and an empty imprecise root.
--   * Reuses the allocating wrapped-constant payload to witness a right-only
--     nominal observation, then checks the explicit seal/unseal roundtrip
--     back to a natural constant.
--   * Routes the blame regression through the one-sided right-seal and
--     right-unseal compatibility wrappers and records the exact target run.

open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import Primitives using (κℕ)
open import CastTerms
open import Conversion
open import Reduction
import Eval as E
open import Interpreter
open import LR-narrow.LogicalRelation using (same-natural)
open import proof.LR-narrow.Application using (value-return-exact)
open import proof.LR-narrow.Blame using (blame-now)
open import proof.LR-narrow.FunctionSealRetraction using
  (seal-trace; unseal-trace)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.PrivateSealBehavior using (_—↠[_]⟨_⟩+_)
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedRightNominal using
  (related-right-seal; module Nominals)
import proof.LR-narrow.ScopedRightSealCompatibility as RS
import proof.LR-narrow.ScopedUniversalExperiment as SU

precise-root : TyStore 1
precise-root = store-bind store-empty (‵ `ℕ)

module Mixed = Model store-empty precise-root
module Right = Nominals store-empty precise-root
module K = RS.Compatibility store-empty precise-root

right-payload : ℕ → Term 1
right-payload n = SU.wrapped-constant n ⦂∀ (‵ `ℕ) [ ‵ `ℕ ]

right-payload-⊢ : ∀ n
  → ⟨ 1 , precise-root , [] ⟩ ⊢ right-payload n ⦂ ‵ `ℕ
right-payload-⊢ n = ⊢• (SU.wrapped-constant-⊢ n)

right-payload-↠ : ∀ n → right-payload n
  —↠[ bind (‵ `ℕ) ∷ bind (＇ Fin.zero) ∷ keep ∷ keep ∷ keep ∷ [] ]
  $ (κℕ n)
right-payload-↠ n =
    right-payload n
  —→[ bind (‵ `ℕ) ]⟨ β-reveal-∀ (Λ ($ (κℕ n))) ⟩
    ((SU.constant-polymorphic n ⦂∀ (‵ `ℕ) [ ＇ Fin.zero ])
      ↑ id↑ (‵ `ℕ)) ↑ id↑ (‵ `ℕ)
  —→[ bind (＇ Fin.zero) ]⟨
      ξ-reveal (ξ-reveal (β-Λ ($ (κℕ n))) refl) refl ⟩
    (($ (κℕ n) ↑ id↑ (‵ `ℕ)) ↑ id↑ (‵ `ℕ)) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ ξ-reveal
      (ξ-reveal (pure-step (id-reveal ($ (κℕ n)))) refl) refl ⟩
    ($ (κℕ n) ↑ id↑ (‵ `ℕ)) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ ξ-reveal (pure-step (id-reveal ($ (κℕ n)))) refl ⟩
    $ (κℕ n) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ pure-step (id-reveal ($ (κℕ n))) ⟩
    $ (κℕ n) ∎[]

right-payload-result : ∀ n → E.EvalResult (right-payload n)
right-payload-result n = E.result 3
  (bind (‵ `ℕ) ∷ bind (＇ Fin.zero) ∷ keep ∷ keep ∷ keep ∷ [])
  ($ (κℕ n)) (right-payload-↠ n) ($ (κℕ n))

right-payload-eval : ∀ n
  → interpretFrom precise-root 5 (right-payload n)
      ≡ returned (right-payload-result n)
right-payload-eval n = refl

right-payload-observed : ∀ n k
  → Mixed.ObservedComputations Mixed.natural root root k
      ($ (κℕ n)) (right-payload n)
right-payload-observed n k = Mixed.observed-from-returns
  {gasᴵ = 0} {gasᴾ = 5}
  (value-return-exact {Σ = store-empty} 0 ($ (κℕ n)))
  (right-payload-eval n)
  (same-natural n)

right-sealed : ℕ → Term 1
right-sealed n = right-payload n ↓ seal Fin.zero (‵ `ℕ)

right-sealed-⊢ : ∀ n
  → ⟨ 1 , precise-root , [] ⟩ ⊢ right-sealed n ⦂ ＇ Fin.zero
right-sealed-⊢ n = ⊢conceal (⊢↓-seal (Z∋ refl)) (right-payload-⊢ n)

right-sealed-↠ : ∀ n → right-sealed n
  —↠[ bind (‵ `ℕ) ∷ bind (＇ Fin.zero) ∷ keep ∷ keep ∷ keep ∷ [] ]
  ($ (κℕ n) ↓ seal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ))
right-sealed-↠ n = seal-trace Fin.zero (‵ `ℕ) (right-payload-↠ n)

right-sealed-result : ∀ n → E.EvalResult (right-sealed n)
right-sealed-result n = E.result 3
  (bind (‵ `ℕ) ∷ bind (＇ Fin.zero) ∷ keep ∷ keep ∷ keep ∷ [])
  ($ (κℕ n) ↓ seal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ))
  (right-sealed-↠ n) (($ (κℕ n)) ↓ seal)

right-sealed-eval : ∀ n
  → interpretFrom precise-root 5 (right-sealed n)
      ≡ returned (right-sealed-result n)
right-sealed-eval n = refl

right-sealed-related : ∀ n k
  → Mixed.related (Right.right-nominal Mixed.natural Fin.zero (Z∋ refl))
      root
      (advance root
        (bind (‵ `ℕ) ∷ bind (＇ Fin.zero) ∷ keep ∷ keep ∷ keep ∷ []))
      k
      ($ (κℕ n))
      ($ (κℕ n) ↓ seal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ))
right-sealed-related n k =
  related-right-seal ($ (κℕ n)) (same-natural n)

right-sealed-observed : ∀ n k
  → Mixed.ObservedComputations
      (Right.right-nominal Mixed.natural Fin.zero (Z∋ refl))
      root root k ($ (κℕ n)) (right-sealed n)
right-sealed-observed n k =
  K.observed-right-seal Mixed.natural Fin.zero (Z∋ refl)
    (right-payload-observed n k)

right-roundtrip : ℕ → Term 1
right-roundtrip n = right-sealed n ↑ unseal Fin.zero (‵ `ℕ)

right-roundtrip-⊢ : ∀ n
  → ⟨ 1 , precise-root , [] ⟩ ⊢ right-roundtrip n ⦂ ‵ `ℕ
right-roundtrip-⊢ n = ⊢reveal (⊢↑-unseal (Z∋ refl)) (right-sealed-⊢ n)

right-roundtrip-↠ : ∀ n → right-roundtrip n
  —↠[ bind (‵ `ℕ) ∷ bind (＇ Fin.zero) ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ]
  $ (κℕ n)
right-roundtrip-↠ n =
    right-roundtrip n
  —↠[ bind (‵ `ℕ) ∷ bind (＇ Fin.zero) ∷ keep ∷ keep ∷ keep ∷ [] ]⟨
      unseal-trace Fin.zero (‵ `ℕ)
        (seal-trace Fin.zero (‵ `ℕ) (right-payload-↠ n)) ⟩+
    (($ (κℕ n) ↓ seal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ))
      ↑ unseal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ))
  —→[ keep ]⟨ pure-step (conceal-reveal ($ (κℕ n))) ⟩
    $ (κℕ n) ∎[]

right-roundtrip-result : ∀ n → E.EvalResult (right-roundtrip n)
right-roundtrip-result n = E.result 3
  (bind (‵ `ℕ) ∷ bind (＇ Fin.zero) ∷ keep ∷ keep ∷ keep ∷ keep ∷ [])
  ($ (κℕ n)) (right-roundtrip-↠ n) ($ (κℕ n))

right-roundtrip-eval : ∀ n
  → interpretFrom precise-root 6 (right-roundtrip n)
      ≡ returned (right-roundtrip-result n)
right-roundtrip-eval n = refl

right-roundtrip-observed : ∀ n k
  → Mixed.ObservedComputations Mixed.natural root root k
      ($ (κℕ n)) (right-roundtrip n)
right-roundtrip-observed n k =
  K.observed-right-unseal Mixed.natural Fin.zero (Z∋ refl)
    (right-sealed-observed n k)

right-blame-seed : ∀ k
  → Mixed.ObservedComputations Mixed.natural root root k blame blame
right-blame-seed k = Mixed.observed-from-right-blame {gas = 0}
  (blame-now {Σ = precise-root})

right-sealed-blame : Term 1
right-sealed-blame = blame ↓ seal Fin.zero (‵ `ℕ)

right-sealed-blame-⊢ : ⟨ 1 , precise-root , [] ⟩
  ⊢ right-sealed-blame ⦂ ＇ Fin.zero
right-sealed-blame-⊢ = ⊢conceal (⊢↓-seal (Z∋ refl)) ⊢blame

right-sealed-blame-↠ : right-sealed-blame —↠[ keep ∷ [] ] blame
right-sealed-blame-↠ =
    right-sealed-blame
  —→[ keep ]⟨ pure-step blame-conceal ⟩
    blame ∎[]

right-sealed-blame-eval : interpretFrom precise-root 1 right-sealed-blame
  ≡ blamed (keep ∷ []) (right-sealed-blame-↠)
right-sealed-blame-eval = refl

right-sealed-blame-observed : ∀ k
  → Mixed.ObservedComputations
      (Right.right-nominal Mixed.natural Fin.zero (Z∋ refl))
      root root k blame right-sealed-blame
right-sealed-blame-observed k =
  K.observed-right-seal Mixed.natural Fin.zero (Z∋ refl) (right-blame-seed k)

right-unsealed-blame : Term 1
right-unsealed-blame = right-sealed-blame ↑ unseal Fin.zero (‵ `ℕ)

right-unsealed-blame-⊢ : ⟨ 1 , precise-root , [] ⟩
  ⊢ right-unsealed-blame ⦂ ‵ `ℕ
right-unsealed-blame-⊢ = ⊢reveal (⊢↑-unseal (Z∋ refl)) right-sealed-blame-⊢

right-unsealed-blame-↠ : right-unsealed-blame —↠[ keep ∷ keep ∷ [] ] blame
right-unsealed-blame-↠ =
    right-unsealed-blame
  —→[ keep ]⟨ ξ-reveal (pure-step blame-conceal) refl ⟩
    blame ↑ unseal Fin.zero (‵ `ℕ)
  —→[ keep ]⟨ pure-step blame-reveal ⟩
    blame ∎[]

right-unsealed-blame-eval : interpretFrom precise-root 2 right-unsealed-blame
  ≡ blamed (keep ∷ keep ∷ []) (right-unsealed-blame-↠)
right-unsealed-blame-eval = refl

right-unseal-forward-blame : ∀ k
  → Mixed.ObservedComputations Mixed.natural root root k
      blame right-unsealed-blame
right-unseal-forward-blame k =
  K.observed-right-unseal Mixed.natural Fin.zero (Z∋ refl)
    (right-sealed-blame-observed k)
