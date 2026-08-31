module proof.LR-narrow.FreshInstantiationObstruction where

-- File Charter:
--   * Mechanizes the fixed-root endpoint obstruction for fresh
--     instantiation types in the integrated experiment.
--   * Shows that no closed root type can scope to the freshly allocated
--     variable, or to the result type `＇0 ⇒ ★` produced by
--     `payload-body [ ＇0 ]ᵗ` after allocating `X↦ℕ`.
--   * This blocks merely broadening the Nat-only universal argument while
--     retaining root-fixed `SemanticType` endpoints. It does not refute the
--     integrated A+B+C′ architecture.

import Data.Fin as Fin
open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import Reduction
open import Primitives using (κℕ)
open import Interpreter
import Eval as E
open import Consistency using (instᵐ; idᶜ; X∼★ᵍ)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.IntegratedModel
open import proof.LR-narrow.IntegratedUniversalSteps
  using (producer-function; producer-function-⊢)
open import proof.LR-narrow.IntegratedProducerSteps
  using (payload-body; inject-function; inject-function-value)

open Model store-empty store-empty

fresh-source : PhysicalScope store-empty 1
fresh-source = allocate root (‵ `ℕ)

arrow-domain-injective : ∀ {Δ} {A A′ B B′ : Ty Δ}
  → A ⇒ B ≡ A′ ⇒ B′ → A ≡ A′
arrow-domain-injective refl = refl

no-closed-root-type-scopes-to-fresh-variable : ∀ (A : Ty 0)
  → scopeTy fresh-source A ≡ ＇ Fin.zero → ⊥
no-closed-root-type-scopes-to-fresh-variable (＇ ()) eq
no-closed-root-type-scopes-to-fresh-variable (‵ x) ()
no-closed-root-type-scopes-to-fresh-variable ★ ()
no-closed-root-type-scopes-to-fresh-variable (A ⇒ B) ()
no-closed-root-type-scopes-to-fresh-variable (`∀ A) ()

no-closed-root-type-scopes-to-fresh-payload-result : ∀ (B : Ty 0)
  → scopeTy fresh-source B ≡ payload-body [ ＇ Fin.zero ]ᵗ → ⊥
no-closed-root-type-scopes-to-fresh-payload-result (＇ ()) eq
no-closed-root-type-scopes-to-fresh-payload-result (‵ x) ()
no-closed-root-type-scopes-to-fresh-payload-result ★ ()
no-closed-root-type-scopes-to-fresh-payload-result (B ⇒ C) eq
    rewrite scope-arrow fresh-source B C =
  no-closed-root-type-scopes-to-fresh-variable B
    (arrow-domain-injective eq)
no-closed-root-type-scopes-to-fresh-payload-result (`∀ B) ()

no-root-fixed-semantic-source-endpoint-for-fresh-payload-result :
  ∀ (A : SemanticType)
  → scopeTy fresh-source (impreciseTy A)
      ≡ payload-body [ ＇ Fin.zero ]ᵗ → ⊥
no-root-fixed-semantic-source-endpoint-for-fresh-payload-result A =
  no-closed-root-type-scopes-to-fresh-payload-result (impreciseTy A)

-- The obstructed type is not ill-formed. It is exactly the ordinary future
-- source type obtained by instantiating the concrete dynamic-payload
-- producer at the freshly allocated name `X`.

fresh-producer-instantiation : Term (suc zero)
fresh-producer-instantiation =
  producer-function (X∼★ᵍ {μ = instᵐ (idᶜ {1})} refl)
    ⦂∀ payload-body [ ＇ Fin.zero ]

fresh-producer-instantiation-⊢ :
  ⟨ 1 , scopeStore fresh-source , [] ⟩
    ⊢ fresh-producer-instantiation ⦂ payload-body [ ＇ Fin.zero ]ᵗ
fresh-producer-instantiation-⊢ = ⊢• producer-function-⊢

fresh-producer-instantiation-return :
  ∃[ tr ] interpretFrom (scopeStore fresh-source) 1
      fresh-producer-instantiation
    ≡ returned (E.result (suc (suc zero)) (bind (＇ Fin.zero) ∷ [])
      (inject-function Fin.zero (X∼★ᵍ {μ = instᵐ (idᶜ {1})} refl)
        ↑ (seal Fin.zero (＇ (Fin.suc Fin.zero)) ↦↑ id↑ ★))
      tr (inject-function-value ↑ fun))
fresh-producer-instantiation-return = _ , refl

-- A fully-applied data companion: execute F[X] on an X-sealed natural,
-- then consume its dynamic packet. This checks evaluation at the future
-- nominal argument; it does not assert a semantic meaning for X.
fresh-producer-data-example : ℕ → Term (suc zero)
fresh-producer-data-example n =
  (ƛ ($ (κℕ n))) ·
    (fresh-producer-instantiation · ($ (κℕ n) ↓ seal Fin.zero (‵ `ℕ)))

fresh-producer-data-example-⊢ : ∀ n
  → ⟨ 1 , scopeStore fresh-source , [] ⟩
      ⊢ fresh-producer-data-example n ⦂ ‵ `ℕ
fresh-producer-data-example-⊢ n =
  ⊢· (⊢ƛ (⊢$ (κℕ n)))
    (⊢· fresh-producer-instantiation-⊢
      (⊢conceal (⊢↓-seal (Z∋ refl)) (⊢$ (κℕ n))))

fresh-producer-data-example-return : ∀ n
  → ∃[ tr ] interpretFrom (scopeStore fresh-source) 5
      (fresh-producer-data-example n)
      ≡ returned (E.result (suc (suc zero))
        (bind (＇ Fin.zero) ∷ keep ∷ keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ n)) tr ($ (κℕ n)))
fresh-producer-data-example-return n = _ , refl
