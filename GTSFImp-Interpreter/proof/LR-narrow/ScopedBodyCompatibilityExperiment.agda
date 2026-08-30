module proof.LR-narrow.ScopedBodyCompatibilityExperiment where

-- File Charter:
--   * Concrete regression for scoped body reveal/conceal compatibility.
--   * Uses one stored natural slot to compile a higher-order body-local
--     conversion and checks that it matches the existing runtime generator.
--   * Exercises both function-conversion directions by revealing the
--     higher-order identity, applying it to the ordinary identity, and
--     then to a natural constant.
--   * Checks both semantic conversion directions and application after an
--     allocating argument, without changing the live logical relation.

open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (≤-refl)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import TermCtx using (Z)
open import Primitives using (κℕ)
open import CastTerms
open import Conversion using (unseal; seal; 〖_,_↑_〗; makeConceal)
open import Reduction
import Eval as E
open import Interpreter
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedIdentity as SI
open import proof.LR-narrow.ScopedApplication using
  (module Applications)
open import proof.LR-narrow.ScopedBodyInterpretation
  using (BodyFragment; variable-body; arrow-body)
import proof.LR-narrow.ScopedBodyInterpretation as BI
import proof.LR-narrow.ScopedBodyConversion as BC
import proof.LR-narrow.ScopedBodyCompatibility as Compat
import proof.LR-narrow.ScopedUniversalExperiment as SU

initial : TyStore 1
initial = store-bind store-empty (‵ `ℕ)

module B = Model initial initial
module I = BI.Interpretation initial initial
module C = BC.Conversions initial initial
module K = Compat.Compatibility initial initial
module EmptyApp = Applications store-empty store-empty

inner-body : BodyFragment {n = 1} (＇ Fin.zero ⇒ ＇ Fin.zero)
inner-body = arrow-body variable-body variable-body

fixture-body : BodyFragment {n = 1}
  ((＇ Fin.zero ⇒ ＇ Fin.zero) ⇒ (＇ Fin.zero ⇒ ＇ Fin.zero))
fixture-body = arrow-body inner-body inner-body

abstractFixtureTy : Ty 1
abstractFixtureTy = (＇ Fin.zero ⇒ ＇ Fin.zero) ⇒ (＇ Fin.zero ⇒ ＇ Fin.zero)

publicFixtureTy : Ty 1
publicFixtureTy = (‵ `ℕ ⇒ ‵ `ℕ) ⇒ (‵ `ℕ ⇒ ‵ `ℕ)

η : TyVar 1 → C.VariableConversion
η Fin.zero = C.slot B.natural Fin.zero Fin.zero (Z∋ refl) (Z∋ refl)

compiled-reveal-is-generated : C.revealᴵ fixture-body η
  ≡ 〖 Fin.zero , ‵ `ℕ ↑ abstractFixtureTy 〗
compiled-reveal-is-generated = refl

compiled-conceal-is-generated : C.concealᴵ fixture-body η
  ≡ makeConceal Fin.zero (‵ `ℕ) abstractFixtureTy
compiled-conceal-is-generated = refl

revealed-higher-order-identityᴵ : Term 1
revealed-higher-order-identityᴵ = (ƛ (` zero)) ↑ C.revealᴵ fixture-body η

revealed-higher-order-identityᴾ : Term 1
revealed-higher-order-identityᴾ = (ƛ (` zero)) ↑ C.revealᴾ fixture-body η

ordinary-identity : ∀ {Δ} → Term Δ
ordinary-identity = ƛ (` zero)

ordinary-identity-value : ∀ {Δ} → Value (ordinary-identity {Δ})
ordinary-identity-value = ƛ (` zero)

ordinary-identity-⊢ : ∀ {Δ} {Σ : TyStore Δ}
  → ⟨ Δ , Σ , [] ⟩ ⊢ ordinary-identity ⦂ (‵ `ℕ ⇒ ‵ `ℕ)
ordinary-identity-⊢ = ⊢ƛ (⊢` Z)

revealed-higher-order-identityᴵ-⊢ : ⟨ 1 , initial , [] ⟩
  ⊢ revealed-higher-order-identityᴵ ⦂ publicFixtureTy
revealed-higher-order-identityᴵ-⊢ =
  ⊢reveal (C.revealᴵ-typed fixture-body η) (⊢ƛ (⊢` Z))

revealed-higher-order-identityᴾ-⊢ : ⟨ 1 , initial , [] ⟩
  ⊢ revealed-higher-order-identityᴾ ⦂ publicFixtureTy
revealed-higher-order-identityᴾ-⊢ =
  ⊢reveal (C.revealᴾ-typed fixture-body η) (⊢ƛ (⊢` Z))

revealed-higher-order-identity-observed : ∀ k
  → B.ObservedComputations
      (I.interpret-body fixture-body (λ X → C.public-type (η X)))
      root root k
      revealed-higher-order-identityᴵ
      revealed-higher-order-identityᴾ
revealed-higher-order-identity-observed k = K.reveal-values fixture-body η
  (SI.identity-related
    (I.interpret-body inner-body (λ X → C.abstract-type (η X))) k)

concealed-higher-order-identity-observed : ∀ k
  → B.ObservedComputations
      (I.interpret-body fixture-body (λ X → C.abstract-type (η X)))
      root root k
      ((ƛ (` zero)) ↓ C.concealᴵ fixture-body η)
      ((ƛ (` zero)) ↓ C.concealᴾ fixture-body η)
concealed-higher-order-identity-observed k = K.conceal-values fixture-body η
  (SI.identity-related
    (I.interpret-body inner-body (λ X → C.public-type (η X))) k)

observe : ℕ → Term 1
observe n = (revealed-higher-order-identityᴵ · ordinary-identity) · $ (κℕ n)

observe-⊢ : ∀ n → ⟨ 1 , initial , [] ⟩ ⊢ observe n ⦂ ‵ `ℕ
observe-⊢ n = ⊢·
  (⊢· revealed-higher-order-identityᴵ-⊢ ordinary-identity-⊢)
  (⊢$ (κℕ n))

observe-↠ : ∀ n → observe n
  —↠[ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ]
  $ (κℕ n)
observe-↠ n =
    (revealed-higher-order-identityᴵ · ordinary-identity) · $ (κℕ n)
  —→[ keep ]⟨ ξ-·₁
      (pure-step (β-reveal-⇒ (ƛ (` zero)) ordinary-identity-value)) refl ⟩
    ((((ƛ (` zero)) · (ordinary-identity ↓ C.concealᴵ inner-body η))
        ↑ C.revealᴵ inner-body η) · $ (κℕ n))
  —→[ keep ]⟨ ξ-·₁
      (ξ-reveal (pure-step (β (ordinary-identity-value ↓ fun))) refl) refl ⟩
    (((ordinary-identity ↓ C.concealᴵ inner-body η)
        ↑ C.revealᴵ inner-body η) · $ (κℕ n))
  —→[ keep ]⟨ pure-step (β-reveal-⇒
      (ordinary-identity-value ↓ fun) ($ (κℕ n))) ⟩
    (((ordinary-identity ↓ C.concealᴵ inner-body η)
        · ($ (κℕ n) ↓ seal Fin.zero (‵ `ℕ)))
        ↑ unseal Fin.zero (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (pure-step (β-conceal-⇒ ordinary-identity-value
        (($ (κℕ n)) ↓ seal))) refl ⟩
    (((ordinary-identity · (($ (κℕ n) ↓ seal Fin.zero (‵ `ℕ))
        ↑ unseal Fin.zero (‵ `ℕ)))
        ↓ seal Fin.zero (‵ `ℕ)) ↑ unseal Fin.zero (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (ξ-conceal (ξ-·₂ ordinary-identity-value
        (pure-step (conceal-reveal ($ (κℕ n)))) refl) refl) refl ⟩
    (((ordinary-identity · $ (κℕ n)) ↓ seal Fin.zero (‵ `ℕ))
      ↑ unseal Fin.zero (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (ξ-conceal (pure-step (β ($ (κℕ n)))) refl) refl ⟩
    (($ (κℕ n) ↓ seal Fin.zero (‵ `ℕ)) ↑ unseal Fin.zero (‵ `ℕ))
  —→[ keep ]⟨ pure-step (conceal-reveal ($ (κℕ n))) ⟩
    $ (κℕ n) ∎[]

observe-result : ∀ n → E.EvalResult (observe n)
observe-result n = E.result 1
  (keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [])
  ($ (κℕ n)) (observe-↠ n) ($ (κℕ n))

observe-eval : ∀ n
  → interpretFrom initial 7 (observe n) ≡ returned (observe-result n)
observe-eval n = refl

observeᴾ-⊢ : ∀ n → ⟨ 1 , initial , [] ⟩
  ⊢ (revealed-higher-order-identityᴾ · ordinary-identity) · $ (κℕ n)
  ⦂ ‵ `ℕ
observeᴾ-⊢ n = ⊢·
  (⊢· revealed-higher-order-identityᴾ-⊢ ordinary-identity-⊢)
  (⊢$ (κℕ n))

observeᴾ-↠ : ∀ n
  → (revealed-higher-order-identityᴾ · ordinary-identity) · $ (κℕ n)
      —↠[ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ]
      $ (κℕ n)
observeᴾ-↠ n =
    (revealed-higher-order-identityᴾ · ordinary-identity) · $ (κℕ n)
  —↠[ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ]⟨
      observe-↠ n ⟩
    $ (κℕ n) ∎[]

observeᴾ-eval : ∀ n
  → interpretFrom initial 7
      ((revealed-higher-order-identityᴾ · ordinary-identity) · $ (κℕ n))
      ≡ returned (observe-result n)
observeᴾ-eval n = refl

right-instantiation-observed : ∀ (R : Ty 0) n k
  → SU.Empty.ObservedComputations SU.Empty.natural root root k
      (ordinary-identity · $ (κℕ n))
      (ordinary-identity · (SU.wrapped-constant n ⦂∀ (‵ `ℕ) [ R ]))
right-instantiation-observed R n k = EmptyApp.application-observed
  SU.Empty.natural SU.Empty.natural {j = k} {k = suc k} ≤-refl
  (SI.identity-related SU.Empty.natural (suc k))
  (SU.right-at-same-index R n k)
