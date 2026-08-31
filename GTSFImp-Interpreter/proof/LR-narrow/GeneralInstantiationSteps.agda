module proof.LR-narrow.GeneralInstantiationSteps where

-- File Charter:
--   * General operational β-instantiation prefixes for the integrated
--     dynamic-payload producer and its identity-universal reveal wrapper.
--   * Works for an arbitrary instantiation type R and exposes the exact
--     returned adapter values, typings, and evaluator equations.
--   * This is operational infrastructure only: no semantic universal
--     membership, live LR, CTI, or evaluator rule is changed.

open import Data.List using (_∷_; [])
open import Data.Nat using (suc)
open import Data.Product using (∃-syntax; _,_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
import Consistency as C
open C using (Env∼; _⊢_∼★)
open import CastTerms
open import Conversion
open import Reduction
open import Interpreter
import Eval as E
open import proof.Consistency as PC using (rename∼★ᵐ)
open import proof.TypeInTermSubst
  using (renameᵗ-id; renameᵗᵐ-preserves-Value)
import proof.LR-narrow.IntegratedProducerSteps as PS
import proof.LR-narrow.IntegratedUniversalSteps as US
open PS using (payload-body)

instantiated-function : ∀ {Δ} (R : Ty Δ) {μ : Env∼ (suc Δ)}
  → μ ⊢ ＇ Fin.zero ∼★
  → Term (suc Δ)
instantiated-function R gate =
  PS.inject-function Fin.zero gate
    ↑ (seal Fin.zero (⇑ᵗ R) ↦↑ id↑ ★)

instantiated-function-value : ∀ {Δ} {R : Ty Δ}
    {μ : Env∼ (suc Δ)} {gate : μ ⊢ ＇ Fin.zero ∼★}
  → Value (instantiated-function R gate)
instantiated-function-value = PS.inject-function-value ↑ fun

instantiated-function-⊢ : ∀ {Δ} {Σ : TyStore Δ} {R : Ty Δ}
    {μ : Env∼ (suc Δ)} {gate : μ ⊢ ＇ Fin.zero ∼★}
  → ⟨ suc Δ , store-bind Σ R , [] ⟩
      ⊢ instantiated-function R gate ⦂ (⇑ᵗ R ⇒ ★)
instantiated-function-⊢ =
  ⊢reveal (⊢↑-⇒ (⊢↓-seal (Z∋ refl)) ⊢↑-id)
    PS.inject-function-⊢

wrapped-instantiated-function : ∀ {Δ} (R : Ty Δ)
    {μ : Env∼ (suc Δ)}
  → μ ⊢ ＇ Fin.zero ∼★
  → Term (suc (suc Δ))
wrapped-instantiated-function R gate =
  (renameᵗᵐ (C.keep C.wk↪ᵗ) (PS.inject-function Fin.zero gate)
    ↑ (makeConceal Fin.zero (⇑ᵗ (＇ Fin.zero))
        (renameᵗ (extᵗ Fin.suc) (＇ Fin.zero))
      ↦↑ 〖 Fin.zero , ⇑ᵗ (＇ Fin.zero)
             ↑ renameᵗ (extᵗ Fin.suc) ★ 〗))
    ↑ (rename↓ (applyVar keep)
        (rename↓ (applyVar (bind (＇ Fin.zero)))
          (makeConceal Fin.zero (⇑ᵗ R) (＇ Fin.zero)))
      ↦↑ rename↑ (applyVar keep)
        (rename↑ (applyVar (bind (＇ Fin.zero)))
          〖 Fin.zero , ⇑ᵗ R ↑ ★ 〗))

wrapped-instantiated-function-value : ∀ {Δ} {R : Ty Δ}
    {μ : Env∼ (suc Δ)} {gate : μ ⊢ ＇ Fin.zero ∼★}
  → Value (wrapped-instantiated-function R gate)
wrapped-instantiated-function-value =
  (renameᵗᵐ-preserves-Value (C.keep C.wk↪ᵗ)
    PS.inject-function-value ↑ fun) ↑ fun

wrapped-instantiated-function-canonical : ∀ {Δ} {R : Ty Δ}
    {μ : Env∼ (suc Δ)} {gate : μ ⊢ ＇ Fin.zero ∼★}
  → wrapped-instantiated-function R gate
      ≡ ((PS.inject-function (C.toRenameᵗ (C.keep C.wk↪ᵗ) Fin.zero)
            (rename∼★ᵐ (C.keep C.wk↪ᵗ) gate)
          ↑ (seal Fin.zero (＇ (Fin.suc Fin.zero)) ↦↑ id↑ ★))
        ↑ (seal (Fin.suc Fin.zero) (⇑ᵗ (⇑ᵗ R)) ↦↑ id↑ ★))
wrapped-instantiated-function-canonical {R = R} {gate = gate}
    rewrite PS.shift-inject-function {X = Fin.zero} {gate = gate}
          | renameᵗ-id (⇑ᵗ (⇑ᵗ R)) = refl

wrapped-instantiated-function-⊢ : ∀ {Δ} {Σ : TyStore Δ} {R : Ty Δ}
    {μ : Env∼ (suc Δ)} {gate : μ ⊢ ＇ Fin.zero ∼★}
  → ⟨ suc (suc Δ) , store-bind (store-bind Σ R) (＇ Fin.zero) , [] ⟩
      ⊢ wrapped-instantiated-function R gate ⦂ (⇑ᵗ (⇑ᵗ R) ⇒ ★)
wrapped-instantiated-function-⊢ {R = R} {gate = gate}
    rewrite wrapped-instantiated-function-canonical {R = R} {gate = gate} =
  ⊢reveal (⊢↑-⇒ (⊢↓-seal (S-bind∋ (Z∋ refl) refl)) ⊢↑-id)
    (⊢reveal (⊢↑-⇒ (⊢↓-seal (Z∋ refl)) ⊢↑-id)
      PS.inject-function-⊢)

bare-instantiation-return : ∀ {Δ} {Σ : TyStore Δ} {R : Ty Δ}
    {μ : Env∼ (suc Δ)} {gate : μ ⊢ ＇ Fin.zero ∼★}
  → ∃[ tr ]
      interpretFrom Σ 1 (US.producer-function gate ⦂∀ payload-body [ R ])
        ≡ returned (E.result (suc Δ) (bind R ∷ [])
          (instantiated-function R gate) tr instantiated-function-value)
bare-instantiation-return = _ , refl

wrapped-instantiation-return : ∀ {Δ} {Σ : TyStore Δ} {R : Ty Δ}
    {μ : Env∼ (suc Δ)} {gate : μ ⊢ ＇ Fin.zero ∼★}
  → ∃[ tr ]
      interpretFrom Σ 3
        (US.wrapped-producer-function gate ⦂∀ payload-body [ R ])
        ≡ returned (E.result (suc (suc Δ))
          (bind R ∷ bind (＇ Fin.zero) ∷ keep ∷ [])
          (wrapped-instantiated-function R gate) tr
          (wrapped-instantiated-function-value {R = R} {gate = gate}))
wrapped-instantiation-return = _ , refl
