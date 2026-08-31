module proof.LR-narrow.IntegratedUniversalSteps where

-- File Charter:
--   * Uniform operational prefixes for the integrated payload universal
--     Λ α. λ x : α. x⟨α!⟩ and its identity-universal reveal wrapper.
--   * Exposes typing, value, and exact natural-instantiation evaluator
--     results that return the reusable adapter functions from
--     IntegratedProducerSteps.
--   * Keeps runtime gates in their actual renamed Env∼ form; no canonical
--     environment equality or semantic universal membership is claimed here.

open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ; suc)
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
open import proof.LR-narrow.PhysicalScope
import proof.LR-narrow.IntegratedProducerSteps as PS
open PS using (payload-body)

producer-function : ∀ {Δ} {μ : Env∼ (suc Δ)}
  → μ ⊢ ＇ Fin.zero ∼★
  → Term Δ
producer-function gate = Λ (PS.inject-function Fin.zero gate)

producer-function-value : ∀ {Δ} {μ : Env∼ (suc Δ)}
    {gate : μ ⊢ ＇ Fin.zero ∼★}
  → Value (producer-function gate)
producer-function-value = Λ PS.inject-function-value

producer-function-⊢ : ∀ {Δ} {Σ : TyStore Δ} {μ : Env∼ (suc Δ)}
    {gate : μ ⊢ ＇ Fin.zero ∼★}
  → ⟨ Δ , Σ , [] ⟩ ⊢ producer-function gate ⦂ `∀ payload-body
producer-function-⊢ =
  ⊢Λ PS.inject-function-value PS.inject-function-⊢

shift-producer-function : ∀ {Δ} {μ : Env∼ (suc Δ)}
    {gate : μ ⊢ ＇ Fin.zero ∼★}
  → ⇑ᵗᵐ (producer-function gate)
      ≡ producer-function (rename∼★ᵐ (C.keep C.wk↪ᵗ) gate)
shift-producer-function = refl

wrapped-producer-function : ∀ {Δ} {μ : Env∼ (suc Δ)}
  → μ ⊢ ＇ Fin.zero ∼★
  → Term Δ
wrapped-producer-function gate =
  producer-function gate ↑ `∀↑ id↑ payload-body

wrapped-producer-function-value : ∀ {Δ} {μ : Env∼ (suc Δ)}
    {gate : μ ⊢ ＇ Fin.zero ∼★}
  → Value (wrapped-producer-function gate)
wrapped-producer-function-value = producer-function-value ↑ all

wrapped-producer-function-⊢ : ∀ {Δ} {Σ : TyStore Δ}
    {μ : Env∼ (suc Δ)} {gate : μ ⊢ ＇ Fin.zero ∼★}
  → ⟨ Δ , Σ , [] ⟩ ⊢ wrapped-producer-function gate
      ⦂ `∀ payload-body
wrapped-producer-function-⊢ =
  ⊢reveal (⊢↑-∀ ⊢↑-id) producer-function-⊢

shift-wrapped-producer-function : ∀ {Δ} {μ : Env∼ (suc Δ)}
    {gate : μ ⊢ ＇ Fin.zero ∼★}
  → ⇑ᵗᵐ (wrapped-producer-function gate)
      ≡ wrapped-producer-function (rename∼★ᵐ (C.keep C.wk↪ᵗ) gate)
shift-wrapped-producer-function = refl

lift-producer-function : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    {μ : Env∼ (suc Δ)} {gate : μ ⊢ ＇ Fin.zero ∼★}
  → (p : ScopeFuture S T)
  → ∃[ μ′ ] ∃[ gate′ ]
      liftTerm p (producer-function gate)
        ≡ producer-function {μ = μ′} gate′
lift-producer-function stay = _ , _ , refl
lift-producer-function {gate = gate} (grow p)
    rewrite shift-producer-function {gate = gate} =
  lift-producer-function p

lift-wrapped-producer-function : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    {μ : Env∼ (suc Δ)} {gate : μ ⊢ ＇ Fin.zero ∼★}
  → (p : ScopeFuture S T)
  → ∃[ μ′ ] ∃[ gate′ ]
      liftTerm p (wrapped-producer-function gate)
        ≡ wrapped-producer-function {μ = μ′} gate′
lift-wrapped-producer-function stay = _ , _ , refl
lift-wrapped-producer-function {gate = gate} (grow p)
    rewrite shift-wrapped-producer-function {gate = gate} =
  lift-wrapped-producer-function p

bare-instantiation-return : ∀ {Δ} {Σ : TyStore Δ}
    {μ : Env∼ (suc Δ)} {gate : μ ⊢ ＇ Fin.zero ∼★}
  → ∃[ tr ]
      interpretFrom Σ 1
        (producer-function gate ⦂∀ payload-body [ ‵ `ℕ ])
        ≡ returned (E.result (suc Δ) (bind (‵ `ℕ) ∷ [])
          (PS.one-adapter-function Fin.zero gate) tr
          PS.one-adapter-function-value)
bare-instantiation-return = _ , refl

wrapped-instantiation-return : ∀ {Δ} {Σ : TyStore Δ}
    {μ : Env∼ (suc Δ)} {gate : μ ⊢ ＇ Fin.zero ∼★}
  → ∃[ tr ]
      interpretFrom Σ 3
        (wrapped-producer-function gate ⦂∀ payload-body [ ‵ `ℕ ])
        ≡ returned (E.result (suc (suc Δ))
          (bind (‵ `ℕ) ∷ bind (＇ Fin.zero) ∷ keep ∷ [])
          (PS.two-adapters-function (Fin.suc Fin.zero) Fin.zero
            (rename∼★ᵐ (C.keep C.wk↪ᵗ) gate))
          tr PS.two-adapters-function-value)
wrapped-instantiation-return = _ , refl
