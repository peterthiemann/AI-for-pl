module proof.LR-narrow.FunctionSealObservationExperiment where

-- File Charter:
--   * Tests backward function-seal observation on the allocating closure body.
--   * Checks actual interpreter returns with arbitrary surplus fuel, then
--     recovers the exact body fuel and allocation history through inversion.
--   * Reuses the fully applied natural observations of the closure experiment.

open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax; proj₁; proj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import Primitives using (κℕ)
open import Reduction
import Eval as E
open import Interpreter
open import proof.LR-narrow.Application using (_++ˢ_)
open import proof.LR-narrow.FunctionSealRetraction using (applyVars)
open import proof.LR-narrow.FunctionSealObservation
open import proof.LR-narrow.FunctionSealClosureExperiment

-- Four steps produce the new closure. Every additional unit is spare;
-- observing a value does not consume it or allocate further names.

private-closure-return : ∀ n spare
  → interpretFrom initial (4 + spare) (public-private · $ (κℕ n))
      ≡ returned (E.result 3
        (keep ∷ keep ∷ bind (‵ `ℕ) ∷ keep ∷ []) (fresh-private n)
        (public-private-↠ n) (fresh-private-value n))
private-closure-return n zero = refl
private-closure-return n (suc spare) = refl

private-return-decomposition : ∀ n spare → ∃[ bodyGas ] ∃[ χs ]
  ∃ λ (bodyTrace :
    make-private · ($ (κℕ n) ↓ seal (Fin.suc Fin.zero) (‵ `ℕ)) —↠[ χs ]
      fresh-private n ↓ seal (applyVars χs Fin.zero) (χs ▶ᵗ (‵ `ℕ ⇒ ‵ `ℕ))) →
  (interpretFrom initial bodyGas
    (make-private · ($ (κℕ n) ↓ seal (Fin.suc Fin.zero) (‵ `ℕ)))
    ≡ returned (E.result 3 χs
      (fresh-private n ↓ seal (applyVars χs Fin.zero) (χs ▶ᵗ (‵ `ℕ ⇒ ‵ `ℕ)))
      bodyTrace (fresh-private-value n ↓ seal)))
  × (bodyGas + 2 ≤ 4 + spare)
  × (keep ∷ keep ∷ bind (‵ `ℕ) ∷ keep ∷ []
      ≡ keep ∷ (χs ++ˢ (keep ∷ [])))
  × (⟨ 3 , χs ▶ˢ initial , [] ⟩
      ⊢ fresh-private n ⦂ χs ▶ᵗ (‵ `ℕ ⇒ ‵ `ℕ))
private-return-decomposition n spare =
  reveal-function-return-invert {Σ = initial} {gas = 4 + spare}
    (S-bind∋ (Z∋ refl) refl) (Z∋ refl)
    make-private-value ($ (κℕ n)) make-private-⊢ (⊢$ (κℕ n))
    (private-closure-return n spare)

-- These equalities test the computed witnesses of the GENERAL inversion
-- proof, rather than supplying a separate hand-picked body derivation.

recovered-body-fuel : ∀ n spare
  → proj₁ (private-return-decomposition n spare) ≡ 2
recovered-body-fuel n zero = refl
recovered-body-fuel n (suc spare) = refl

recovered-body-changes : ∀ n spare
  → proj₁ (proj₂ (private-return-decomposition n spare))
      ≡ keep ∷ bind (‵ `ℕ) ∷ []
recovered-body-changes n zero = refl
recovered-body-changes n (suc spare) = refl

recovered-body-store : ∀ n spare
  → (proj₁ (proj₂ (private-return-decomposition n spare))) ▶ˢ initial
      ≡ physical
recovered-body-store n spare rewrite recovered-body-changes n spare = refl
