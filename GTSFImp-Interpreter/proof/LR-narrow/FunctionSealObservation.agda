module proof.LR-narrow.FunctionSealObservation where

-- File Charter:
--   * Decomposes observed function-seal returns into abstract-body returns.
--   * Retains the exact physical allocation history and returned payload,
--     including private names in newly created closures.
--   * Accounts for the adapter's two administrative steps in evaluator fuel.
--   * Uses existing evaluator phases and canonical forms; no live LR changes.

open import Data.List using ([])
open import Data.Nat using (ℕ; suc; _+_; _∸_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; +-mono-≤; +-suc; m≤m+n; ∸-monoʳ-≤)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong) renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import Reduction
import Eval as E
open import Interpreter
open import proof.TypeInTermSubst using (renameᵗ-id)
open import proof.TypeSafety.Preservation using (multi-preservation)
open import proof.LR-narrow.Application using
  (value-unique; value-return-exact; _++ˢ_)
open import proof.LR-narrow.FramePhases using (Frame)
open import proof.LR-narrow.RevealFrames using
  (RevealFrm; reveal-frm; revealFrame)
open import proof.LR-narrow.RevealSteps using
  (unseal-step-question; unseal-value-none; reveal-fun-app-step-question)
open import proof.LR-narrow.StepExpansion using
  (pure-step-return-invert; pure-step-return)
open import proof.LR-narrow.FunctionSealRetraction using
  (applyVars; changed-entry)
open import proof.LR-narrow.FunctionSealCompatibility using
  (reveal-function; changed-variable-type; canonical-payload)

private
  unseal-frame : ∀ {Δ Δ′} (χs : StoreChanges Δ Δ′) Y B
    → Frame.transports revealFrame χs (reveal-frm (unseal Y B))
        ≡ reveal-frm (unseal (applyVars χs Y) (χs ▶ᵗ B))
  unseal-frame [] Y B = refl
  unseal-frame (keep ∷ χs) Y B rewrite renameᵗ-id B = unseal-frame χs Y B
  unseal-frame (bind A ∷ χs) Y B = unseal-frame χs (Fin.suc Y) (⇑ᵗ B)

  matching-unseal-return : ∀ {Δ} {Σ : TyStore Δ} {gas} {U : Term Δ}
      {Y B} (vU : Value U)
      {out : E.EvalResult ((U ↓ seal Y B) ↑ unseal Y B)}
    → interpretFrom Σ gas ((U ↓ seal Y B) ↑ unseal Y B) ≡ returned out
    → (1 ≤ gas) × (out ≡ E.result Δ (keep ∷ []) U
        (((U ↓ seal Y B) ↑ unseal Y B)
          —→[ keep ]⟨ pure-step (conceal-reveal vU) ⟩ U ∎[]) vU)
  matching-unseal-return {Σ = Σ} {Y = Y} {B} vU returnedU
      with unseal-step-question {Σ = Σ} Y B vU
  matching-unseal-return {Σ = Σ} {Y = Y} {B} vU returnedU
      | vU′ , step-eq with value-unique vU′ vU
  matching-unseal-return {Σ = Σ} {gas = gas} {Y = Y} {B} vU returnedU
      | .vU , step-eq | refl
      with pure-step-return-invert {Σ = Σ} {n = gas} (λ ())
        (unseal-value-none Y B vU) (conceal-reveal vU) step-eq returnedU
  matching-unseal-return {Σ = Σ} vU returnedU
      | .vU , step-eq | refl
      | pure-step-return {gas} next next-return refl
      with trans (sym (value-return-exact {Σ = Σ} gas vU)) next-return
  matching-unseal-return vU returnedU
      | .vU , step-eq | refl
      | pure-step-return {gas} ._ next-return refl | refl = s≤s z≤n , refl

  -- Normalize the frame at this boundary only. Forgetting proof witnesses
  -- in this equality avoids transporting the enclosing phase's trace.
  matching-unseal-frame-return : ∀ {Δ} {Σ : TyStore Δ} {gas}
      {U : Term Δ} {Y B} (vU : Value U) (f : RevealFrm Δ)
    → f ≡ reveal-frm (unseal Y B)
    → {out : E.EvalResult (Frame.plug revealFrame f (U ↓ seal Y B))}
    → interpretFrom Σ gas (Frame.plug revealFrame f (U ↓ seal Y B))
        ≡ returned out
    → (1 ≤ gas) ×
        (_≡_ {A = ∃[ Δ′ ] StoreChanges Δ Δ′ × Term Δ′}
          (E.Δ′ out , E.changes out , E.term out) (Δ , keep ∷ [] , U))
  matching-unseal-frame-return {Σ = Σ} {gas = gas} vU ._ refl call-return
      with matching-unseal-return {Σ = Σ} {gas = gas} vU call-return
  matching-unseal-frame-return vU ._ refl call-return
      | positive , refl = positive , refl

-- This statement fixes the body to the OBSERVED final context and payload.
-- Only the last keep is removed from its allocation history. In particular,
-- no syntactic lowering or common raw-store future is required.

unseal-return-invert : ∀ {Δ} {Σ : TyStore Δ} {gas} {M : Term Δ} {Y B}
    {out : E.EvalResult (M ↑ unseal Y B)}
  → Σ ∋ Y ⦂ B → ⟨ Δ , Σ , [] ⟩ ⊢ M ⦂ ＇ Y
  → interpretFrom Σ gas (M ↑ unseal Y B) ≡ returned out
  → ∃[ bodyGas ] ∃[ χs ]
      ∃ λ (bodyTrace : M —↠[ χs ]
        E.term out ↓ seal (applyVars χs Y) (χs ▶ᵗ B)) →
      (interpretFrom Σ bodyGas M ≡ returned
        (E.result (E.Δ′ out) χs
          (E.term out ↓ seal (applyVars χs Y) (χs ▶ᵗ B))
          bodyTrace (E.value out ↓ seal)))
      × (bodyGas + 1 ≤ gas)
      × (E.changes out ≡ χs ++ˢ (keep ∷ []))
      × (⟨ E.Δ′ out , χs ▶ˢ Σ , [] ⟩ ⊢ E.term out ⦂ χs ▶ᵗ B)
unseal-return-invert {Σ = Σ} {gas = gas} {Y = Y} {B}
    entry typed whole-return
    with Frame.return-phases-of revealFrame {Σ = Σ} {gas = gas}
      (reveal-frm (unseal Y B)) whole-return
unseal-return-invert {Σ = Σ} {Y = Y} {B} entry typed whole-return
    | Frame.return-phases bodyGas (E.result Δ′ χs Z traceZ vZ) body-return
        callGas callResult call-return result-split gas-split
    with canonical-payload (changed-entry χs entry) vZ
      (subst≡ (λ T → ⟨ Δ′ , χs ▶ˢ Σ , [] ⟩ ⊢ Z ⦂ T)
        (changed-variable-type χs Y) (multi-preservation typed traceZ))
unseal-return-invert {Σ = Σ} {Y = Y} {B} entry typed whole-return
    | Frame.return-phases bodyGas (E.result Δ′ χs Z traceZ vZ) body-return
        callGas (E.result Δ″ ψs T traceT vT) call-return result-split gas-split
    | U , vU , typedU , refl
    with matching-unseal-frame-return {Σ = χs ▶ˢ Σ} {gas = callGas} vU
      (Frame.transports revealFrame χs (reveal-frm (unseal Y B)))
      (unseal-frame χs Y B) call-return
unseal-return-invert {Y = Y} {B} entry typed whole-return
    | Frame.return-phases bodyGas (E.result Δ′ χs Z traceZ vZ) body-return
        callGas (E.result Δ″ ψs T traceT vT) call-return result-split gas-split
    | U , vU , typedU , refl | call-positive , refl
    with result-split
unseal-return-invert entry typed whole-return
    | Frame.return-phases bodyGas (E.result Δ′ χs Z traceZ vZ) body-return
        callGas (E.result Δ″ ψs T traceT vT) call-return result-split gas-split
    | U , vU , typedU , refl | call-positive , refl | refl
    rewrite value-unique vZ (vT ↓ seal) =
  bodyGas , χs , traceZ , body-return ,
  subst≡ (λ n → bodyGas + 1 ≤ n) gas-split
    (+-mono-≤ ≤-refl call-positive) , refl , typedU

reveal-function-return-invert : ∀ {Δ} {Σ : TyStore Δ} {gas}
    {F V : Term Δ} {X A Y B}
    {out : E.EvalResult (reveal-function X A Y B F · V)}
  → Σ ∋ X ⦂ A → Σ ∋ Y ⦂ B → Value F → Value V
  → ⟨ Δ , Σ , [] ⟩ ⊢ F ⦂ (＇ X ⇒ ＇ Y)
  → ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ A
  → interpretFrom Σ gas (reveal-function X A Y B F · V) ≡ returned out
  → ∃[ bodyGas ] ∃[ χs ]
      ∃ λ (bodyTrace : F · (V ↓ seal X A) —↠[ χs ]
        E.term out ↓ seal (applyVars χs Y) (χs ▶ᵗ B)) →
      (interpretFrom Σ bodyGas (F · (V ↓ seal X A)) ≡ returned
        (E.result (E.Δ′ out) χs
          (E.term out ↓ seal (applyVars χs Y) (χs ▶ᵗ B))
          bodyTrace (E.value out ↓ seal)))
      × (bodyGas + 2 ≤ gas)
      × (E.changes out ≡ keep ∷ (χs ++ˢ (keep ∷ [])))
      × (⟨ E.Δ′ out , χs ▶ˢ Σ , [] ⟩ ⊢ E.term out ⦂ χs ▶ᵗ B)
reveal-function-return-invert {Σ = Σ} {X = X} {A} {Y} {B}
    entryX entryY vF vV typedF typedV whole-return
    with reveal-fun-app-step-question {Σ = Σ} (seal X A) (unseal Y B) vF vV
reveal-function-return-invert {Σ = Σ} {gas = gas}
    entryX entryY vF vV typedF typedV whole-return | vF′ , vV′ , step-eq
    with pure-step-return-invert {Σ = Σ} {n = gas} (λ ()) refl
      (β-reveal-⇒ vF′ vV′) step-eq whole-return
reveal-function-return-invert {Σ = Σ}
    entryX entryY vF vV typedF typedV whole-return | vF′ , vV′ , step-eq
    | pure-step-return {gas} next next-return refl
    with unseal-return-invert {Σ = Σ} {gas = gas} entryY
      (⊢· typedF (⊢conceal (⊢↓-seal entryX) typedV)) next-return
reveal-function-return-invert
    entryX entryY vF vV typedF typedV whole-return | vF′ , vV′ , step-eq
    | pure-step-return {gas} next next-return refl
    | bodyGas , χs , bodyTrace , body-return , budget , changes-eq , typedU =
  bodyGas , χs , bodyTrace , body-return ,
  subst≡ (λ n → n ≤ suc gas) (sym (+-suc bodyGas 1)) (s≤s budget) ,
  cong (keep ∷_) changes-eq , typedU

-- The backward observation can feed a smaller body observation to a
-- step-indexed hypothesis, then lower its residual index to the caller's.

function-seal-body-budget : ∀ {bodyGas wholeGas k}
  → bodyGas + 2 ≤ wholeGas → wholeGas < k
  → (bodyGas < k) × (k ∸ wholeGas ≤ k ∸ bodyGas)
function-seal-body-budget {bodyGas} {wholeGas} {k} budget observed =
  ≤-trans (s≤s (≤-trans (m≤m+n bodyGas 2) budget)) observed ,
  ∸-monoʳ-≤ k (≤-trans (m≤m+n bodyGas 2) budget)
