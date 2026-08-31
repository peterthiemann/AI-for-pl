module proof.LR-narrow.IntegratedLocalIdentitySteps where

-- File Charter:
--   * Operational identity seal/unseal adapter facts for arbitrary local
--     representation types and arbitrary value arguments.
--   * The adapter is a concrete function reveal around λx.x; applying it
--     performs exactly three keep steps and returns the original argument.
--   * Future lifting preserves the adapter shape with lifted slot and type.
--   * This file only packages operational syntax facts; no semantic LR or
--     calculus rule is changed.

open import Data.List using (_∷_; [])
open import Data.Nat using (suc)
open import Data.Product using (_,_; ∃-syntax)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym) renaming (subst to subst≡)

open import Types
open import TyStore
open import TermCtx using (Z)
open import CastTerms
open import Conversion
open import Reduction
open import Interpreter
import Eval as E
open import Consistency using (wk↪ᵗ)
open import proof.TypeInTermSubst using (toRename-wk-eq; renameᵗ-wk-eq)
open import proof.LR-narrow.PhysicalScope
import proof.LR-narrow.PrivateSealBehavior as PB
open import proof.LR-narrow.ScopedIdentity using (identity-return)
open import proof.LR-narrow.FunctionSealObservation
  using (unseal-return-expand)
open import proof.LR-narrow.RevealSteps using (reveal-fun-app-step-question)
open import proof.LR-narrow.StepExpansion using (pure-step-return-expand)

identity-adapter : ∀ {Δ} → TyVar Δ → Ty Δ → Term Δ
identity-adapter X R = (ƛ (` 0)) ↑ (seal X R ↦↑ unseal X R)

identity-adapter-value : ∀ {Δ} {X : TyVar Δ} {R}
  → Value (identity-adapter X R)
identity-adapter-value = (ƛ (` 0)) ↑ fun

identity-adapter-⊢ : ∀ {Δ} {Σ : TyStore Δ} {X R}
  → Σ ∋ X ⦂ R
  → ⟨ Δ , Σ , [] ⟩ ⊢ identity-adapter X R ⦂ (R ⇒ R)
identity-adapter-⊢ entry =
  ⊢reveal (⊢↑-⇒ (⊢↓-seal entry) (⊢↑-unseal entry))
    (⊢ƛ (⊢` Z))

identity-adapter-call-⊢ : ∀ {Δ} {Σ : TyStore Δ} {X R U}
  → Σ ∋ X ⦂ R
  → ⟨ Δ , Σ , [] ⟩ ⊢ U ⦂ R
  → ⟨ Δ , Σ , [] ⟩ ⊢ identity-adapter X R · U ⦂ R
identity-adapter-call-⊢ entry typedU =
  ⊢· (identity-adapter-⊢ entry) typedU

identity-adapter-↠ : ∀ {Δ} {U : Term Δ} X R
  → Value U
  → identity-adapter X R · U —↠[ keep ∷ keep ∷ keep ∷ [] ] U
identity-adapter-↠ {U = U} X R vU =
    identity-adapter X R · U
  —→[ keep ]⟨ pure-step (β-reveal-⇒ (ƛ (` 0)) vU) ⟩
    ((ƛ (` 0)) · (U ↓ seal X R)) ↑ unseal X R
  —→[ keep ]⟨ PB.reveal-keep-step (unseal X R)
      (pure-step (β (vU ↓ seal))) ⟩
    (U ↓ seal X R) ↑ unseal X R
  —→[ keep ]⟨ pure-step (conceal-reveal vU) ⟩
    U ∎[]

-- Existential traces avoid identifying the evaluator's proof terms with the
-- displayed reduction proof. The actual endpoint and three keeps stay fixed.
identity-adapter-return : ∀ {Δ} {Σ : TyStore Δ} {X R U}
  → (vU : Value U)
  → ∃[ gas ] ∃[ tr ] interpretFrom Σ gas (identity-adapter X R · U)
      ≡ returned (E.result Δ (keep ∷ keep ∷ keep ∷ []) U tr vU)
identity-adapter-return {Σ = Σ} {X} {R} vU
    with identity-return Σ (vU ↓ seal)
identity-adapter-return {Σ = Σ} {X} {R} vU | vSeal , bodyReturn
    with unseal-return-expand {Σ = Σ} {gas = 1} {Y = X} {B = R}
      {χs = keep ∷ []} vU bodyReturn
identity-adapter-return {Σ = Σ} {X} {R} vU | vSeal , bodyReturn
    | bodyGas , bodyTrace , unsealReturn
    with reveal-fun-app-step-question {Σ = Σ}
      (seal X R) (unseal X R) (ƛ (` 0)) vU
identity-adapter-return {Σ = Σ} vU | vSeal , bodyReturn
    | bodyGas , bodyTrace , unsealReturn | vId , vArg , stepEq =
  suc bodyGas , _ , pure-step-return-expand {Σ = Σ} (λ ()) refl
    (β-reveal-⇒ vId vArg) stepEq unsealReturn

lift-identity-adapter : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    (p : ScopeFuture S T) X R
  → liftTerm p (identity-adapter X R)
      ≡ identity-adapter (liftVar p X) (liftTy p R)
lift-identity-adapter stay X R = refl
lift-identity-adapter (grow p) X R
    rewrite toRename-wk-eq X | renameᵗ-wk-eq R =
  lift-identity-adapter p (Fin.suc X) (⇑ᵗ R)

lifted-identity-adapter-⊢ : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    {X : TyVar Δ} {R}
  → (p : ScopeFuture S T)
  → scopeStore S ∋ X ⦂ R
  → ⟨ Δ′ , scopeStore T , [] ⟩ ⊢ liftTerm p (identity-adapter X R)
      ⦂ (liftTy p R ⇒ liftTy p R)
lifted-identity-adapter-⊢ {X = X} {R} p entry =
  subst≡ (λ A → ⟨ _ , _ , [] ⟩
      ⊢ liftTerm p (identity-adapter X R) ⦂ A)
    (lift-ty-arrow p R R)
    (lift-typed p (identity-adapter-⊢ entry))

lifted-identity-adapter-call-⊢ : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    {X : TyVar Δ} {R U}
  → (p : ScopeFuture S T)
  → scopeStore S ∋ X ⦂ R
  → ⟨ Δ′ , scopeStore T , [] ⟩ ⊢ U ⦂ liftTy p R
  → ⟨ Δ′ , scopeStore T , [] ⟩
      ⊢ liftTerm p (identity-adapter X R) · U ⦂ liftTy p R
lifted-identity-adapter-call-⊢ p entry typedU =
  ⊢· (lifted-identity-adapter-⊢ p entry) typedU

lifted-identity-adapter-↠ : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    {X : TyVar Δ} {R U}
  → (p : ScopeFuture S T) → Value U
  → liftTerm p (identity-adapter X R) · U
      —↠[ keep ∷ keep ∷ keep ∷ [] ] U
lifted-identity-adapter-↠ {X = X} {R} p vU
    rewrite lift-identity-adapter p X R =
  identity-adapter-↠ (liftVar p X) (liftTy p R) vU

lifted-identity-adapter-return : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    {X : TyVar Δ} {R U}
  → (p : ScopeFuture S T) → (vU : Value U)
  → ∃[ gas ] ∃[ tr ] interpretFrom (scopeStore T) gas
      (liftTerm p (identity-adapter X R) · U)
      ≡ returned (E.result Δ′ (keep ∷ keep ∷ keep ∷ []) U tr vU)
lifted-identity-adapter-return {T = T} {X = X} {R} p vU
    rewrite lift-identity-adapter p X R =
  identity-adapter-return {Σ = scopeStore T} vU
