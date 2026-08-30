module proof.LR-narrow.ScopedBodyConversion where

-- File Charter:
--   * Compiles typed reveal/conceal conversions through BodyFragment.
--   * A variable either retains its semantic meaning or exchanges a nominal
--     slot for its stored representation. No compatibility premise is stored.
--   * Both directions reverse the domain conversion at arrows.
--   * ScopedBodyCompatibility proves the operational meaning of these terms.

open import Types
open import TyStore
open import Conversion
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedBodyInterpretation
  using (BodyFragment; natural-body; variable-body; arrow-body)
import proof.LR-narrow.ScopedBodyInterpretation as BI

module Conversions {Δᴵ Δᴾ} (Σᴵ : TyStore Δᴵ) (Σᴾ : TyStore Δᴾ) where

  open Model Σᴵ Σᴾ
  module I = BI.Interpretation Σᴵ Σᴾ
  open I using (interpret-body)

  data VariableConversion : Set₁ where
    unchanged : ScopedType → VariableConversion
    slot : (A : ScopedType) (X : TyVar Δᴵ) (Y : TyVar Δᴾ)
      → Σᴵ ∋ X ⦂ impreciseTy A → Σᴾ ∋ Y ⦂ preciseTy A
      → VariableConversion

  abstract-type : VariableConversion → ScopedType
  abstract-type (unchanged A) = A
  abstract-type (slot A X Y p q) = nominal A X Y p q

  public-type : VariableConversion → ScopedType
  public-type (unchanged A) = A
  public-type (slot A X Y p q) = A

  mutual

    revealᴵ : ∀ {n C} (p : BodyFragment C) (η : TyVar n → VariableConversion)
      → Conv↑ Δᴵ (impreciseTy (interpret-body p (λ X → abstract-type (η X))))
          (impreciseTy (interpret-body p (λ X → public-type (η X))))
    revealᴵ natural-body η = id↑ (‵ `ℕ)
    revealᴵ (variable-body {X}) η with η X
    revealᴵ variable-body η | unchanged A = id↑ (impreciseTy A)
    revealᴵ variable-body η | slot A X Y p q = unseal X (impreciseTy A)
    revealᴵ (arrow-body p q) η = concealᴵ p η ↦↑ revealᴵ q η

    concealᴵ : ∀ {n C} (p : BodyFragment C) (η : TyVar n → VariableConversion)
      → Conv↓ Δᴵ (impreciseTy (interpret-body p (λ X → public-type (η X))))
          (impreciseTy (interpret-body p (λ X → abstract-type (η X))))
    concealᴵ natural-body η = id↓ (‵ `ℕ)
    concealᴵ (variable-body {X}) η with η X
    concealᴵ variable-body η | unchanged A = id↓ (impreciseTy A)
    concealᴵ variable-body η | slot A X Y p q = seal X (impreciseTy A)
    concealᴵ (arrow-body p q) η = revealᴵ p η ↦↓ concealᴵ q η

    revealᴾ : ∀ {n C} (p : BodyFragment C) (η : TyVar n → VariableConversion)
      → Conv↑ Δᴾ (preciseTy (interpret-body p (λ X → abstract-type (η X))))
          (preciseTy (interpret-body p (λ X → public-type (η X))))
    revealᴾ natural-body η = id↑ (‵ `ℕ)
    revealᴾ (variable-body {X}) η with η X
    revealᴾ variable-body η | unchanged A = id↑ (preciseTy A)
    revealᴾ variable-body η | slot A X Y p q = unseal Y (preciseTy A)
    revealᴾ (arrow-body p q) η = concealᴾ p η ↦↑ revealᴾ q η

    concealᴾ : ∀ {n C} (p : BodyFragment C) (η : TyVar n → VariableConversion)
      → Conv↓ Δᴾ (preciseTy (interpret-body p (λ X → public-type (η X))))
          (preciseTy (interpret-body p (λ X → abstract-type (η X))))
    concealᴾ natural-body η = id↓ (‵ `ℕ)
    concealᴾ (variable-body {X}) η with η X
    concealᴾ variable-body η | unchanged A = id↓ (preciseTy A)
    concealᴾ variable-body η | slot A X Y p q = seal Y (preciseTy A)
    concealᴾ (arrow-body p q) η = revealᴾ p η ↦↓ concealᴾ q η

  mutual

    revealᴵ-typed : ∀ {n C} (p : BodyFragment C)
        (η : TyVar n → VariableConversion) → Σᴵ ⊢↑ revealᴵ p η
    revealᴵ-typed natural-body η = ⊢↑-id
    revealᴵ-typed (variable-body {X}) η with η X
    revealᴵ-typed variable-body η | unchanged A = ⊢↑-id
    revealᴵ-typed variable-body η | slot A X Y p q = ⊢↑-unseal p
    revealᴵ-typed (arrow-body p q) η =
      ⊢↑-⇒ (concealᴵ-typed p η) (revealᴵ-typed q η)

    concealᴵ-typed : ∀ {n C} (p : BodyFragment C)
        (η : TyVar n → VariableConversion) → Σᴵ ⊢↓ concealᴵ p η
    concealᴵ-typed natural-body η = ⊢↓-id
    concealᴵ-typed (variable-body {X}) η with η X
    concealᴵ-typed variable-body η | unchanged A = ⊢↓-id
    concealᴵ-typed variable-body η | slot A X Y p q = ⊢↓-seal p
    concealᴵ-typed (arrow-body p q) η =
      ⊢↓-⇒ (revealᴵ-typed p η) (concealᴵ-typed q η)

    revealᴾ-typed : ∀ {n C} (p : BodyFragment C)
        (η : TyVar n → VariableConversion) → Σᴾ ⊢↑ revealᴾ p η
    revealᴾ-typed natural-body η = ⊢↑-id
    revealᴾ-typed (variable-body {X}) η with η X
    revealᴾ-typed variable-body η | unchanged A = ⊢↑-id
    revealᴾ-typed variable-body η | slot A X Y p q = ⊢↑-unseal q
    revealᴾ-typed (arrow-body p q) η =
      ⊢↑-⇒ (concealᴾ-typed p η) (revealᴾ-typed q η)

    concealᴾ-typed : ∀ {n C} (p : BodyFragment C)
        (η : TyVar n → VariableConversion) → Σᴾ ⊢↓ concealᴾ p η
    concealᴾ-typed natural-body η = ⊢↓-id
    concealᴾ-typed (variable-body {X}) η with η X
    concealᴾ-typed variable-body η | unchanged A = ⊢↓-id
    concealᴾ-typed variable-body η | slot A X Y p q = ⊢↓-seal q
    concealᴾ-typed (arrow-body p q) η =
      ⊢↓-⇒ (revealᴾ-typed p η) (concealᴾ-typed q η)
