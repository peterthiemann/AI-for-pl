module proof.LR-narrow.ScopedRightBodyConversion where

-- File Charter:
--   * Compiles precise-only reveal/conceal conversions through BodyFragment.
--   * Variables keep their meaning or exchange a precise nominal slot for
--     its stored representation. The imprecise endpoint never changes.
--   * Arrows reverse the domain conversion; only target syntax is compiled.
--   * Stores contain the slots already; no allocation or semantic
--     compatibility assumption is hidden in the variable descriptions.

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

open import Types
open import TyStore
open import Conversion
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedRightNominal
open import proof.LR-narrow.ScopedBodyInterpretation
  using (BodyFragment; natural-body; variable-body; arrow-body)
import proof.LR-narrow.ScopedBodyInterpretation as BI

module Conversions {Δᴵ Δᴾ} (Σᴵ : TyStore Δᴵ) (Σᴾ : TyStore Δᴾ) where

  open Model Σᴵ Σᴾ
  open Nominals Σᴵ Σᴾ
  private
    module I = BI.Interpretation Σᴵ Σᴾ
  open I using (interpret-body)

  data RightVariableConversion : Set₁ where
    unchanged : ScopedType → RightVariableConversion
    right-slot : (A : ScopedType) (Y : TyVar Δᴾ)
      → Σᴾ ∋ Y ⦂ preciseTy A → RightVariableConversion

  abstract-type : RightVariableConversion → ScopedType
  abstract-type (unchanged A) = A
  abstract-type (right-slot A Y entryY) = right-nominal A Y entryY

  public-type : RightVariableConversion → ScopedType
  public-type (unchanged A) = A
  public-type (right-slot A Y entryY) = A

  private
    imprecise-variable : ∀ c
      → impreciseTy (abstract-type c) ≡ impreciseTy (public-type c)
    imprecise-variable (unchanged A) = refl
    imprecise-variable (right-slot A Y entryY) = refl

  imprecise-body : ∀ {n C} (p : BodyFragment C)
      (η : TyVar n → RightVariableConversion)
    → impreciseTy (interpret-body p (λ X → abstract-type (η X)))
      ≡ impreciseTy (interpret-body p (λ X → public-type (η X)))
  imprecise-body natural-body η = refl
  imprecise-body (variable-body {X}) η = imprecise-variable (η X)
  imprecise-body (arrow-body p q) η =
    cong₂ _⇒_ (imprecise-body p η) (imprecise-body q η)

  mutual

    revealᴾ : ∀ {n C} (p : BodyFragment C)
        (η : TyVar n → RightVariableConversion)
      → Conv↑ Δᴾ (preciseTy (interpret-body p (λ X → abstract-type (η X))))
          (preciseTy (interpret-body p (λ X → public-type (η X))))
    revealᴾ natural-body η = id↑ (‵ `ℕ)
    revealᴾ (variable-body {X}) η with η X
    revealᴾ variable-body η | unchanged A = id↑ (preciseTy A)
    revealᴾ variable-body η | right-slot A Y entryY = unseal Y (preciseTy A)
    revealᴾ (arrow-body p q) η = concealᴾ p η ↦↑ revealᴾ q η

    concealᴾ : ∀ {n C} (p : BodyFragment C)
        (η : TyVar n → RightVariableConversion)
      → Conv↓ Δᴾ (preciseTy (interpret-body p (λ X → public-type (η X))))
          (preciseTy (interpret-body p (λ X → abstract-type (η X))))
    concealᴾ natural-body η = id↓ (‵ `ℕ)
    concealᴾ (variable-body {X}) η with η X
    concealᴾ variable-body η | unchanged A = id↓ (preciseTy A)
    concealᴾ variable-body η | right-slot A Y entryY = seal Y (preciseTy A)
    concealᴾ (arrow-body p q) η = revealᴾ p η ↦↓ concealᴾ q η

  mutual

    revealᴾ-typed : ∀ {n C} (p : BodyFragment C)
        (η : TyVar n → RightVariableConversion) → Σᴾ ⊢↑ revealᴾ p η
    revealᴾ-typed natural-body η = ⊢↑-id
    revealᴾ-typed (variable-body {X}) η with η X
    revealᴾ-typed variable-body η | unchanged A = ⊢↑-id
    revealᴾ-typed variable-body η | right-slot A Y entryY = ⊢↑-unseal entryY
    revealᴾ-typed (arrow-body p q) η =
      ⊢↑-⇒ (concealᴾ-typed p η) (revealᴾ-typed q η)

    concealᴾ-typed : ∀ {n C} (p : BodyFragment C)
        (η : TyVar n → RightVariableConversion) → Σᴾ ⊢↓ concealᴾ p η
    concealᴾ-typed natural-body η = ⊢↓-id
    concealᴾ-typed (variable-body {X}) η with η X
    concealᴾ-typed variable-body η | unchanged A = ⊢↓-id
    concealᴾ-typed variable-body η | right-slot A Y entryY = ⊢↓-seal entryY
    concealᴾ-typed (arrow-body p q) η =
      ⊢↓-⇒ (revealᴾ-typed p η) (concealᴾ-typed q η)
