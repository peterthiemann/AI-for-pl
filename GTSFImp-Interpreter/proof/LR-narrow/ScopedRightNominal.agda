module proof.LR-narrow.ScopedRightNominal where

-- File Charter:
--   * A precise-only nominal slot relates an unsealed imprecise value to a
--     sealed precise payload. No imprecise slot or lookup is introduced.
--   * Proves value typing, downward closure, independent physical-future
--     closure, and coherence when changing the physical model roots.
--   * This is a proof-local semantic constructor, not a live LR rule.

open import Data.List using ([])
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym) renaming (subst to subst≡; subst₂ to subst₂≡)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopeRebase

data RightSealedValues {Δᴵ Δᴾ} (Y : TyVar Δᴾ) (R : Ty Δᴾ)
    (A : Term Δᴵ → Term Δᴾ → Set) : Term Δᴵ → Term Δᴾ → Set where
  related-right-seal : ∀ {U V} → Value V → A U V
    → RightSealedValues Y R A U (V ↓ seal Y R)

module Nominals {Δᴵ₀ Δᴾ₀} (Σᴵ₀ : TyStore Δᴵ₀)
    (Σᴾ₀ : TyStore Δᴾ₀) where

  open Model Σᴵ₀ Σᴾ₀

  right-nominal : (A : ScopedType) (Y : TyVar Δᴾ₀)
    → Σᴾ₀ ∋ Y ⦂ preciseTy A → ScopedType
  right-nominal A Y entryY = record
    { impreciseTy = impreciseTy A
    ; preciseTy = ＇ Y
    ; related = λ S T k → RightSealedValues
        (scopeVar T Y) (scopeTy T (preciseTy A)) (related A S T k)
    ; imprecise-value = λ { (related-right-seal vV r) → imprecise-value A r }
    ; precise-value = λ { (related-right-seal vV r) → vV ↓ seal }
    ; imprecise-typed = λ { (related-right-seal vV r) → imprecise-typed A r }
    ; precise-typed = λ { {T = T} (related-right-seal {V = V} vV r) →
        subst≡ (λ B → ⟨ _ , scopeStore T , [] ⟩
          ⊢ V ↓ seal (scopeVar T Y) (scopeTy T (preciseTy A)) ⦂ B)
          (sym (scope-variable T Y))
          (⊢conceal (⊢↓-seal (scope-entry T entryY)) (precise-typed A r)) }
    ; downward = λ { j≤k (related-right-seal vV r) →
        related-right-seal vV (downward A j≤k r) }
    ; future-closed = λ { p q (related-right-seal {V = V} vV r) →
        subst₂≡ (RightSealedValues _ _ (related A _ _ _)) refl
          (sym (lift-root-seal q Y (preciseTy A) V))
          (related-right-seal (lift-value q vV) (future-closed A p q r)) }
    }

module RebaseNominals {Δᴵ₀ Δᴾ₀ Δᴵ Δᴾ}
    {Σᴵ₀ : TyStore Δᴵ₀} {Σᴾ₀ : TyStore Δᴾ₀}
    (S : PhysicalScope Σᴵ₀ Δᴵ) (T : PhysicalScope Σᴾ₀ Δᴾ) where

  private
    module R = Rebase S T
    module Old = Nominals Σᴵ₀ Σᴾ₀
    module New = Nominals (scopeStore S) (scopeStore T)

  right-nominal-relation : ∀ {Δᴵ′ Δᴾ′} (A : R.Old.ScopedType) Y
      (entryY : Σᴾ₀ ∋ Y ⦂ R.Old.preciseTy A)
      (P : PhysicalScope (scopeStore S) Δᴵ′)
      (Q : PhysicalScope (scopeStore T) Δᴾ′) k U V
    → R.New.related (R.rebase (Old.right-nominal A Y entryY)) P Q k U V
      ≡ R.New.related (New.right-nominal (R.rebase A) (scopeVar T Y)
          (scope-entry T entryY)) P Q k U V
  right-nominal-relation A Y entryY P Q k U V
      rewrite graft-variable T Q Y | graft-type T Q (R.Old.preciseTy A) =
    refl
