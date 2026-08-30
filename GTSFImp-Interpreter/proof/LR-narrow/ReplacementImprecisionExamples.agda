module proof.LR-narrow.ReplacementImprecisionExamples where

-- File Charter:
--   * Checked type-imprecision regressions for historical conceal and pending
--     universal-wrapper failures, on the current alias-free calculus.
--   * Refutes inversion of replacement and identification of a fresh nominal
--     type with its representation before the conversion has taken place.
--   * Does not claim that these type-level failures are operational failures.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import Conversion using (replaceTy)
import Imprecision as I

private
  X : TyVar 1
  X = Fin.zero

replacement-erases-old-name :
  replaceTy X (‵ `ℕ) (`∀ (＇ (Fin.suc X))) ≡ `∀ (‵ `ℕ)
replacement-erases-old-name = refl

replaced-universal-dynamic :
  I.idᵐ I.⊢ replaceTy X (‵ `ℕ) (`∀ (＇ (Fin.suc X))) ⊑ ★
replaced-universal-dynamic = I.∀⊑★ nonstar-ι I.ι⊑★

original-universal-not-dynamic :
  I.idᵐ I.⊢ `∀ (＇ (Fin.suc X)) ⊑ ★ → ⊥
original-universal-not-dynamic (I.∀⊑ () _ _)
original-universal-not-dynamic (I.∀⊑★ _ (I.X⊑★ ()))

un-replacement-impossible :
  (∀ {B : Ty 1} → I.idᵐ I.⊢ replaceTy X (‵ `ℕ) B ⊑ ★
    → I.idᵐ I.⊢ B ⊑ ★)
  → ⊥
un-replacement-impossible rule =
  original-universal-not-dynamic
    (rule {B = `∀ (＇ (Fin.suc X))} replaced-universal-dynamic)

base-not-fresh-name : ∀ {Δ} {μ : I.ImpEnv Δ} {Y : TyVar Δ}
  → μ I.⊢ ‵ `ℕ ⊑ ＇ Y → ⊥
base-not-fresh-name ()

old-not-fresh-name : ∀ {μ : I.ImpEnv 2}
  → μ I.⊢ ＇ (Fin.suc Fin.zero) ⊑ ＇ Fin.zero → ⊥
old-not-fresh-name ()

old-below-replaced-fresh : ∀ {μ : I.ImpEnv 2}
  → μ I.⊢ ＇ (Fin.suc Fin.zero)
      ⊑ replaceTy Fin.zero (＇ (Fin.suc Fin.zero)) (＇ Fin.zero)
old-below-replaced-fresh = I.X⊑X
