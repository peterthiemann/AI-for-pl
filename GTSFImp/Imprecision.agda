module Imprecision where

-- File Charter:
--   * Defines intrinsically scoped type imprecision.
--   * Includes structural universal-to-dynamic and empty-universal clauses
--     required for consistency to coincide with a common lower bound.

open import Data.Nat using (zero; suc)
open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Nullary.Decidable using (False)
open import Types

private
  variable
    Δ : TyCtx

-- A variable is either paired with itself, unconstrained below `★`,
-- or an *alias* that unfolds to a stored representative type.  Alias
-- modes arise only in runtime worlds, where a conversion allocates a
-- name for a type that already has an imprecise counterpart.

data VarImp (Δ : TyCtx) : Set where
  X⊑X : VarImp Δ
  X⊑★ : VarImp Δ
  X⊑ᵗ : Ty Δ → VarImp Δ

⇑ᵛ : VarImp Δ → VarImp (suc Δ)
⇑ᵛ X⊑X = X⊑X
⇑ᵛ X⊑★ = X⊑★
⇑ᵛ (X⊑ᵗ T) = X⊑ᵗ (⇑ᵗ T)

ImpEnv : TyCtx → Set
ImpEnv Δ = TyVar Δ → VarImp Δ

idᵐ : ∀ {Δ} → ImpEnv Δ
idᵐ X = X⊑X

extendᵐ : VarImp (suc Δ) → ImpEnv Δ → ImpEnv (suc Δ)
extendᵐ v μ zero = v
extendᵐ v μ (suc X) = ⇑ᵛ (μ X)

extᵐ : ImpEnv Δ → ImpEnv (suc Δ)
extᵐ = extendᵐ X⊑X

instᵐ : ImpEnv Δ → ImpEnv (suc Δ)
instᵐ = extendᵐ X⊑★

-- Transporting a mode across a binder.  The paired and dynamic modes
-- are stable, so their equations survive `cong ⇑ᵛ`.

ext-mode-paired : ∀ {Δ} {μ : ImpEnv Δ} {v : VarImp (suc Δ)}
    {Z : TyVar Δ}
  → μ Z ≡ X⊑X
  → extendᵐ v μ (suc Z) ≡ X⊑X
ext-mode-paired eq = cong ⇑ᵛ eq

ext-mode-star : ∀ {Δ} {μ : ImpEnv Δ} {v : VarImp (suc Δ)}
    {Z : TyVar Δ}
  → μ Z ≡ X⊑★
  → extendᵐ v μ (suc Z) ≡ X⊑★
ext-mode-star eq = cong ⇑ᵛ eq

-- and are reflected back, since the alias mode never lifts to them.
-- The `⇑ᵛ`-based inverses leave no unsolved arguments, because
-- `extendᵐ v μ (suc Z)` reduces to `⇑ᵛ (μ Z)` and forgets `v`.

lift-paired-inv : ∀ {Δ} {w : VarImp Δ}
  → ⇑ᵛ w ≡ X⊑X
  → w ≡ X⊑X
lift-paired-inv {w = X⊑X} eq = refl

lift-star-inv : ∀ {Δ} {w : VarImp Δ}
  → ⇑ᵛ w ≡ X⊑★
  → w ≡ X⊑★
lift-star-inv {w = X⊑★} eq = refl

-- Renaming a mode renames the representative of an alias and leaves
-- the paired and dynamic modes alone; `⇑ᵛ` is the shift instance.

renameᵛ : ∀ {Δ Δ′} → (Δ ⇒ʳ Δ′) → VarImp Δ → VarImp Δ′
renameᵛ ρ X⊑X = X⊑X
renameᵛ ρ X⊑★ = X⊑★
renameᵛ ρ (X⊑ᵗ T) = X⊑ᵗ (renameᵗ ρ T)

renameᵛ-paired-inv : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {w : VarImp Δ}
  → renameᵛ ρ w ≡ X⊑X
  → w ≡ X⊑X
renameᵛ-paired-inv {w = X⊑X} eq = refl

renameᵛ-star-inv : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {w : VarImp Δ}
  → renameᵛ ρ w ≡ X⊑★
  → w ≡ X⊑★
renameᵛ-star-inv {w = X⊑★} eq = refl

renameᵛ-alias-inv : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {w : VarImp Δ}
    {T : Ty Δ′}
  → renameᵛ ρ w ≡ X⊑ᵗ T
  → Σ[ T₀ ∈ Ty Δ ] ((w ≡ X⊑ᵗ T₀) × (T ≡ renameᵗ ρ T₀))
renameᵛ-alias-inv {w = X⊑ᵗ T₀} refl = T₀ , refl , refl

ext-mode-paired-inv : ∀ {Δ} (μ : ImpEnv Δ) {v : VarImp (suc Δ)}
    (Z : TyVar Δ)
  → extendᵐ v μ (suc Z) ≡ X⊑X
  → μ Z ≡ X⊑X
ext-mode-paired-inv μ Z eq with μ Z
ext-mode-paired-inv μ Z eq | X⊑X = refl
ext-mode-paired-inv μ Z () | X⊑★
ext-mode-paired-inv μ Z () | X⊑ᵗ T

ext-mode-star-inv : ∀ {Δ} (μ : ImpEnv Δ) {v : VarImp (suc Δ)}
    (Z : TyVar Δ)
  → extendᵐ v μ (suc Z) ≡ X⊑★
  → μ Z ≡ X⊑★
ext-mode-star-inv μ Z eq with μ Z
ext-mode-star-inv μ Z () | X⊑X
ext-mode-star-inv μ Z eq | X⊑★ = refl
ext-mode-star-inv μ Z () | X⊑ᵗ T

----------------------------------------------------------------------
-- Imprecision
----------------------------------------------------------------------

infix 4 _⊢_⊑_

data _⊢_⊑_ {Δ : TyCtx} (μ : ImpEnv Δ) : Ty Δ → Ty Δ → Set where

  ★⊑★ :
      -------------
      μ ⊢ ★ ⊑ ★

  ι⊑ι : ∀ {ι}
      ---------------------
      → μ ⊢ (‵ ι) ⊑ (‵ ι)

  X⊑X : ∀ {X}
      -------------------
    → μ ⊢ ＇ X ⊑ ＇ X

  ⇒⊑⇒ : ∀ {A A′ B B′}
    → μ ⊢ A ⊑ A′
    → μ ⊢ B ⊑ B′
      ---------------------------
    → μ ⊢ (A ⇒ B) ⊑ (A′ ⇒ B′)

  ∀⊑∀ : ∀ {A B}
    → extᵐ μ ⊢ A ⊑ B
      -----------------------
    → μ ⊢ (`∀ A) ⊑ (`∀ B)

  ⇒⊑★ : ∀ {A B}
    → μ ⊢ A ⊑ ★
    → μ ⊢ B ⊑ ★
      -----------------
    → μ ⊢ A ⇒ B ⊑ ★

  ι⊑★ : ∀ {ι}
      ---------------
    → μ ⊢ ‵ ι ⊑ ★

  X⊑★ : ∀ {X}
    → μ X ≡ X⊑★
      ----------------
    → μ ⊢ ＇ X ⊑ ★

  ∀⊑ : ∀ {A B}
    → NonVar A
    → zero ∈ᵗ A
    → instᵐ μ ⊢ A ⊑ ⇑ᵗ B
      ---------------------------
    → μ ⊢ (`∀ A) ⊑ B

  ∀★⊑★ :
      ------------------
    μ ⊢ (`∀ ★) ⊑ ★

  ∀⊑★ : ∀ {A}
    → NonStar A
    → extᵐ μ ⊢ A ⊑ ★
      -----------------
    → μ ⊢ (`∀ A) ⊑ ★

  bot-elim :
      --------------------------------
    μ ⊢ (`∀ (＇ zero)) ⊑ (`∀ ★)

  bot⊑★ :
      ---------------------------
    μ ⊢ (`∀ (＇ zero)) ⊑ ★

  -- An alias inherits its representative's imprecisions.  The rule is
  -- the composite of the unfolding `＇X ⊑ T` with `T ⊑ B`; fusing it
  -- keeps the judgment closed under transitivity, which the separate
  -- unfolding axiom would not be (the mode records `T`, not `B`).

  alias : ∀ {X T B}
    → μ X ≡ X⊑ᵗ T
    → {notSelf : False (isVar? X B)}
    → μ ⊢ T ⊑ B
      ---------------------------
    → μ ⊢ ＇ X ⊑ B

infix 4 _⊑_

_⊑_ : ∀ {Δ} → Ty Δ → Ty Δ → Set
A ⊑ B = idᵐ ⊢ A ⊑ B
