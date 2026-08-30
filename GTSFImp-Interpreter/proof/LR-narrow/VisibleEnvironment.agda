module proof.LR-narrow.VisibleEnvironment where

-- File Charter:
--   * Separates visible semantic names from the physical model roots.
--   * Injective order-preserving endpoint embeddings retain private slots
--     outside the visible environment, including after later paired binds.
--   * Re-roots old meanings and introduces fresh nominal meanings with
--     actual lookup evidence. This is not yet a universal-type interpretation.

open import Data.Nat using (suc)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong) renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms using (Term)
import Consistency as C
open import Consistency using (_↪ᵗ_; toRenameᵗ)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopeRebase

record VisibleEnvironment {Δᴵ Δᴾ} (Σᴵ : TyStore Δᴵ) (Σᴾ : TyStore Δᴾ)
    (visible : TyCtx) : Set₁ where
  module B = Model Σᴵ Σᴾ
  field
    impreciseNames : visible ↪ᵗ Δᴵ
    preciseNames : visible ↪ᵗ Δᴾ
    representation : TyVar visible → B.ScopedType
    impreciseEntry : ∀ X
      → Σᴵ ∋ toRenameᵗ impreciseNames X ⦂ B.impreciseTy (representation X)
    preciseEntry : ∀ X
      → Σᴾ ∋ toRenameᵗ preciseNames X ⦂ B.preciseTy (representation X)

  meaning : TyVar visible → B.ScopedType
  meaning X = B.nominal (representation X)
    (toRenameᵗ impreciseNames X) (toRenameᵗ preciseNames X)
    (impreciseEntry X) (preciseEntry X)

open VisibleEnvironment public

scopeNames : ∀ {Δ₀ Δ n} {Σ₀ : TyStore Δ₀}
  → PhysicalScope Σ₀ Δ → n ↪ᵗ Δ₀ → n ↪ᵗ Δ
scopeNames root ρ = ρ
scopeNames (allocate S A) ρ = C.skip (scopeNames S ρ)

scope-names : ∀ {Δ₀ Δ n} {Σ₀ : TyStore Δ₀}
    (S : PhysicalScope Σ₀ Δ) (ρ : n ↪ᵗ Δ₀) X
  → toRenameᵗ (scopeNames S ρ) X ≡ scopeVar S (toRenameᵗ ρ X)
scope-names root ρ X = refl
scope-names (allocate S A) ρ X = cong Fin.suc (scope-names S ρ X)

rerootEnvironment : ∀ {Δᴵ₀ Δᴾ₀ Δᴵ Δᴾ n}
    {Σᴵ₀ : TyStore Δᴵ₀} {Σᴾ₀ : TyStore Δᴾ₀}
    (S : PhysicalScope Σᴵ₀ Δᴵ) (T : PhysicalScope Σᴾ₀ Δᴾ)
  → VisibleEnvironment Σᴵ₀ Σᴾ₀ n
  → VisibleEnvironment (scopeStore S) (scopeStore T) n
rerootEnvironment S T env = record
  { impreciseNames = scopeNames S (impreciseNames env)
  ; preciseNames = scopeNames T (preciseNames env)
  ; representation = λ X → Rebase.rebase S T (representation env X)
  ; impreciseEntry = λ X →
      subst≡ (λ Y → scopeStore S ∋ Y ⦂
          scopeTy S (Model.impreciseTy (representation env X)))
        (sym (scope-names S (impreciseNames env) X))
        (scope-entry S (impreciseEntry env X))
  ; preciseEntry = λ X →
      subst≡ (λ Y → scopeStore T ∋ Y ⦂
          scopeTy T (Model.preciseTy (representation env X)))
        (sym (scope-names T (preciseNames env) X))
        (scope-entry T (preciseEntry env X))
  }

reroot-meaning : ∀ {Δᴵ₀ Δᴾ₀ Δᴵ Δᴾ Δᴵ′ Δᴾ′ n}
    {Σᴵ₀ : TyStore Δᴵ₀} {Σᴾ₀ : TyStore Δᴾ₀}
    (S : PhysicalScope Σᴵ₀ Δᴵ) (T : PhysicalScope Σᴾ₀ Δᴾ)
    (env : VisibleEnvironment Σᴵ₀ Σᴾ₀ n) X
    (P : PhysicalScope (scopeStore S) Δᴵ′)
    (Q : PhysicalScope (scopeStore T) Δᴾ′) k U V
  → Model.related
      (Rebase.rebase S T (meaning env X)) P Q k U V
      ≡ Model.related
          (meaning (rerootEnvironment S T env) X) P Q k U V
reroot-meaning {Σᴵ₀ = Σᴵ₀} {Σᴾ₀} S T env X P Q k U V
    rewrite scope-names S (impreciseNames env) X
      | scope-names T (preciseNames env) X
      | graft-variable S P (toRenameᵗ (impreciseNames env) X)
      | graft-variable T Q (toRenameᵗ (preciseNames env) X)
      | graft-type S P (Model.impreciseTy (representation env X))
      | graft-type T Q (Model.preciseTy (representation env X)) = refl

module Extend {Δᴵ Δᴾ n} {Σᴵ : TyStore Δᴵ} {Σᴾ : TyStore Δᴾ}
    (env : VisibleEnvironment Σᴵ Σᴾ n) (A : Model.ScopedType Σᴵ Σᴾ) where

  module Old = Model Σᴵ Σᴾ
  module R = Rebase {Σᴵ₀ = Σᴵ} {Σᴾ₀ = Σᴾ}
    (allocate root (Old.impreciseTy A)) (allocate root (Old.preciseTy A))

  extended : VisibleEnvironment (store-bind Σᴵ (Old.impreciseTy A))
    (store-bind Σᴾ (Old.preciseTy A)) (suc n)
  extended = record
    { impreciseNames = C.keep (impreciseNames env)
    ; preciseNames = C.keep (preciseNames env)
    ; representation = λ { Fin.zero → R.rebase A
        ; (Fin.suc X) → R.rebase (representation env X) }
    ; impreciseEntry = λ { Fin.zero → Z∋ refl
        ; (Fin.suc X) → S-bind∋ (impreciseEntry env X) refl }
    ; preciseEntry = λ { Fin.zero → Z∋ refl
        ; (Fin.suc X) → S-bind∋ (preciseEntry env X) refl }
    }

  old-meaning : ∀ {Δᴵ′ Δᴾ′}
      (P : PhysicalScope (store-bind Σᴵ (Old.impreciseTy A)) Δᴵ′)
      (Q : PhysicalScope (store-bind Σᴾ (Old.preciseTy A)) Δᴾ′) X k U V
    → R.New.related (R.rebase (meaning env X)) P Q k U V
        ≡ R.New.related (meaning extended (Fin.suc X)) P Q k U V
  old-meaning P Q X k U V = R.nominal-relation (representation env X)
    (toRenameᵗ (impreciseNames env) X) (toRenameᵗ (preciseNames env) X)
    (impreciseEntry env X) (preciseEntry env X) P Q k U V
