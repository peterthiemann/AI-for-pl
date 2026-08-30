module proof.LR-narrow.ScopedBodyInterpretation where

-- File Charter:
--   * Interprets the natural/variable/arrow fragment of existing type syntax
--     in scoped semantic environments; variables may denote any ScopedType.
--   * Proves endpoint, renaming, and substitution coherence structurally.
--     Rebasing preserves the interpreted relation in both directions.
--   * This fragment excludes dynamic and nested universal type syntax.
--     Substitution coherence does not identify a nominal seal with its
--     representation: converting between them remains an operational proof.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans) renaming (subst to subst≡)

open import Types
open import TyStore
open import Consistency using (_↪ᵗ_; toRenameᵗ)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopeRebase
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedTypeEquivalence
open import proof.LR-narrow.ScopedTypeSubstitution using (scope-body-shift)
open import proof.LR-narrow.VisibleEnvironment

data BodyFragment {n : TyCtx} : Ty n → Set where
  natural-body : BodyFragment (‵ `ℕ)
  variable-body : ∀ {X} → BodyFragment (＇ X)
  arrow-body : ∀ {A B}
    → BodyFragment A → BodyFragment B → BodyFragment (A ⇒ B)

rename-body : ∀ {n m C} (ρ : n ⇒ʳ m)
  → BodyFragment C → BodyFragment (renameᵗ ρ C)
rename-body ρ natural-body = natural-body
rename-body ρ variable-body = variable-body
rename-body ρ (arrow-body p q) =
  arrow-body (rename-body ρ p) (rename-body ρ q)

subst-body : ∀ {n m C} (σ : n ⇒ˢ m)
  → (∀ X → BodyFragment (σ X))
  → BodyFragment C → BodyFragment (substᵗ σ C)
subst-body σ ps natural-body = natural-body
subst-body σ ps (variable-body {X}) = ps X
subst-body σ ps (arrow-body p q) =
  arrow-body (subst-body σ ps p) (subst-body σ ps q)

scoped-body-visible : ∀ {Δ₀ Δ n} {Σ₀ : TyStore Δ₀}
    (T : PhysicalScope Σ₀ Δ) (ρ : n ↪ᵗ Δ₀) {C : Ty (suc n)}
  → BodyFragment C
  → scopeBody T (substᵗ (extsᵗ (λ X → ＇ toRenameᵗ ρ X)) C)
      ≡ renameᵗ (extᵗ (toRenameᵗ (scopeNames T ρ))) C
scoped-body-visible T ρ natural-body = scope-body-natural T
scoped-body-visible T ρ (variable-body {Fin.zero}) = scope-body-bound T
scoped-body-visible T ρ (variable-body {Fin.suc X}) = trans
  (scope-body-shift T (＇ toRenameᵗ ρ X))
  (cong ⇑ᵗ (trans (scope-variable T (toRenameᵗ ρ X))
    (cong ＇_ (sym (scope-names T ρ X)))))
scoped-body-visible T ρ (arrow-body p q) = trans
  (scope-body-arrow T _ _)
  (cong₂ _⇒_ (scoped-body-visible T ρ p) (scoped-body-visible T ρ q))

module Interpretation {Δᴵ Δᴾ} (Σᴵ : TyStore Δᴵ) (Σᴾ : TyStore Δᴾ) where

  open Model Σᴵ Σᴾ
  open Equivalence Σᴵ Σᴾ

  extend-meaning : ∀ {n} → ScopedType → (TyVar n → ScopedType)
    → TyVar (suc n) → ScopedType
  extend-meaning A ρ Fin.zero = A
  extend-meaning A ρ (Fin.suc X) = ρ X

  interpret-body : ∀ {n} {C : Ty n}
    → BodyFragment C → (TyVar n → ScopedType) → ScopedType
  interpret-body natural-body ρ = natural
  interpret-body (variable-body {X}) ρ = ρ X
  interpret-body (arrow-body p q) ρ =
    arrow (interpret-body p ρ) (interpret-body q ρ)

  endpointᴵ : ∀ {n C} (p : BodyFragment C) (ρ : TyVar n → ScopedType)
    → impreciseTy (interpret-body p ρ)
      ≡ substᵗ (λ X → impreciseTy (ρ X)) C
  endpointᴵ natural-body ρ = refl
  endpointᴵ variable-body ρ = refl
  endpointᴵ (arrow-body p q) ρ = cong₂ _⇒_ (endpointᴵ p ρ) (endpointᴵ q ρ)

  endpointᴾ : ∀ {n C} (p : BodyFragment C) (ρ : TyVar n → ScopedType)
    → preciseTy (interpret-body p ρ)
      ≡ substᵗ (λ X → preciseTy (ρ X)) C
  endpointᴾ natural-body ρ = refl
  endpointᴾ variable-body ρ = refl
  endpointᴾ (arrow-body p q) ρ = cong₂ _⇒_ (endpointᴾ p ρ) (endpointᴾ q ρ)

  interpret-renaming : ∀ {n m C} (ρ : n ⇒ʳ m) (p : BodyFragment C)
      (η : TyVar m → ScopedType)
    → interpret-body (rename-body ρ p) η
      ≡ interpret-body p (λ X → η (ρ X))
  interpret-renaming ρ natural-body η = refl
  interpret-renaming ρ variable-body η = refl
  interpret-renaming ρ (arrow-body p q) η = cong₂ arrow
    (interpret-renaming ρ p η) (interpret-renaming ρ q η)

  interpret-substitution : ∀ {n m C} (σ : n ⇒ˢ m)
      (ps : ∀ X → BodyFragment (σ X)) (p : BodyFragment C)
      (η : TyVar m → ScopedType)
    → interpret-body (subst-body σ ps p) η
      ≡ interpret-body p (λ X → interpret-body (ps X) η)
  interpret-substitution σ ps natural-body η = refl
  interpret-substitution σ ps variable-body η = refl
  interpret-substitution σ ps (arrow-body p q) η = cong₂ arrow
    (interpret-substitution σ ps p η) (interpret-substitution σ ps q η)

  interpret-cong : ∀ {n C} (p : BodyFragment C)
      {η θ : TyVar n → ScopedType}
    → (∀ X → Equivalent (η X) (θ X))
    → Equivalent (interpret-body p η) (interpret-body p θ)
  interpret-cong natural-body eq = eq-refl
  interpret-cong (variable-body {X}) eq = eq X
  interpret-cong (arrow-body p q) eq =
    arrow-cong (interpret-cong p eq) (interpret-cong q eq)

module BodyRebase {Δᴵ₀ Δᴾ₀ Δᴵ Δᴾ}
    {Σᴵ₀ : TyStore Δᴵ₀} {Σᴾ₀ : TyStore Δᴾ₀}
    (S : PhysicalScope Σᴵ₀ Δᴵ) (T : PhysicalScope Σᴾ₀ Δᴾ) where

  module Old = Interpretation Σᴵ₀ Σᴾ₀
  module New = Interpretation (scopeStore S) (scopeStore T)
  module R = Rebase S T
  module RE = RebaseEquivalence S T
  open Equivalence (scopeStore S) (scopeStore T)

  interpret-rebase : ∀ {n C} (p : BodyFragment C)
      (η : TyVar n → Model.ScopedType Σᴵ₀ Σᴾ₀)
    → Equivalent (R.rebase (Old.interpret-body p η))
        (New.interpret-body p (λ X → R.rebase (η X)))
  interpret-rebase natural-body η = RE.natural
  interpret-rebase variable-body η = eq-refl
  interpret-rebase (arrow-body p q) η = eq-trans
    (RE.arrow (Old.interpret-body p η) (Old.interpret-body q η))
    (arrow-cong (interpret-rebase p η) (interpret-rebase q η))

-- The visible binder denotes its fresh nominal slot, not its representation.
-- This identifies the body environment used after allocation; it does not
-- perform the seal/unseal conversion back to the public argument type.

module VisibleBodyExtension {Δᴵ Δᴾ n}
    {Σᴵ : TyStore Δᴵ} {Σᴾ : TyStore Δᴾ}
    (env : VisibleEnvironment Σᴵ Σᴾ n) (A : Model.ScopedType Σᴵ Σᴾ) where

  module X = Extend env A
  module New = Interpretation (store-bind Σᴵ (Model.impreciseTy A))
                              (store-bind Σᴾ (Model.preciseTy A))
  open Equivalence (store-bind Σᴵ (Model.impreciseTy A))
                   (store-bind Σᴾ (Model.preciseTy A))

  private
    old-equivalent : ∀ Y
      → Equivalent (X.R.rebase (meaning env Y))
          (meaning X.extended (Fin.suc Y))
    old-equivalent Y = record
      { imprecise-type = refl
      ; precise-type = refl
      ; to = λ { {S = S} {T} {k} {U} {V} r →
          subst≡ (λ Q → Q) (X.old-meaning S T Y k U V) r }
      ; from = λ { {S = S} {T} {k} {U} {V} r →
          subst≡ (λ Q → Q) (sym (X.old-meaning S T Y k U V)) r }
      }

  interpret-extended : ∀ {C : Ty (suc n)} (p : BodyFragment C)
    → Equivalent
        (New.interpret-body p
          (New.extend-meaning
            (X.R.New.nominal (X.R.rebase A) Fin.zero Fin.zero
              (Z∋ refl) (Z∋ refl))
            (λ Y → X.R.rebase (meaning env Y))))
        (New.interpret-body p (meaning X.extended))
  interpret-extended p = New.interpret-cong p
    (λ { Fin.zero → eq-refl ; (Fin.suc Y) → old-equivalent Y })
