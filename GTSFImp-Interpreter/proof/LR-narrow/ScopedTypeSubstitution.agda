module proof.LR-narrow.ScopedTypeSubstitution where

-- File Charter:
--   * Proves that physical scopes commute with type opening and body shift.
--   * Shows that grafting composes scoped universal bodies by reassociating
--     the same physical allocation history.
--   * Relates scoped bodies to visible endpoint substitutions.
--   * Uses only syntax-level type renaming and substitution laws from Types
--     together with PhysicalScope.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans; sym)

open import Types
open import TyStore
open import proof.LR-narrow.PhysicalScope

private
  substᵗ-substᵗ : ∀ {Δ₁ Δ₂ Δ₃}
      (σ : Δ₂ ⇒ˢ Δ₃) (τ : Δ₁ ⇒ˢ Δ₂) (A : Ty Δ₁)
    → substᵗ σ (substᵗ τ A) ≡ substᵗ (λ X → substᵗ σ (τ X)) A
  substᵗ-substᵗ σ τ (＇ X) = refl
  substᵗ-substᵗ σ τ (‵ ι) = refl
  substᵗ-substᵗ σ τ ★ = refl
  substᵗ-substᵗ σ τ (A ⇒ B) =
    cong₂ _⇒_ (substᵗ-substᵗ σ τ A) (substᵗ-substᵗ σ τ B)
  substᵗ-substᵗ σ τ (`∀ A) =
    cong `∀
      (trans
        (substᵗ-substᵗ (extsᵗ σ) (extsᵗ τ) A)
        (substᵗ-cong A exts-comp))
    where
    exts-comp : ∀ X
      → substᵗ (extsᵗ σ) (extsᵗ τ X)
        ≡ extsᵗ (λ Y → substᵗ σ (τ Y)) X
    exts-comp Fin.zero = refl
    exts-comp (Fin.suc X) = substᵗ-shift σ (τ X)

  scopeSub : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
    → PhysicalScope Σ₀ Δ → Δ₀ ⇒ˢ Δ
  scopeSub S X = scopeTy S (＇ X)

  scopeTy-subst : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
      (S : PhysicalScope Σ₀ Δ) (A : Ty Δ₀)
    → substᵗ (scopeSub S) A ≡ scopeTy S A
  scopeTy-subst root A = substᵗ-id A
  scopeTy-subst (allocate S B) A =
    trans
      (substᵗ-cong A (λ X → refl))
      (trans
        (sym (renameᵗ-subst Fin.suc (scopeSub S) A))
        (cong ⇑ᵗ (scopeTy-subst S A)))

  scopeBody-subst : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
      (S : PhysicalScope Σ₀ Δ) (C : Ty (suc Δ₀))
    → substᵗ (extsᵗ (scopeSub S)) C ≡ scopeBody S C
  scopeBody-subst {Σ₀ = Σ₀} root C =
    trans (substᵗ-cong C exts-id) (substᵗ-id C)
    where
    exts-id : ∀ X → extsᵗ (scopeSub (root {Σ₀ = Σ₀})) X ≡ ＇ X
    exts-id Fin.zero = refl
    exts-id (Fin.suc X) = refl
  scopeBody-subst (allocate S B) C =
    trans
      (substᵗ-cong C exts-scope)
      (trans
        (sym (renameᵗ-subst (extᵗ Fin.suc) (extsᵗ (scopeSub S)) C))
        (cong (renameᵗ (extᵗ Fin.suc)) (scopeBody-subst S C)))
    where
    exts-scope : ∀ X
      → extsᵗ (scopeSub (allocate S B)) X
        ≡ renameᵗ (extᵗ Fin.suc) (extsᵗ (scopeSub S) X)
    exts-scope Fin.zero = refl
    exts-scope (Fin.suc X) =
      sym (renameᵗ-shift Fin.suc (scopeSub S X))

  scope-open-env : ∀ {Δ} (A : Ty Δ) (X : TyVar (suc Δ))
    → singleSubᵗ (⇑ᵗ A) (extᵗ Fin.suc X)
      ≡ renameᵗ Fin.suc (singleSubᵗ A X)
  scope-open-env A Fin.zero = refl
  scope-open-env A (Fin.suc X) = refl

  instantiateEnv : ∀ {Δ₀ n Δ} {Σ₀ : TyStore Δ₀}
    → PhysicalScope Σ₀ Δ → (n ⇒ˢ Δ₀) → Ty Δ → suc n ⇒ˢ Δ
  instantiateEnv S ρ A Fin.zero = A
  instantiateEnv S ρ A (Fin.suc X) = scopeTy S (ρ X)

  scope-instantiate-env : ∀ {Δ₀ n Δ} {Σ₀ : TyStore Δ₀}
      (S : PhysicalScope Σ₀ Δ) (ρ : n ⇒ˢ Δ₀) (A : Ty Δ)
      (X : TyVar (suc n))
    → substᵗ (singleSubᵗ A)
        (substᵗ (extsᵗ (scopeSub S)) (extsᵗ ρ X))
      ≡ instantiateEnv S ρ A X
  scope-instantiate-env S ρ A Fin.zero = refl
  scope-instantiate-env S ρ A (Fin.suc X) =
    trans
      (cong (substᵗ (singleSubᵗ A)) (substᵗ-shift (scopeSub S) (ρ X)))
      (trans
        (cong (substᵗ (singleSubᵗ A)) (cong ⇑ᵗ (scopeTy-subst S (ρ X))))
        (shift-openᵗ (scopeTy S (ρ X)) A))

scope-open : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
    (S : PhysicalScope Σ₀ Δ) (C : Ty (suc Δ₀)) (A : Ty Δ₀)
  → scopeBody S C [ scopeTy S A ]ᵗ ≡ scopeTy S (C [ A ]ᵗ)
scope-open root C A = refl
scope-open (allocate S B) C A =
  trans
    (substᵗ-rename (singleSubᵗ (⇑ᵗ (scopeTy S A))) (extᵗ Fin.suc)
      (scopeBody S C))
    (trans
      (substᵗ-cong (scopeBody S C) (scope-open-env (scopeTy S A)))
      (trans
        (sym (renameᵗ-subst Fin.suc (singleSubᵗ (scopeTy S A))
          (scopeBody S C)))
        (cong ⇑ᵗ (scope-open S C A))))

scope-body-shift : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
    (S : PhysicalScope Σ₀ Δ) (A : Ty Δ₀)
  → scopeBody S (⇑ᵗ A) ≡ ⇑ᵗ (scopeTy S A)
scope-body-shift root A = refl
scope-body-shift (allocate S B) A =
  trans
    (cong (renameᵗ (extᵗ Fin.suc)) (scope-body-shift S A))
    (renameᵗ-shift Fin.suc (scopeTy S A))

graft-body : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀} (S : PhysicalScope Σ₀ Δ)
    (P : PhysicalScope (scopeStore S) Δ′) (C : Ty (suc Δ₀))
  → scopeBody (graft S P) C ≡ scopeBody P (scopeBody S C)
graft-body S root C = refl
graft-body S (allocate P A) C =
  cong (renameᵗ (extᵗ Fin.suc)) (graft-body S P C)

scope-instantiate : ∀ {Δ₀ n Δ} {Σ₀ : TyStore Δ₀}
    (S : PhysicalScope Σ₀ Δ) (ρ : n ⇒ˢ Δ₀) (C : Ty (suc n)) (A : Ty Δ)
  → substᵗ (λ { Fin.zero → A ; (Fin.suc X) → scopeTy S (ρ X) }) C
    ≡ scopeBody S (substᵗ (extsᵗ ρ) C) [ A ]ᵗ
scope-instantiate S ρ C A =
  sym
    (trans
      (cong (_[ A ]ᵗ) (sym (scopeBody-subst S (substᵗ (extsᵗ ρ) C))))
      (trans
        (cong (substᵗ (singleSubᵗ A))
          (substᵗ-substᵗ (extsᵗ (scopeSub S)) (extsᵗ ρ) C))
        (trans
          (substᵗ-substᵗ (singleSubᵗ A)
            (λ X → substᵗ (extsᵗ (scopeSub S)) (extsᵗ ρ X)) C)
          (trans (substᵗ-cong C (scope-instantiate-env S ρ A))
            (substᵗ-cong C (λ { Fin.zero → refl ; (Fin.suc X) → refl }))))))
