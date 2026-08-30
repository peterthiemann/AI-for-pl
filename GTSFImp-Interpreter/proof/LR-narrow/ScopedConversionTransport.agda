module proof.LR-narrow.ScopedConversionTransport where

-- File Charter:
--   * Lifts reveal and conceal conversions from a physical root into any
--     physical scope by renaming along the retained allocation history.
--   * Proves scoped conversion validity, future lifting through scoped
--     reveal and conceal terms, and frame transport through store changes.
--   * Exposes packaged structural shape laws for scoped arrow, identity,
--     unseal, and seal conversions.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)

open import Types
open import TyStore
open import Consistency using (wk↪ᵗ; toRenameᵗ)
open import Conversion
open import CastTerms
open import Reduction
open import proof.TypeInTermSubst using
  (StoreRename-suc-bind; reveal-renameᵗ; conceal-renameᵗ; toRename-wk-eq)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.FramePhases using (Frame)
open import proof.LR-narrow.RevealFrames using
  (RevealFrm; ConcealFrm; revealFrame; concealFrame; reveal-frm; conceal-frm)
open import proof.LR-narrow.SlotLifting using
  (rename↑-identity; rename↓-identity)
open import proof.LR-narrow.TermRenamingComposition using
  (reveal-pointwise; conceal-pointwise)
open import proof.LR-narrow.TypeRenamingComposition using
  (Packed↑; Packed↓; pack↑; pack↓; pack-↦↑; pack-↦↓; apply↑; apply↓)

mutual
  scope↑ : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀} (S : PhysicalScope Σ₀ Δ) {A B}
    → Conv↑ Δ₀ A B
    → Conv↑ Δ (scopeTy S A) (scopeTy S B)
  scope↑ root c = c
  scope↑ (allocate S A) c = rename↑ Fin.suc (scope↑ S c)

  scope↓ : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀} (S : PhysicalScope Σ₀ Δ) {A B}
    → Conv↓ Δ₀ A B
    → Conv↓ Δ (scopeTy S A) (scopeTy S B)
  scope↓ root c = c
  scope↓ (allocate S A) c = rename↓ Fin.suc (scope↓ S c)

private
  mapPack↑ : ∀ {Δ} → Packed↑ Δ → Packed↑ (suc Δ)
  mapPack↑ (pack↑ c) = pack↑ (rename↑ Fin.suc c)

  mapPack↓ : ∀ {Δ} → Packed↓ Δ → Packed↓ (suc Δ)
  mapPack↓ (pack↓ c) = pack↓ (rename↓ Fin.suc c)

  reveal-frm-pack : ∀ {Δ} {A B A′ B′ : Ty Δ}
      {c : Conv↑ Δ A B} {d : Conv↑ Δ A′ B′}
    → pack↑ c ≡ pack↑ d
    → reveal-frm c ≡ reveal-frm d
  reveal-frm-pack refl = refl

  conceal-frm-pack : ∀ {Δ} {A B A′ B′ : Ty Δ}
      {c : Conv↓ Δ A B} {d : Conv↓ Δ A′ B′}
    → pack↓ c ≡ pack↓ d
    → conceal-frm c ≡ conceal-frm d
  conceal-frm-pack refl = refl

  scope↑-arrow-pack : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
      (S : PhysicalScope Σ₀ Δ) {A A′ B B′}
      (c : Conv↓ Δ₀ A′ A) (d : Conv↑ Δ₀ B B′)
    → pack↑ (scope↑ S (c ↦↑ d)) ≡ pack↑ (scope↓ S c ↦↑ scope↑ S d)
  scope↑-arrow-pack root c d = refl
  scope↑-arrow-pack (allocate S A) c d =
    cong mapPack↑ (scope↑-arrow-pack S c d)

  scope↓-arrow-pack : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
      (S : PhysicalScope Σ₀ Δ) {A A′ B B′}
      (c : Conv↑ Δ₀ A′ A) (d : Conv↓ Δ₀ B B′)
    → pack↓ (scope↓ S (c ↦↓ d)) ≡ pack↓ (scope↑ S c ↦↓ scope↓ S d)
  scope↓-arrow-pack root c d = refl
  scope↓-arrow-pack (allocate S A) c d =
    cong mapPack↓ (scope↓-arrow-pack S c d)

  scope↑-id-pack : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
      (S : PhysicalScope Σ₀ Δ) (A : Ty Δ₀)
    → pack↑ (scope↑ S (id↑ A)) ≡ pack↑ (id↑ (scopeTy S A))
  scope↑-id-pack root A = refl
  scope↑-id-pack (allocate S B) A = cong mapPack↑ (scope↑-id-pack S A)

  scope↓-id-pack : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
      (S : PhysicalScope Σ₀ Δ) (A : Ty Δ₀)
    → pack↓ (scope↓ S (id↓ A)) ≡ pack↓ (id↓ (scopeTy S A))
  scope↓-id-pack root A = refl
  scope↓-id-pack (allocate S B) A = cong mapPack↓ (scope↓-id-pack S A)

  scope↑-unseal-pack : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
      (S : PhysicalScope Σ₀ Δ) (X : TyVar Δ₀) (R : Ty Δ₀)
    → pack↑ (scope↑ S (unseal X R))
      ≡ pack↑ (unseal (scopeVar S X) (scopeTy S R))
  scope↑-unseal-pack root X R = refl
  scope↑-unseal-pack (allocate S A) X R =
    cong mapPack↑ (scope↑-unseal-pack S X R)

  scope↓-seal-pack : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
      (S : PhysicalScope Σ₀ Δ) (X : TyVar Δ₀) (R : Ty Δ₀)
    → pack↓ (scope↓ S (seal X R))
      ≡ pack↓ (seal (scopeVar S X) (scopeTy S R))
  scope↓-seal-pack root X R = refl
  scope↓-seal-pack (allocate S A) X R =
    cong mapPack↓ (scope↓-seal-pack S X R)

scope↑-valid : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀} (S : PhysicalScope Σ₀ Δ)
    {A B} {c : Conv↑ Δ₀ A B}
  → Σ₀ ⊢↑ c
  → scopeStore S ⊢↑ scope↑ S c
scope↑-valid root c⊢ = c⊢
scope↑-valid (allocate S A) c⊢ =
  reveal-renameᵗ StoreRename-suc-bind (scope↑-valid S c⊢)

scope↓-valid : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀} (S : PhysicalScope Σ₀ Δ)
    {A B} {c : Conv↓ Δ₀ A B}
  → Σ₀ ⊢↓ c
  → scopeStore S ⊢↓ scope↓ S c
scope↓-valid root c⊢ = c⊢
scope↓-valid (allocate S A) c⊢ =
  conceal-renameᵗ StoreRename-suc-bind (scope↓-valid S c⊢)

lift-reveal : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    (p : ScopeFuture S T) (M : Term Δ) {A B} (c : Conv↑ Δ₀ A B)
  → liftTerm p (M ↑ scope↑ S c) ≡ liftTerm p M ↑ scope↑ T c
lift-reveal stay M c = refl
lift-reveal {S = S} (grow {A = A} p) M c =
  trans
    (cong (liftTerm p)
      (cong (apply↑ (⇑ᵗᵐ M))
        (reveal-pointwise (toRenameᵗ wk↪ᵗ) Fin.suc
          toRename-wk-eq (scope↑ S c))))
    (lift-reveal p (⇑ᵗᵐ M) c)

lift-conceal : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    (p : ScopeFuture S T) (M : Term Δ) {A B} (c : Conv↓ Δ₀ A B)
  → liftTerm p (M ↓ scope↓ S c) ≡ liftTerm p M ↓ scope↓ T c
lift-conceal stay M c = refl
lift-conceal {S = S} (grow {A = A} p) M c =
  trans
    (cong (liftTerm p)
      (cong (apply↓ (⇑ᵗᵐ M))
        (conceal-pointwise (toRenameᵗ wk↪ᵗ) Fin.suc
          toRename-wk-eq (scope↓ S c))))
    (lift-conceal p (⇑ᵗᵐ M) c)

open Frame revealFrame using ()
  renaming (transports to reveal-transports)
open Frame concealFrame using ()
  renaming (transports to conceal-transports)

reveal-frame-transport : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    (S : PhysicalScope Σ₀ Δ) (χs : StoreChanges Δ Δ′) {A B}
    (c : Conv↑ Δ₀ A B)
  → reveal-transports χs (reveal-frm (scope↑ S c))
      ≡ reveal-frm (scope↑ (advance S χs) c)
reveal-frame-transport S [] c = refl
reveal-frame-transport S (keep ∷ χs) c =
  trans
    (cong (reveal-transports χs)
      (reveal-frm-pack (rename↑-identity (scope↑ S c))))
    (reveal-frame-transport S χs c)
reveal-frame-transport S (bind A ∷ χs) c =
  reveal-frame-transport (allocate S A) χs c

conceal-frame-transport : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    (S : PhysicalScope Σ₀ Δ) (χs : StoreChanges Δ Δ′) {A B}
    (c : Conv↓ Δ₀ A B)
  → conceal-transports χs (conceal-frm (scope↓ S c))
      ≡ conceal-frm (scope↓ (advance S χs) c)
conceal-frame-transport S [] c = refl
conceal-frame-transport S (keep ∷ χs) c =
  trans
    (cong (conceal-transports χs)
      (conceal-frm-pack (rename↓-identity (scope↓ S c))))
    (conceal-frame-transport S χs c)
conceal-frame-transport S (bind A ∷ χs) c =
  conceal-frame-transport (allocate S A) χs c

scope↑-arrow : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀} (S : PhysicalScope Σ₀ Δ)
    {A A′ B B′} (c : Conv↓ Δ₀ A′ A) (d : Conv↑ Δ₀ B B′)
  → reveal-frm (scope↑ S (c ↦↑ d))
      ≡ reveal-frm (scope↓ S c ↦↑ scope↑ S d)
scope↑-arrow S c d = reveal-frm-pack (scope↑-arrow-pack S c d)

scope↓-arrow : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀} (S : PhysicalScope Σ₀ Δ)
    {A A′ B B′} (c : Conv↑ Δ₀ A′ A) (d : Conv↓ Δ₀ B B′)
  → conceal-frm (scope↓ S (c ↦↓ d))
      ≡ conceal-frm (scope↑ S c ↦↓ scope↓ S d)
scope↓-arrow S c d = conceal-frm-pack (scope↓-arrow-pack S c d)

scope↑-id : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
    (S : PhysicalScope Σ₀ Δ) (A : Ty Δ₀)
  → reveal-frm (scope↑ S (id↑ A)) ≡ reveal-frm (id↑ (scopeTy S A))
scope↑-id S A = reveal-frm-pack (scope↑-id-pack S A)

scope↓-id : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
    (S : PhysicalScope Σ₀ Δ) (A : Ty Δ₀)
  → conceal-frm (scope↓ S (id↓ A)) ≡ conceal-frm (id↓ (scopeTy S A))
scope↓-id S A = conceal-frm-pack (scope↓-id-pack S A)

scope↑-unseal : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
    (S : PhysicalScope Σ₀ Δ) (X : TyVar Δ₀) (R : Ty Δ₀)
  → reveal-frm (scope↑ S (unseal X R))
      ≡ reveal-frm (unseal (scopeVar S X) (scopeTy S R))
scope↑-unseal S X R = reveal-frm-pack (scope↑-unseal-pack S X R)

scope↓-seal : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
    (S : PhysicalScope Σ₀ Δ) (X : TyVar Δ₀) (R : Ty Δ₀)
  → conceal-frm (scope↓ S (seal X R))
      ≡ conceal-frm (seal (scopeVar S X) (scopeTy S R))
scope↓-seal S X R = conceal-frm-pack (scope↓-seal-pack S X R)
