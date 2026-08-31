module proof.LR-narrow.IntegratedLocalNominal where

-- File Charter:
--   * Scope-anchored nominal meaning constructors for the integrated local
--     model.
--   * Paired nominal seals require explicit matched capabilities; precise-only
--     seals require explicit target-only capabilities.
--   * Payload evidence is supplied by an existing anchored Meaning at the same
--     step index. No relation is inferred from store representations.

open import Data.List using ([])
open import Data.Nat using (ℕ; _≤_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂; trans)
  renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
open import Conversion using (seal; ⊢↓-seal)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.IntegratedLocal
import proof.LR-narrow.IntegratedWorld as IW

module LocalNominal {ΔI0 ΔP0} (ΣI0 : TyStore ΔI0)
    (ΣP0 : TyStore ΔP0) where

  module L = Local ΣI0 ΣP0
  open L

  module Wd = IW.Worlds ΣI0 ΣP0
  open Wd

  private
    lift-anchored-seal : ∀ {Δ₀ ΔA ΔI ΔI′} {Σ₀ : TyStore Δ₀}
        {S₀ : PhysicalScope Σ₀ ΔA}
        {S : PhysicalScope Σ₀ ΔI} {S′ : PhysicalScope Σ₀ ΔI′}
      → (p : ScopeFuture S₀ S) → (r : ScopeFuture S S′)
      → (X : TyVar ΔA) → (R : Ty ΔA) → (U : Term ΔI)
      → liftTerm r (U ↓ seal (liftVar p X) (liftTy p R))
          ≡ liftTerm r U ↓ seal (liftVar (scope-trans p r) X)
              (liftTy (scope-trans p r) R)
    lift-anchored-seal p r X R U =
      trans (lift-local-seal r (liftVar p X) (liftTy p R) U)
        (cong₂ (λ Y R′ → liftTerm r U ↓ seal Y R′)
          (sym (lift-var-comp p r X)) (sym (lift-ty-comp p r R)))

    seal-typed : ∀ {Δ₀ ΔA ΔI} {Σ₀ : TyStore Δ₀}
        {S₀ : PhysicalScope Σ₀ ΔA}
        {S : PhysicalScope Σ₀ ΔI} {p : ScopeFuture S₀ S}
        {X : TyVar ΔA} {R : Ty ΔA} {U : Term ΔI}
      → scopeStore S₀ ∋ X ⦂ R
      → ⟨ ΔI , scopeStore S , [] ⟩ ⊢ U ⦂ liftTy p R
      → ⟨ ΔI , scopeStore S , [] ⟩
          ⊢ U ↓ seal (liftVar p X) (liftTy p R) ⦂ liftTy p (＇ X)
    seal-typed {p = p} {X = X} {R = R} {U = U} entry typed =
      subst≡ (λ A → ⟨ _ , _ , [] ⟩
          ⊢ U ↓ seal (liftVar p X) (liftTy p R) ⦂ A)
        (sym (lift-ty-variable p X))
        (⊢conceal (⊢↓-seal (lift-entry p entry)) typed)

    matched-future-anchored : ∀ {ΔA ΔB ΔI ΔP ΔI′ ΔP′}
        {S₀ : PhysicalScope ΣI0 ΔA} {T₀ : PhysicalScope ΣP0 ΔB}
        {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
        {S′ : PhysicalScope ΣI0 ΔI′} {T′ : PhysicalScope ΣP0 ΔP′}
        {W : World S T} {W′ : World S′ T′}
      → (p : ScopeFuture S₀ S) → (q : ScopeFuture T₀ T)
      → (r : ScopeFuture S S′) → (s : ScopeFuture T T′)
      → Future r s W W′ → ∀ {X Y}
      → Matched W (liftVar p X) (liftVar q Y)
      → Matched W′ (liftVar (scope-trans p r) X)
          (liftVar (scope-trans q s) Y)
    matched-future-anchored p q r s ext {X} {Y} m =
      subst≡ (λ X′ → Matched _ X′ (liftVar (scope-trans q s) Y))
        (sym (lift-var-comp p r X))
        (subst≡ (λ Y′ → Matched _ (liftVar r (liftVar p X)) Y′)
          (sym (lift-var-comp q s Y)) (matched-future ext m))

    only-future-anchored : ∀ {ΔB ΔI ΔP ΔI′ ΔP′}
        {T₀ : PhysicalScope ΣP0 ΔB}
        {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
        {S′ : PhysicalScope ΣI0 ΔI′} {T′ : PhysicalScope ΣP0 ΔP′}
        {W : World S T} {W′ : World S′ T′}
      → (q : ScopeFuture T₀ T)
      → (r : ScopeFuture S S′) → (s : ScopeFuture T T′)
      → Future r s W W′
      → ∀ {Y} → PreciseOnly W (liftVar q Y)
      → PreciseOnly W′ (liftVar (scope-trans q s) Y)
    only-future-anchored q r s ext {Y} o =
      subst≡ (λ Y′ → PreciseOnly _ Y′)
        (sym (lift-var-comp q s Y)) (only-future ext o)

  record PairedSealValues {ΔA ΔB ΔI ΔP}
      {S₀ : PhysicalScope ΣI0 ΔA} {T₀ : PhysicalScope ΣP0 ΔB}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {RI : Ty ΔA} {RP : Ty ΔB}
      (A : Meaning S₀ T₀ RI RP)
      (X : TyVar ΔA) (Y : TyVar ΔB)
      (p : ScopeFuture S₀ S) (q : ScopeFuture T₀ T)
      (W : World S T) (k : ℕ) (U : Term ΔI) (V : Term ΔP) : Set where
    constructor paired-seal-values
    field
      payloadI : Term ΔI
      payloadP : Term ΔP
      payload-related : related A p q W k payloadI payloadP
      imprecise-shape :
        U ≡ payloadI ↓ seal (liftVar p X) (liftTy p RI)
      precise-shape :
        V ≡ payloadP ↓ seal (liftVar q Y) (liftTy q RP)
      matched-slot : Matched W (liftVar p X) (liftVar q Y)

  open PairedSealValues public

  paired-seal : ∀ {ΔA ΔB} {S₀ : PhysicalScope ΣI0 ΔA}
      {T₀ : PhysicalScope ΣP0 ΔB} {RI : Ty ΔA} {RP : Ty ΔB}
      (A : Meaning S₀ T₀ RI RP) {X : TyVar ΔA} {Y : TyVar ΔB}
    → scopeStore S₀ ∋ X ⦂ RI → scopeStore T₀ ∋ Y ⦂ RP
    → Meaning S₀ T₀ (＇ X) (＇ Y)
  paired-seal {S₀ = S₀} {T₀ = T₀} {RI = RI} {RP = RP}
      A {X} {Y} entryI entryP = record
    { related = PairedSealValues A X Y
    ; imprecise-value = λ rel →
        subst≡ Value (sym (imprecise-shape rel))
          (imprecise-value A (payload-related rel) ↓ seal)
    ; precise-value = λ rel →
        subst≡ Value (sym (precise-shape rel))
          (precise-value A (payload-related rel) ↓ seal)
    ; imprecise-typed = λ { {S = S} {p = p} rel →
        subst≡ (λ M → ⟨ _ , _ , [] ⟩ ⊢ M ⦂ liftTy p (＇ X))
          (sym (imprecise-shape rel))
          (seal-typed {Σ₀ = ΣI0} {S₀ = S₀} {S = S} {p = p}
            {X = X} {R = RI} entryI
            (imprecise-typed A (payload-related rel))) }
    ; precise-typed = λ { {T = T} {q = q} rel →
        subst≡ (λ M → ⟨ _ , _ , [] ⟩ ⊢ M ⦂ liftTy q (＇ Y))
          (sym (precise-shape rel))
          (seal-typed {Σ₀ = ΣP0} {S₀ = T₀} {S = T} {p = q}
            {X = Y} {R = RP} entryP
            (precise-typed A (payload-related rel))) }
    ; downward = λ j≤k rel → paired-seal-values
        (payloadI rel) (payloadP rel)
        (downward A j≤k (payload-related rel))
        (imprecise-shape rel) (precise-shape rel) (matched-slot rel)
    ; future-closed = λ { {p = p} {q = q} r s ext rel → paired-seal-values
        (liftTerm r (payloadI rel)) (liftTerm s (payloadP rel))
        (future-closed A r s ext (payload-related rel))
        (trans (cong (liftTerm r) (imprecise-shape rel))
          (lift-anchored-seal p r X RI (payloadI rel)))
        (trans (cong (liftTerm s) (precise-shape rel))
          (lift-anchored-seal q s Y RP (payloadP rel)))
        (matched-future-anchored p q r s ext (matched-slot rel)) }
    }

  record PreciseSealValues {ΔA ΔB ΔI ΔP}
      {S₀ : PhysicalScope ΣI0 ΔA} {T₀ : PhysicalScope ΣP0 ΔB}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {AI : Ty ΔA} {RP : Ty ΔB}
      (A : Meaning S₀ T₀ AI RP)
      (Y : TyVar ΔB)
      (p : ScopeFuture S₀ S) (q : ScopeFuture T₀ T)
      (W : World S T) (k : ℕ) (U : Term ΔI) (V : Term ΔP) : Set where
    constructor precise-seal-values
    field
      payloadI : Term ΔI
      payloadP : Term ΔP
      payload-related : related A p q W k payloadI payloadP
      imprecise-shape : U ≡ payloadI
      precise-shape :
        V ≡ payloadP ↓ seal (liftVar q Y) (liftTy q RP)
      precise-only-slot : PreciseOnly W (liftVar q Y)

  open PreciseSealValues public

  precise-seal : ∀ {ΔA ΔB} {S₀ : PhysicalScope ΣI0 ΔA}
      {T₀ : PhysicalScope ΣP0 ΔB} {AI : Ty ΔA} {RP : Ty ΔB}
      (A : Meaning S₀ T₀ AI RP) {Y : TyVar ΔB}
    → scopeStore T₀ ∋ Y ⦂ RP
    → Meaning S₀ T₀ AI (＇ Y)
  precise-seal {T₀ = T₀} {AI = AI} {RP = RP} A {Y} entryP = record
    { related = PreciseSealValues A Y
    ; imprecise-value = λ rel →
        subst≡ Value (sym (imprecise-shape rel))
          (imprecise-value A (payload-related rel))
    ; precise-value = λ rel →
        subst≡ Value (sym (precise-shape rel))
          (precise-value A (payload-related rel) ↓ seal)
    ; imprecise-typed = λ { {p = p} rel →
        subst≡ (λ M → ⟨ _ , _ , [] ⟩ ⊢ M ⦂ liftTy p AI)
          (sym (imprecise-shape rel))
          (imprecise-typed A (payload-related rel)) }
    ; precise-typed = λ { {T = T} {q = q} rel →
        subst≡ (λ M → ⟨ _ , _ , [] ⟩ ⊢ M ⦂ liftTy q (＇ Y))
          (sym (precise-shape rel))
          (seal-typed {Σ₀ = ΣP0} {S₀ = T₀} {S = T} {p = q}
            {X = Y} {R = RP} entryP
            (precise-typed A (payload-related rel))) }
    ; downward = λ j≤k rel → precise-seal-values
        (payloadI rel) (payloadP rel)
        (downward A j≤k (payload-related rel))
        (imprecise-shape rel) (precise-shape rel) (precise-only-slot rel)
    ; future-closed = λ { {q = q} r s ext rel → precise-seal-values
        (liftTerm r (payloadI rel)) (liftTerm s (payloadP rel))
        (future-closed A r s ext (payload-related rel))
        (cong (liftTerm r) (imprecise-shape rel))
        (trans (cong (liftTerm s) (precise-shape rel))
          (lift-anchored-seal q s Y RP (payloadP rel)))
        (only-future-anchored q r s ext (precise-only-slot rel)) }
    }
