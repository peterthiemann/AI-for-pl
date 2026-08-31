module proof.LR-narrow.IntegratedProducer where

-- File Charter:
--   * Relates the dynamic producer's returned adapter functions at
--     Nat ⇒ dataDynamic for all future worlds and related natural arguments.
--   * Proves the natural-instantiation family's endpoint equalities.
--     IntegratedUniversal uses these results to prove concrete membership.
--   * Actual closed universal calls are tested in IntegratedEscapingProducer.
--     No live LR, CTI, or operational rule is changed.

open import Data.List using ([])
open import Data.Nat using (ℕ; suc; _<_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
  renaming (subst to subst≡; subst₂ to subst₂≡)

open import Types
open import TyStore
import Consistency as C
open C using (Env∼; _⊢_∼★)
open import CastTerms
open import Primitives using (κℕ)
open import Interpreter
open import LR-narrow.LogicalRelation using (same-natural)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.IntegratedModel
import proof.LR-narrow.IntegratedData as ID
import proof.LR-narrow.IntegratedWorld as IW
import proof.LR-narrow.IntegratedProducerSteps as PS
open PS using (payload-body)

scope-body-star : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
    (S : PhysicalScope Σ₀ Δ)
  → scopeBody S ★ ≡ ★
scope-body-star root = refl
scope-body-star (allocate S A) =
  cong (renameᵗ (extᵗ Fin.suc)) (scope-body-star S)

module ProducerAt {ΔI0 ΔP0} (ΣI0 : TyStore ΔI0)
    (ΣP0 : TyStore ΔP0) where

  module M = Model ΣI0 ΣP0
  module Wds = IW.Worlds ΣI0 ΣP0
  module Data = ID.Data ΣI0 ΣP0

  open M
  open Wds

  resultI : ∀ {ΔI} (S : PhysicalScope ΣI0 ΔI)
    → scopeTy S (‵ `ℕ ⇒ ★)
        ≡ scopeBody S payload-body [ ‵ `ℕ ]ᵗ
  resultI S
      rewrite scope-arrow S (‵ `ℕ) ★
            | scope-natural S
            | Data.I.scope-star S
            | scope-body-arrow S (＇ Fin.zero) ★
            | scope-body-bound S
            | scope-body-star S = refl

  resultP : ∀ {ΔP} (T : PhysicalScope ΣP0 ΔP)
    → scopeTy T (‵ `ℕ ⇒ ★)
        ≡ scopeBody T payload-body [ ‵ `ℕ ]ᵗ
  resultP T
      rewrite scope-arrow T (‵ `ℕ) ★
            | scope-natural T
            | Data.P.scope-star T
            | scope-body-arrow T (＇ Fin.zero) ★
            | scope-body-bound T
            | scope-body-star T = refl

  payload-family :
    NaturalFamily payload-body payload-body
  payload-family = record
    { result = arrow natural Data.dataDynamic
    ; resultI = resultI
    ; resultP = resultP
    }

  private
    functionI-typed : ∀ {ΔI} {S : PhysicalScope ΣI0 ΔI}
        {X Y : TyVar ΔI} {μ : Env∼ ΔI} {gate : μ ⊢ ＇ Y ∼★}
      → scopeStore S ∋ X ⦂ ‵ `ℕ
      → scopeStore S ∋ Y ⦂ ＇ X
      → ⟨ ΔI , scopeStore S , [] ⟩
          ⊢ PS.two-adapters-function X Y gate
          ⦂ scopeTy S (‵ `ℕ ⇒ ★)
    functionI-typed {S = S} x-entry y-entry =
      subst≡ (λ A → ⟨ _ , scopeStore S , [] ⟩
          ⊢ PS.two-adapters-function _ _ _ ⦂ A)
        (sym eq) (PS.two-adapters-function-⊢ x-entry y-entry)
      where
      eq : scopeTy S (‵ `ℕ ⇒ ★) ≡ (‵ `ℕ ⇒ ★)
      eq rewrite scope-arrow S (‵ `ℕ) ★
               | scope-natural S
               | Data.I.scope-star S = refl

    functionP-typed : ∀ {ΔP} {T : PhysicalScope ΣP0 ΔP}
        {Z : TyVar ΔP} {μ : Env∼ ΔP} {gate : μ ⊢ ＇ Z ∼★}
      → scopeStore T ∋ Z ⦂ ‵ `ℕ
      → ⟨ ΔP , scopeStore T , [] ⟩
          ⊢ PS.one-adapter-function Z gate
          ⦂ scopeTy T (‵ `ℕ ⇒ ★)
    functionP-typed {T = T} z-entry =
      subst≡ (λ A → ⟨ _ , scopeStore T , [] ⟩
          ⊢ PS.one-adapter-function _ _ ⦂ A)
        (sym eq) (PS.one-adapter-function-⊢ z-entry)
      where
      eq : scopeTy T (‵ `ℕ ⇒ ★) ≡ (‵ `ℕ ⇒ ★)
      eq rewrite scope-arrow T (‵ `ℕ) ★
               | scope-natural T
               | Data.P.scope-star T = refl

    source-packet : ∀ {ΔI} {S : PhysicalScope ΣI0 ΔI}
        {X Y : TyVar ΔI} {μ : Env∼ ΔI} {gate : μ ⊢ ＇ Y ∼★} n
      → scopeStore S ∋ X ⦂ ‵ `ℕ
      → scopeStore S ∋ Y ⦂ ＇ X
      → Data.I.NominalPacket S Y n (PS.two-adapters-result X Y gate n)
    source-packet n x-entry y-entry = Data.I.ground-packet _
      _ (Data.I.payload-seal y-entry
        (Data.I.payload-seal x-entry Data.I.payload-natural))
      _ refl

    target-packet : ∀ {ΔP} {T : PhysicalScope ΣP0 ΔP}
        {Z : TyVar ΔP} {μ : Env∼ ΔP} {gate : μ ⊢ ＇ Z ∼★} n
      → scopeStore T ∋ Z ⦂ ‵ `ℕ
      → Data.P.NominalPacket T Z n (PS.one-adapter-result Z gate n)
    target-packet n z-entry = Data.P.ground-packet _
      _ (Data.P.payload-seal z-entry Data.P.payload-natural) _ refl

  adapters-related : ∀ {ΔI ΔP}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {W : World S T} {X Y : TyVar ΔI} {Z : TyVar ΔP}
      {μI : Env∼ ΔI} {μP : Env∼ ΔP}
      {gateI : μI ⊢ ＇ Y ∼★} {gateP : μP ⊢ ＇ Z ∼★}
    → scopeStore S ∋ X ⦂ ‵ `ℕ
    → scopeStore S ∋ Y ⦂ ＇ X
    → scopeStore T ∋ Z ⦂ ‵ `ℕ
    → Matched W Y Z
    → ∀ k
    → related (arrow natural Data.dataDynamic) W k
        (PS.two-adapters-function X Y gateI)
        (PS.one-adapter-function Z gateP)
  adapters-related {S = S} {T} {W} {X} {Y} {Z} {gateI = gateI}
      {gateP = gateP} x-entry y-entry z-entry matched k =
    arrow-values PS.two-adapters-function-value
      PS.one-adapter-function-value
      (functionI-typed x-entry y-entry)
      (functionP-typed z-entry) call
    where
    call : ∀ {ΔI′ ΔP′}
        {S′ : PhysicalScope ΣI0 ΔI′} {T′ : PhysicalScope ΣP0 ΔP′}
        {W′ : World S′ T′} {j U V}
      → (p : ScopeFuture S S′) → (q : ScopeFuture T T′)
      → Future p q W W′ → j < k → related natural W′ j U V
      → Observed Data.dataDynamic W′ j
          (liftTerm p (PS.two-adapters-function X Y gateI) · U)
          (liftTerm q (PS.one-adapter-function Z gateP) · V)
    call {W′ = W′} {j = j} p q ext j<k (same-natural n) =
      subst₂≡ (Observed Data.dataDynamic W′ j) source-eq target-eq
        (observed-from-returns {A = Data.dataDynamic}
          {M = liftTerm p (PS.two-adapters X Y gateI n)}
          {N = liftTerm q (PS.one-adapter Z gateP n)}
          {gasI = 5} {gasP = 3}
          (PS.two-adapters-lift-return n p)
          (PS.one-adapter-lift-return n q)
          future-refl
          (future-closed Data.dataDynamic p q ext
            (Data.matched-name-tagged matched
              (source-packet n x-entry y-entry)
              (target-packet n z-entry))))
      where
      source-eq : liftTerm p (PS.two-adapters X Y gateI n)
        ≡ liftTerm p (PS.two-adapters-function X Y gateI) · $ (κℕ n)
      source-eq = trans
        (PS.lift-application p (PS.two-adapters-function X Y gateI)
          ($ (κℕ n)))
        (cong (liftTerm p (PS.two-adapters-function X Y gateI) ·_)
          (lift-constant p (κℕ n)))

      target-eq : liftTerm q (PS.one-adapter Z gateP n)
        ≡ liftTerm q (PS.one-adapter-function Z gateP) · $ (κℕ n)
      target-eq = trans
        (PS.lift-application q (PS.one-adapter-function Z gateP)
          ($ (κℕ n)))
        (cong (liftTerm q (PS.one-adapter-function Z gateP) ·_)
          (lift-constant q (κℕ n)))

  paired-adapters-related : ∀ {ΔI ΔP}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {W : World S T} {X : TyVar ΔI} {Y : TyVar ΔP}
      {μI : Env∼ ΔI} {μP : Env∼ ΔP}
      {gateI : μI ⊢ ＇ X ∼★} {gateP : μP ⊢ ＇ Y ∼★}
    → scopeStore S ∋ X ⦂ ‵ `ℕ
    → scopeStore T ∋ Y ⦂ ‵ `ℕ
    → Matched W X Y
    → ∀ k
    → related (arrow natural Data.dataDynamic) W k
        (PS.one-adapter-function X gateI)
        (PS.one-adapter-function Y gateP)
  paired-adapters-related {S = S} {T} {W} {X} {Y} {gateI = gateI}
      {gateP = gateP} x-entry y-entry matched k =
    arrow-values PS.one-adapter-function-value
      PS.one-adapter-function-value typedI (functionP-typed y-entry) call
    where
    source-type : scopeTy S (‵ `ℕ ⇒ ★) ≡ (‵ `ℕ ⇒ ★)
    source-type rewrite scope-arrow S (‵ `ℕ) ★
                      | scope-natural S
                      | Data.I.scope-star S = refl

    typedI : ⟨ _ , scopeStore S , [] ⟩
      ⊢ PS.one-adapter-function X gateI ⦂ scopeTy S (‵ `ℕ ⇒ ★)
    typedI = subst≡ (λ A → ⟨ _ , scopeStore S , [] ⟩
        ⊢ PS.one-adapter-function X gateI ⦂ A)
      (sym source-type) (PS.one-adapter-function-⊢ x-entry)

    call : ∀ {ΔI′ ΔP′}
        {S′ : PhysicalScope ΣI0 ΔI′} {T′ : PhysicalScope ΣP0 ΔP′}
        {W′ : World S′ T′} {j U V}
      → (p : ScopeFuture S S′) → (q : ScopeFuture T T′)
      → Future p q W W′ → j < k → related natural W′ j U V
      → Observed Data.dataDynamic W′ j
          (liftTerm p (PS.one-adapter-function X gateI) · U)
          (liftTerm q (PS.one-adapter-function Y gateP) · V)
    call {W′ = W′} {j = j} p q ext j<k (same-natural n) =
      subst₂≡ (Observed Data.dataDynamic W′ j) source-eq target-eq
        (observed-from-returns {A = Data.dataDynamic}
          {M = liftTerm p (PS.one-adapter X gateI n)}
          {N = liftTerm q (PS.one-adapter Y gateP n)}
          {gasI = 3} {gasP = 3}
          (PS.one-adapter-lift-return n p)
          (PS.one-adapter-lift-return n q) future-refl
          (future-closed Data.dataDynamic p q ext
            (Data.matched-name-tagged matched
              (Data.I.ground-packet _ _
                (Data.I.payload-seal x-entry Data.I.payload-natural)
                gateI refl)
              (target-packet n y-entry))))
      where
      source-eq : liftTerm p (PS.one-adapter X gateI n)
        ≡ liftTerm p (PS.one-adapter-function X gateI) · $ (κℕ n)
      source-eq = trans
        (PS.lift-application p (PS.one-adapter-function X gateI)
          ($ (κℕ n)))
        (cong (liftTerm p (PS.one-adapter-function X gateI) ·_)
          (lift-constant p (κℕ n)))

      target-eq : liftTerm q (PS.one-adapter Y gateP n)
        ≡ liftTerm q (PS.one-adapter-function Y gateP) · $ (κℕ n)
      target-eq = trans
        (PS.lift-application q (PS.one-adapter-function Y gateP)
          ($ (κℕ n)))
        (cong (liftTerm q (PS.one-adapter-function Y gateP) ·_)
          (lift-constant q (κℕ n)))
