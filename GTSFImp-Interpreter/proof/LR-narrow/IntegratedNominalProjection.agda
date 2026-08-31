module proof.LR-narrow.IntegratedNominalProjection where

-- File Charter:
--   * Value-level matched nominal projection compatibility for the
--     integrated dataDynamic model.
--   * Queries a matched pair of directly-Nat nominal capabilities, projects
--     dynamic packets with those names, and unseals the successful packet to
--     Nat.
--   * This is intentionally not an alias-chain projection theorem: the query
--     name must have direct Nat representation on both sides.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (yes; no)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import Reduction
open import Primitives using (κℕ)
open import Interpreter
import Consistency as C
import Eval as E
open import LR-narrow.Computation using (BlamesFrom)
open import LR-narrow.LogicalRelation using (groundInjection; same-natural)
open import proof.TypeInTermSubst using (renameᵗ-id)
open import proof.TypeSafety.Progress using (lookup-unique)
open import proof.LR-narrow.GroundTagSteps
open import proof.LR-narrow.Application using
  (prepend-return; value-return-exact; value-unique)
open import proof.LR-narrow.FramePhases using (Frame)
open import proof.LR-narrow.RevealFrames using
  (RevealFrm; revealFrame; reveal-frm)
open import proof.LR-narrow.RevealSteps using (unseal-step-question)
open import proof.LR-narrow.StepExpansion using (pure-step-return-expand)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.IntegratedModel
import proof.LR-narrow.IntegratedData as ID
import proof.LR-narrow.IntegratedProjection as IP

nominal-projection : ∀ {Δ} {μ : C.Env∼ Δ} X
  → μ C.⊢★∼ ＇ X → μ C.⊢ ★ ∼ ＇ X
nominal-projection X gate =
  groundProjection (＇ X) gate (C.idᵍ (＇ X)) (C.ground-nonstar (＇ X))

nominal-nat-query : ∀ {Δ} {μ : C.Env∼ Δ}
  → (X : TyVar Δ) → μ C.⊢★∼ ＇ X → Term Δ → Term Δ
nominal-nat-query X gate M =
  M ⟨ nominal-projection X gate ⟩ ↑ unseal X (‵ `ℕ)

module PacketQueries {Δ0} (Σ0 : TyStore Δ0) where

  open ID.Unary Σ0
  module GroundQuery = IP.PacketQueries Σ0

  private
    unseal-frame-keep : ∀ {Δ} {X : TyVar Δ}
      → Frame.transports revealFrame (keep ∷ [])
          (reveal-frm (unseal X (‵ `ℕ)))
        ≡ reveal-frm (unseal X (‵ `ℕ))
    unseal-frame-keep {Δ = Δ} {X = X}
        rewrite renameᵗ-id {Δ = Δ} (‵ `ℕ) = refl

    matching-unseal-run : ∀ {Δ} {Σ : TyStore Δ} {U : Term Δ} {X}
      → (vU : Value U)
      → interpretFrom Σ 1 ((U ↓ seal X (‵ `ℕ)) ↑ unseal X (‵ `ℕ))
          ≡ returned (E.result Δ (keep ∷ []) U
            (((U ↓ seal X (‵ `ℕ)) ↑ unseal X (‵ `ℕ))
              —→[ keep ]⟨ pure-step (conceal-reveal vU) ⟩ U ∎[]) vU)
    matching-unseal-run {Σ = Σ} {X = X} vU
        with unseal-step-question {Σ = Σ} X (‵ `ℕ) vU
    matching-unseal-run {Σ = Σ} vU | vU′ , step-eq
        rewrite value-unique vU′ vU =
      prepend-return {Σ = Σ} {gas = 0} step-eq
        (value-return-exact {Σ = Σ} 0 vU)

    matching-unseal-frame-run : ∀ {Δ} {Σ : TyStore Δ}
        {U : Term Δ} {X} (f : RevealFrm Δ)
      → f ≡ reveal-frm (unseal X (‵ `ℕ)) → (vU : Value U)
      → ∃[ trace ]
          interpretFrom Σ 1 (Frame.plug revealFrame f
            (U ↓ seal X (‵ `ℕ)))
          ≡ returned (E.result Δ (keep ∷ []) U trace vU)
    matching-unseal-frame-run {Σ = Σ} ._ refl vU =
      _ , matching-unseal-run {Σ = Σ} vU

  matching-return : ∀ {Δ} {S : PhysicalScope Σ0 Δ}
      {X n M} {μ : C.Env∼ Δ}
    → NominalPacket S X n M → scopeStore S ∋ X ⦂ ‵ `ℕ
    → (gate : μ C.⊢★∼ ＇ X)
    → ∃[ gas ] ∃[ tr ] interpretFrom (scopeStore S) gas
        (nominal-nat-query X gate M)
        ≡ returned (E.result Δ (keep ∷ keep ∷ []) ($ (κℕ n)) tr
          ($ (κℕ n)))
  matching-return {S = S} {X = X} {n = n}
      (ground-packet μ ._ (payload-seal actual inner) A∼★ refl)
      entry gate
      with lookup-unique actual entry
  matching-return {S = S} {X = X} {n = n}
      (ground-packet μ ._ (payload-seal actual inner) A∼★ refl)
      entry gate | refl
      with inner
  matching-return {S = S} {X = X} {n = n}
      (ground-packet μ ._ (payload-seal actual payload-natural) A∼★ refl)
      entry gate | refl | payload-natural
      with tag-projection-step-view {Σ = scopeStore S}
        (＇ X) (＇ X) A∼★ gate (($ (κℕ n)) ↓ seal)
  matching-return {S = S} {X = X} {n = n}
      (ground-packet μ ._ (payload-seal actual payload-natural) A∼★ refl)
      entry gate | refl | payload-natural | tag-matched refl step step-eq
      with pure-step-return-expand {Σ = scopeStore S} {gas = 0}
        {M = (($ (κℕ n)) ↓ seal X (‵ `ℕ) ⟨
          groundInjection (＇ X) A∼★ ⟩ ⟨ nominal-projection X gate ⟩)}
        {N = ($ (κℕ n)) ↓ seal X (‵ `ℕ)}
        (λ ()) (projection-cast-value-none (＇ X) gate
          (C.idᵍ (＇ X)) (C.ground-nonstar (＇ X))
          ((($ (κℕ n)) ↓ seal)
            《 inj ⦃ Gᵍ = ＇ X ⦄ ⦃ G∼★ = A∼★ ⦄
              ⦃ Gns = C.ground-nonstar (＇ X) ⦄ 》))
        step step-eq
        (value-return-exact {Σ = scopeStore S} 0 (($ (κℕ n)) ↓ seal))
  matching-return {S = S} {X = X} {n = n}
      (ground-packet μ ._ (payload-seal actual payload-natural) A∼★ refl)
      entry gate | refl | payload-natural | tag-matched refl step step-eq
      | project-ret
      with matching-unseal-frame-run {Σ = scopeStore S} {U = $ (κℕ n)} {X = X}
        (Frame.transports revealFrame (keep ∷ [])
          (reveal-frm (unseal X (‵ `ℕ))))
        unseal-frame-keep ($ (κℕ n))
  matching-return {S = S} {X = X} {n = n}
      (ground-packet μ ._ (payload-seal actual payload-natural) A∼★ refl)
      entry gate | refl | payload-natural | tag-matched refl step step-eq
      | project-ret
      | unseal-trace , unseal-ret
      with Frame.return-expand revealFrame
        {Σ = scopeStore S} {operandGas = suc zero} {callGas = suc zero}
        (reveal-frm (unseal X (‵ `ℕ))) project-ret unseal-ret
  matching-return {S = S} {X = X} {n = n}
      (ground-packet μ ._ (payload-seal actual payload-natural) A∼★ refl)
      entry gate | refl | payload-natural | tag-matched refl step step-eq
      | project-ret
      | unseal-trace , unseal-ret | gas , ret = gas , _ , ret
  matching-return {S = S} {X = X} {n = n}
      (ground-packet μ ._ (payload-seal actual payload-natural) A∼★ refl)
      entry gate | refl | payload-natural | tag-mismatched neq step step-eq =
    ⊥-elim (neq refl)

  mismatch-blame : ∀ {Δ} {S : PhysicalScope Σ0 Δ}
      {A X n M} {μ : C.Env∼ Δ}
    → GroundPacket S A n M → (gate : μ C.⊢★∼ ＇ X)
    → A ≢ ＇ X
    → ∃[ gas ] BlamesFrom (scopeStore S) gas (nominal-nat-query X gate M)
  mismatch-blame {S = S} {X = X} packet gate different =
    Frame.operand-blame-expand revealFrame
      {Σ = scopeStore S} {operandGas = suc zero}
      (reveal-frm (unseal X (‵ `ℕ)))
      (GroundQuery.mismatching-blame packet (＇ X) gate different)

  same-natural-mismatch : ∀ {Δ} {S : PhysicalScope Σ0 Δ}
      {X n M} {μ : C.Env∼ Δ}
    → NaturalPacket S n M → (gate : μ C.⊢★∼ ＇ X)
    → ∃[ gas ] BlamesFrom (scopeStore S) gas (nominal-nat-query X gate M)
  same-natural-mismatch packet gate = mismatch-blame packet gate (λ ())

  nominal-mismatch : ∀ {Δ} {S : PhysicalScope Σ0 Δ}
      {X Y n M} {μ : C.Env∼ Δ}
    → NominalPacket S Y n M → (gate : μ C.⊢★∼ ＇ X)
    → ＇ Y ≢ ＇ X
    → ∃[ gas ] BlamesFrom (scopeStore S) gas (nominal-nat-query X gate M)
  nominal-mismatch packet gate different =
    mismatch-blame packet gate different

module Projections {ΔI0 ΔP0} (ΣI0 : TyStore ΔI0)
    (ΣP0 : TyStore ΔP0) where

  open Model ΣI0 ΣP0
  open Worlds
  open ID.Data ΣI0 ΣP0
  module QI = PacketQueries ΣI0
  module QP = PacketQueries ΣP0

  precise-only-query-different : ∀ {ΔI ΔP}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {W : World S T} {X Y Z}
    → Matched W X Y → PreciseOnly W Z → _≢_ {A = Ty ΔP} (＇ Z) (＇ Y)
  precise-only-query-different m o refl = only-not-matched-at o m

  matched-query-observed : ∀ {ΔI ΔP}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {W : World S T} {k U V X Y}
      {μI : C.Env∼ ΔI} {μP : C.Env∼ ΔP}
    → Matched W X Y
    → scopeStore S ∋ X ⦂ ‵ `ℕ
    → scopeStore T ∋ Y ⦂ ‵ `ℕ
    → (gateI : μI C.⊢★∼ ＇ X)
    → (gateP : μP C.⊢★∼ ＇ Y)
    → related dataDynamic W k U V
    → Observed natural W k
        (nominal-nat-query X gateI U)
        (nominal-nat-query Y gateP V)
  matched-query-observed query entryX entryY gateI gateP
      (same-natural-tagged p q) =
    observed-from-right-blame {gas = gasP} blameP
    where
    gasP = proj₁ (QP.same-natural-mismatch q gateP)
    blameP = proj₂ (QP.same-natural-mismatch q gateP)
  matched-query-observed {S = S} {T} {W} {X = X} {Y = Y}
      query entryX entryY gateI gateP
      (matched-name-tagged {n = n} {X = X′} {Y = Y′} m p q)
      with ＇ Y′ ≟Ty ＇ Y
  matched-query-observed {S = S} {T} {W} {X = X} {Y = Y}
      query entryX entryY gateI gateP
      (matched-name-tagged {n = n} {X = X′} {Y = .Y} m p q)
      | yes refl
      rewrite matched-right-inj m query
      with QI.matching-return p entryX gateI | QP.matching-return q entryY gateP
  matched-query-observed {S = S} {T} {W}
      query entryX entryY gateI gateP
      (matched-name-tagged {n = n} m p q)
      | yes refl | gasI , trI , retI | gasP , trP , retP =
    observed-from-returns {gasI = gasI} {gasP = gasP} retI retP
      future-refl (same-natural n)
  matched-query-observed query entryX entryY gateI gateP
      (matched-name-tagged {Y = Y′} m p q)
      | no different =
    observed-from-right-blame {gas = gasP} blameP
    where
    gasP = proj₁ (QP.nominal-mismatch q gateP different)
    blameP = proj₂ (QP.nominal-mismatch q gateP different)
  matched-query-observed query entryX entryY gateI gateP
      (precise-only-tagged {Y = Y′} o p q) =
    observed-from-right-blame {gas = gasP} blameP
    where
    different = precise-only-query-different query o
    gasP = proj₁ (QP.nominal-mismatch q gateP different)
    blameP = proj₂ (QP.nominal-mismatch q gateP different)
