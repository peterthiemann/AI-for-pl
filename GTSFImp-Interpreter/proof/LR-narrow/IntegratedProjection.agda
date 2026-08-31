module proof.LR-narrow.IntegratedProjection where

-- File Charter:
--   * Proves natural projection compatibility for every related dynamic
--     data value, including matched and precise-only nominal packets.
--   * Uses shared actual tag-step facts, not an assumed cast obligation.
--   * The precise-only branch may blame while the imprecise branch returns.
--     General function/universal payloads and expanded casts are not claimed.

open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import TyStore
open import CastTerms
open import Reduction
open import Primitives using (κℕ)
open import Interpreter
import Consistency as C
import Eval as E
open import proof.LR-narrow.FramePhases using (Frame)
open import proof.LR-narrow.CastPhases using
  (cast-operand-step-question; cast-stuck-step-none; cast-operand-nonvalue)
import proof.LR-narrow.IntegratedFrameComposition as FC
open import LR-narrow.Computation using (BlamesFrom)
open import LR-narrow.LogicalRelation using (same-natural)
open import proof.LR-narrow.GroundTagSteps
open import proof.LR-narrow.StepExpansion using (pure-step-blame-expand)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.IntegratedModel
import proof.LR-narrow.IntegratedData as ID

natural-projection : ∀ {Δ} {μ : C.Env∼ Δ} → μ C.⊢ ★ ∼ ‵ `ℕ
natural-projection =
  groundProjection (‵ `ℕ) C.★∼ι (C.id (‵ `ℕ)) nonstar-ι

-- Keeping the environment as frame data makes transport through arbitrary
-- allocations explicit, even though the natural ground itself is closed.
naturalQueryFrame : Frame
naturalQueryFrame = record
  { Frm = C.Env∼
  ; plug = λ μ M → M ⟨ natural-projection {μ = μ} ⟩
  ; transport = applyEnv
  ; plug-step = λ
      { μ {χ = keep} step → ξ-⟨⟩ step refl
      ; μ {χ = bind A} step → ξ-⟨⟩ step refl }
  ; plug-step? = λ
      { μ {Σ} {χ = keep} eq → cast-operand-step-question {Σ = Σ} eq
      ; μ {Σ} {χ = bind A} eq → cast-operand-step-question {Σ = Σ} eq }
  ; plug-stuck = λ { μ {Σ} → cast-stuck-step-none {Σ = Σ} }
  ; plug-nonvalue = λ μ → cast-operand-nonvalue
  ; plug-not-blame = λ μ M ()
  ; plug-blame = λ μ → blame-⟨⟩
  ; plug-blame-step? = λ μ → refl
  }

module PacketQueries {Δ0} (Σ0 : TyStore Δ0) where

  open ID.Unary Σ0

  natural-return : ∀ {Δ} {S : PhysicalScope Σ0 Δ}
      {n M} {μ : C.Env∼ Δ}
    → NaturalPacket S n M
    → ∃[ tr ] interpretFrom (scopeStore S) 1
        (M ⟨ natural-projection {μ = μ} ⟩)
        ≡ returned (E.result Δ (keep ∷ []) ($ (κℕ n)) tr ($ (κℕ n)))
  natural-return (ground-packet μ U payload-natural C.ι∼★ refl) = _ , refl

  mismatching-blame : ∀ {Δ} {S : PhysicalScope Σ0 Δ}
      {A n M} {μ : C.Env∼ Δ} {G : Ty Δ}
    → GroundPacket S A n M → (g : Ground G) → (gate : μ C.⊢★∼ G)
    → A ≢ G
    → BlamesFrom (scopeStore S) 1
        (M ⟨ groundProjection g gate (C.idᵍ g) (C.ground-nonstar g) ⟩)
  mismatching-blame {S = S} (ground-packet μ U pl gateU refl)
      g gate different
      with tag-projection-step-view {Σ = scopeStore S}
        (payload-ground pl) g gateU gate (payload-value pl)
  mismatching-blame (ground-packet μ U pl gateU refl) g gate different
      | tag-matched eq step eqStep = ⊥-elim (different eq)
  mismatching-blame {Δ = Δ} {S = S}
      (ground-packet μ U pl gateU refl) g gate different
      | tag-mismatched neq step eqStep =
    pure-step-blame-expand {Σ = scopeStore S} {gas = 0} (λ ())
      (projection-cast-value-none g gate (C.idᵍ g) (C.ground-nonstar g)
        (payload-value pl 《 inj ⦃ Gᵍ = payload-ground pl ⦄
          ⦃ G∼★ = gateU ⦄ ⦃ Gns = C.ground-nonstar (payload-ground pl) ⦄ 》))
      step eqStep
      (Δ , [] , (blame ∎[]) , refl)

module Projections {ΔI0 ΔP0} (ΣI0 : TyStore ΔI0)
    (ΣP0 : TyStore ΔP0) where

  open Model ΣI0 ΣP0
  open Worlds
  open ID.Data ΣI0 ΣP0
  module QueryI = PacketQueries ΣI0
  module QueryP = PacketQueries ΣP0
  module Frames = FC.Composition naturalQueryFrame naturalQueryFrame ΣI0 ΣP0

  natural-query-values : ∀ {ΔI ΔP}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {W : World S T} {k U V} {μI : C.Env∼ ΔI} {μP : C.Env∼ ΔP}
    → related dataDynamic W k U V
    → Observed natural W k
        (U ⟨ natural-projection {μ = μI} ⟩)
        (V ⟨ natural-projection {μ = μP} ⟩)
  natural-query-values {S = S} {T} {μI = μI} {μP}
      (same-natural-tagged p q)
      with QueryI.natural-return {μ = μI} p
         | QueryP.natural-return {μ = μP} q
  natural-query-values {S = S} {T} (same-natural-tagged {n = n} p q)
      | trI , retI | trP , retP =
    observed-from-returns {gasI = 1} {gasP = 1} retI retP
      future-refl (same-natural n)
  natural-query-values {μP = μP} (matched-name-tagged m p q) =
    observed-from-right-blame {gas = 1}
      (QueryP.mismatching-blame {μ = μP} q (‵ `ℕ) C.★∼ι (λ ()))
  natural-query-values {μP = μP} (precise-only-tagged o p q) =
    observed-from-right-blame {gas = 1}
      (QueryP.mismatching-blame {μ = μP} q (‵ `ℕ) C.★∼ι (λ ()))

  natural-query-observed : ∀ {ΔI ΔP}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {W : World S T} {k M N} {μI : C.Env∼ ΔI} {μP : C.Env∼ ΔP}
    → Observed dataDynamic W k M N
    → Observed natural W k
        (M ⟨ natural-projection {μ = μI} ⟩)
        (N ⟨ natural-projection {μ = μP} ⟩)
  natural-query-observed {μI = μI} {μP = μP} =
    Frames.frame-observed μI μP
      (λ χI χP ext j≤k r → natural-query-values r)
