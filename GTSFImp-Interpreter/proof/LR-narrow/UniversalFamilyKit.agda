open import proof.LR-narrow.RevealStatements

module proof.LR-narrow.UniversalFamilyKit where

-- File Charter:
--   * Discharges the replacement-closure kit: every right-universal
--     value described by endpoints and a bare instantiation chain
--     carries the replacement-closed family stored by the `∀⊑` clause.
--   * Extends a chain by one slot-conversion wrapper (paired, dynamic
--     and inert, in both directions), then iterates along a sequence.
--   * Draws the reveal statements from the completed induction, which
--     no longer mentions the kit, so the construction is well founded.

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Unit using () renaming (tt to unit)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
open import Conversion using (replaceTy; 〖_,_↑_〗; makeConceal)
open import Consistency using (toRenameᵗ)
open import Reduction
import Imprecision as I
open import proof.ImprecisionConsistency using
  (toRenameᵗ-injective; ty-all-injective; subst₂-⊑;
   fin-suc-injective)

open import LR-narrow.World
open import LR-narrow.SlotSequence
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.UniversalFamily
open import LR-narrow.Closure using (value-imprecision-downward-to)
import proof.LR-narrow.Closure as ClosureProof
open import proof.LR-narrow.SlotLifting using
  (slot-imprecise-variable-lift;
   slot-imprecise-rep-lift; lifted-reveal-imprecise;
   lifted-conceal-imprecise; transported-reveal-eq;
   transported-conceal-eq; replace-imprecise-lift)
import proof.LR-narrow.DynamicReveal
open module DynKit = proof.LR-narrow.DynamicReveal using
  (dyn-reveal-endpoints; dyn-conceal-endpoints)
import proof.LR-narrow.AliasReveal
open module AliasKit = proof.LR-narrow.AliasReveal using
  (alias-reveal-endpoints; alias-conceal-endpoints)
open import proof.LR-narrow.AliasUniversalChain using
  (reveal-alias-universal-head; conceal-alias-universal-head)
import proof.LR-narrow.PreciseReveal
open module PreciseKit = proof.LR-narrow.PreciseReveal using
  (precise-reveal-endpoints; precise-conceal-endpoints)
open import proof.LR-narrow.ImprecisionSize using (sizeᵖ)
open import proof.LR-narrow.AliasAvoid using
  (AliasAvoidᵖ; AliasAvoid★ᵖ; alias-avoid★-any;
   star-avoid★ᵖ; subst₂-avoid★;
   alias-avoid★-subst-left; alias-avoid★-subst-rightᵉ)
open import proof.LR-narrow.StarNoOccurrence using
  (replaceTy-absent; renameᵗ-∉ᵗ; renameᵗ-reflects-∉ᵗ;
   replaceTy-self-∉; paired-no-occurrence)
open import proof.LR-narrow.RevealLifting using
  (slot-future; alias-avoid★-lift-center;
   alias-avoid★-lift-dynamic-body; liftImpreciseTy-replace)
open import proof.LR-narrow.ImpreciseReveal using
  (imp-reveal-endpoints; imp-conceal-endpoints;
   imprecise-reveal-value; imprecise-conceal-value;
   lift-center-∉ᵗ)
open import proof.LR-narrow.ImmediateReturn using
  (related-values-return)
open import proof.LR-narrow.FramePhases using (Frame)
open import proof.LR-narrow.FrameComposition
open import proof.LR-narrow.RevealFrames using
  (revealFrame; concealFrame; reveal-frm; conceal-frm)
open import proof.TypeInTermSubst using (rename-openᵗ)

open ImpreciseComposition revealFrame using () renaming
  (imprecise-frame-computations-related to
    reveal-imprecise-composition;
   ImprecisePlugValues to RevealImprecisePlugValues)
open ImpreciseComposition concealFrame using () renaming
  (imprecise-frame-computations-related to
    conceal-imprecise-composition;
   ImprecisePlugValues to ConcealImprecisePlugValues)

∉-all-inv : ∀ {Δ} {X : TyVar Δ} {A : Ty (suc Δ)}
  → X ∉ᵗ `∀ A → Fin.suc X ∉ᵗ A
∉-all-inv (∉-all h) = h

import proof.DGG.CtxImp as CTI
import proof.DGG.CastTermImprecision as CTIR
import proof.LR-narrow.Universal as UniversalProof
open import LR-narrow.TermRelation
open import proof.LR-narrow.RevealStructural using
  (statements-all; revealed-endpoints; concealed-endpoints;
   reveal-right-universal-head;
   conceal-right-universal-head; reveal-right-universal-absent-head;
   conceal-right-universal-absent-head;
   reveal-dyn-universal-head; conceal-dyn-universal-head)

------------------------------------------------------------------------
-- The completed induction, as a below-bundle at every point
------------------------------------------------------------------------

below-all : ∀ (k n : ℕ) → Below k n
below-all k n j m lex = statements-all j m

------------------------------------------------------------------------
-- The chain data is downward closed
------------------------------------------------------------------------

data-downward : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    {nonvar : NonVar Ac} {occurs : Fin.zero ∈ᵗ Ac}
    {p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ} {k : ℕ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvar occurs p₀ Bᴾ Bᴵ (suc k) Vᴵ Vᴾ
  → RightUniversalData W nonvar occurs p₀ Bᴾ Bᴵ k Vᴵ Vᴾ
data-downward d = universal-data
  (data-endpoints d) (data-embedᴾ d) (data-embedᴵ d)
  (proj₂ (data-chain d))

------------------------------------------------------------------------
-- Extending a chain by one paired reveal
------------------------------------------------------------------------

reveal-paired-chain : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
  → AliasAvoidᵖ (Fin.suc (center s)) p₀
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Ac)
  → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Bc)
  → ∀ {Acʳ : Ty (suc Δᶜ)} {Bcʳ : Ty Δᶜ}
      (q₀ : I.instᵐ (impEnv (core W)) I.⊢ Acʳ ⊑ ⇑ᵗ Bcʳ)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvar occurs p₀ B₀ᴾ Bᴵ k Vᴵ Vᴾ
  → RightUniversalsRelated W q₀
      (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ)
      (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) k
      (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗)
      (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B₀ᴾ 〗)
reveal-paired-chain W s nonvar occurs p₀ avoidᵇ sourceᴾ sourceᴵ q₀
    {k = zero} dat = tt
reveal-paired-chain W s nonvar occurs p₀ avoidᵇ sourceᴾ sourceᴵ q₀
    {k = suc m} dat =
  (λ W′ W≼W′ Rᴾ r★ t →
    reveal-right-universal-head W s nonvar occurs p₀ avoidᵇ
      sourceᴾ sourceᴵ
      (below-all (suc m) (suc (sizeᵖ p₀))) ≤-refl dat
      W′ W≼W′ Rᴾ r★ t) ,
  reveal-paired-chain W s nonvar occurs p₀ avoidᵇ sourceᴾ sourceᴵ q₀
    (data-downward dat)

------------------------------------------------------------------------
-- Extending a chain by one paired conceal
------------------------------------------------------------------------

conceal-paired-chain : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    {Acʳ : Ty (suc Δᶜ)} {Bcʳ : Ty Δᶜ}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
    (nonvarʳ : NonVar Acʳ) (occursʳ : Fin.zero ∈ᵗ Acʳ)
    (q₀ : I.instᵐ (impEnv (core W)) I.⊢ Acʳ ⊑ ⇑ᵗ Bcʳ)
  → AliasAvoidᵖ (Fin.suc (center s)) p₀
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Ac)
  → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Bc)
  → (targetᴾ : embedPrecise (core W)
      (`∀ (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ))
      ≡ `∀ Acʳ)
  → (targetᴵ : embedImprecise (core W)
      (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) ≡ Bcʳ)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvarʳ occursʳ q₀
      (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ)
      (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) k Vᴵ Vᴾ
  → RightUniversalsRelated W p₀ B₀ᴾ Bᴵ k
      (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ)
      (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ B₀ᴾ))
conceal-paired-chain W s nonvar occurs p₀ nonvarʳ occursʳ q₀
    avoidᵇ sourceᴾ sourceᴵ targetᴾ targetᴵ {k = zero} dat = tt
conceal-paired-chain W s nonvar occurs p₀ nonvarʳ occursʳ q₀
    avoidᵇ sourceᴾ sourceᴵ targetᴾ targetᴵ {k = suc m} dat =
  (λ W′ W≼W′ Rᴾ r★ t →
    conceal-right-universal-head W s nonvar occurs p₀
      nonvarʳ occursʳ q₀ avoidᵇ sourceᴾ sourceᴵ targetᴾ targetᴵ
      (below-all (suc m) (suc (sizeᵖ p₀))) ≤-refl dat
      W′ W≼W′ Rᴾ r★ t) ,
  conceal-paired-chain W s nonvar occurs p₀ nonvarʳ occursʳ q₀
    avoidᵇ sourceᴾ sourceᴵ targetᴾ targetᴵ (data-downward dat)

------------------------------------------------------------------------
-- Extending a chain by one inert reveal or conceal
------------------------------------------------------------------------

reveal-inert-chain : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Ac)
  → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Bc)
  → (no-occur : slotXᴾ s ∉ᵗ `∀ B₀ᴾ)
  → ∀ {Acʳ : Ty (suc Δᶜ)} {Bcʳ : Ty Δᶜ}
      (q₀ : I.instᵐ (impEnv (core W)) I.⊢ Acʳ ⊑ ⇑ᵗ Bcʳ)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvar occurs p₀ B₀ᴾ Bᴵ k Vᴵ Vᴾ
  → RightUniversalsRelated W q₀
      (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ) Bᴵ k
      Vᴵ (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B₀ᴾ 〗)
reveal-inert-chain W s nonvar occurs p₀ sourceᴾ sourceᴵ no-occur q₀
    {k = zero} dat = tt
reveal-inert-chain W s nonvar occurs p₀ sourceᴾ sourceᴵ no-occur q₀
    {k = suc m} dat =
  (λ W′ W≼W′ Rᴾ r★ t →
    reveal-right-universal-absent-head W s nonvar occurs p₀
      sourceᴾ sourceᴵ no-occur
      (below-all (suc m) (suc (sizeᵖ p₀))) ≤-refl dat
      W′ W≼W′ Rᴾ r★ t) ,
  reveal-inert-chain W s nonvar occurs p₀ sourceᴾ sourceᴵ no-occur q₀
    (data-downward dat)

conceal-inert-chain : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ} {Acʳ : Ty (suc Δᶜ)}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
    (nonvarʳ : NonVar Acʳ) (occursʳ : Fin.zero ∈ᵗ Acʳ)
    (q₀ : I.instᵐ (impEnv (core W)) I.⊢ Acʳ ⊑ ⇑ᵗ Bc)
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Ac)
  → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Bc)
  → (targetᴾ : embedPrecise (core W)
      (`∀ (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ))
      ≡ `∀ Acʳ)
  → (no-occur : slotXᴾ s ∉ᵗ `∀ B₀ᴾ)
  → (agree : Acʳ ≡ Ac)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvarʳ occursʳ q₀
      (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B₀ᴾ) Bᴵ k
      Vᴵ Vᴾ
  → RightUniversalsRelated W p₀ B₀ᴾ Bᴵ k
      Vᴵ (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ B₀ᴾ))
conceal-inert-chain W s nonvar occurs p₀ nonvarʳ occursʳ q₀
    sourceᴾ sourceᴵ targetᴾ no-occur agree {k = zero} dat = tt
conceal-inert-chain W s nonvar occurs p₀ nonvarʳ occursʳ q₀
    sourceᴾ sourceᴵ targetᴾ no-occur agree {k = suc m} dat =
  (λ W′ W≼W′ Rᴾ r★ t →
    conceal-right-universal-absent-head W s nonvar occurs p₀
      nonvarʳ occursʳ q₀ sourceᴾ sourceᴵ targetᴾ no-occur agree
      (below-all (suc m) (suc (sizeᵖ p₀))) ≤-refl dat
      W′ W≼W′ Rᴾ r★ t) ,
  conceal-inert-chain W s nonvar occurs p₀ nonvarʳ occursʳ q₀
    sourceᴾ sourceᴵ targetᴾ no-occur agree (data-downward dat)

------------------------------------------------------------------------
-- Extending a chain by one dynamic reveal or conceal
------------------------------------------------------------------------

reveal-dyn-chain : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (d : DynamicSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Ac)
  → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Bc)
  → ∀ {Acʳ : Ty (suc Δᶜ)} {Bcʳ : Ty Δᶜ}
      (q₀ : I.instᵐ (impEnv (core W)) I.⊢ Acʳ ⊑ ⇑ᵗ Bcʳ)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvar occurs p₀ B₀ᴾ Bᴵ k Vᴵ Vᴾ
  → RightUniversalsRelated W q₀
      (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B₀ᴾ) Bᴵ k
      Vᴵ (Vᴾ ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ `∀ B₀ᴾ 〗)
reveal-dyn-chain W d nonvar occurs p₀ sourceᴾ sourceᴵ q₀
    {k = zero} dat = tt
reveal-dyn-chain W d nonvar occurs p₀ sourceᴾ sourceᴵ q₀
    {k = suc m} dat =
  (λ W′ W≼W′ Rᴾ r★ t →
    reveal-dyn-universal-head W d nonvar occurs p₀
      sourceᴾ sourceᴵ
      (below-all (suc m) (suc (sizeᵖ p₀))) ≤-refl dat
      W′ W≼W′ Rᴾ r★ t) ,
  reveal-dyn-chain W d nonvar occurs p₀ sourceᴾ sourceᴵ q₀
    (data-downward dat)

conceal-dyn-chain : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (d : DynamicSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ} {Acʳ : Ty (suc Δᶜ)}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
    (nonvarʳ : NonVar Acʳ) (occursʳ : Fin.zero ∈ᵗ Acʳ)
    (q₀ : I.instᵐ (impEnv (core W)) I.⊢ Acʳ ⊑ ⇑ᵗ Bc)
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Ac)
  → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Bc)
  → (targetᴾ : embedPrecise (core W)
      (`∀ (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B₀ᴾ))
      ≡ `∀ Acʳ)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvarʳ occursʳ q₀
      (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B₀ᴾ)
      Bᴵ k Vᴵ Vᴾ
  → RightUniversalsRelated W p₀ B₀ᴾ Bᴵ k
      Vᴵ (Vᴾ ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) (`∀ B₀ᴾ))
conceal-dyn-chain W d nonvar occurs p₀ nonvarʳ occursʳ q₀
    sourceᴾ sourceᴵ targetᴾ {k = zero} dat = tt
conceal-dyn-chain W d nonvar occurs p₀ nonvarʳ occursʳ q₀
    sourceᴾ sourceᴵ targetᴾ {k = suc m} dat =
  (λ W′ W≼W′ Rᴾ r★ t →
    conceal-dyn-universal-head W d nonvar occurs p₀
      nonvarʳ occursʳ q₀ sourceᴾ sourceᴵ targetᴾ
      (below-all (suc m) (suc (sizeᵖ p₀))) ≤-refl dat
      W′ W≼W′ Rᴾ r★ t) ,
  conceal-dyn-chain W d nonvar occurs p₀ nonvarʳ occursʳ q₀
    sourceᴾ sourceᴵ targetᴾ (data-downward dat)

------------------------------------------------------------------------
-- Extending a chain by one alias reveal or conceal
------------------------------------------------------------------------

reveal-alias-chain : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (a : AliasSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Ac)
  → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Bc)
  → ∀ {Acʳ : Ty (suc Δᶜ)} {Bcʳ : Ty Δᶜ}
      (q₀ : I.instᵐ (impEnv (core W)) I.⊢ Acʳ ⊑ ⇑ᵗ Bcʳ)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvar occurs p₀ B₀ᴾ Bᴵ k Vᴵ Vᴾ
  → RightUniversalsRelated W q₀
      (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B₀ᴾ) Bᴵ k
      Vᴵ (Vᴾ ↑ 〖 aslotXᴾ a , aslotRᴾ a ↑ `∀ B₀ᴾ 〗)
reveal-alias-chain W a nonvar occurs p₀ sourceᴾ sourceᴵ q₀
    {k = zero} dat = tt
reveal-alias-chain W a nonvar occurs p₀ sourceᴾ sourceᴵ q₀
    {k = suc m} dat =
  (λ W′ W≼W′ Rᴾ r★ t →
    reveal-alias-universal-head W a nonvar occurs p₀ sourceᴾ sourceᴵ
      (below-all (suc m) (suc (sizeᵖ p₀))) ≤-refl dat
      W′ W≼W′ Rᴾ r★ t) ,
  reveal-alias-chain W a nonvar occurs p₀ sourceᴾ sourceᴵ q₀
    (data-downward dat)

conceal-alias-chain : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (a : AliasSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ} {Acʳ : Ty (suc Δᶜ)}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
    (nonvarʳ : NonVar Acʳ) (occursʳ : Fin.zero ∈ᵗ Acʳ)
    (q₀ : I.instᵐ (impEnv (core W)) I.⊢ Acʳ ⊑ ⇑ᵗ Bc)
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Ac)
  → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Bc)
  → (targetᴾ : embedPrecise (core W)
      (`∀ (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B₀ᴾ))
      ≡ `∀ Acʳ)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvarʳ occursʳ q₀
      (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B₀ᴾ)
      Bᴵ k Vᴵ Vᴾ
  → RightUniversalsRelated W p₀ B₀ᴾ Bᴵ k
      Vᴵ (Vᴾ ↓ makeConceal (aslotXᴾ a) (aslotRᴾ a) (`∀ B₀ᴾ))
conceal-alias-chain W a nonvar occurs p₀ nonvarʳ occursʳ q₀
    sourceᴾ sourceᴵ targetᴾ {k = zero} dat = tt
conceal-alias-chain W a nonvar occurs p₀ nonvarʳ occursʳ q₀
    sourceᴾ sourceᴵ targetᴾ {k = suc m} dat =
  (λ W′ W≼W′ Rᴾ r★ t →
    conceal-alias-universal-head W a nonvar occurs p₀
      nonvarʳ occursʳ q₀ sourceᴾ sourceᴵ targetᴾ
      (below-all (suc m) (suc (sizeᵖ p₀))) ≤-refl dat
      W′ W≼W′ Rᴾ r★ t) ,
  conceal-alias-chain W a nonvar occurs p₀ nonvarʳ occursʳ q₀
    sourceᴾ sourceᴵ targetᴾ (data-downward dat)

------------------------------------------------------------------------
-- Avoidance through the right-universal instantiation
------------------------------------------------------------------------

-- The instantiation `openRightBodyImprecision` substitutes the bound
-- variable by the applied representative on the left and discharges
-- it at ★ on the right.  Inherited alias leaves substitute their
-- recorded representatives, so the weakened avoidance transports; the
-- star-discharged copies land below ★ and are exempt.  The transport
-- rebuilds the instantiation with its maps in scope and transfers to
-- the World-built derivation by uniqueness.

open-right-body-avoid★ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {Aᴾ : Ty (suc Δᴾ)} {Aᴵ : Ty Δᴵ} {Rᴾ : Ty Δᴾ} {c : TyVar Δᶜ}
    (body-related : I.instᵐ (impEnv (core W)) I.⊢
      renameᵗ (extᵗ (toRenameᵗ (preciseEmbedding (core W)))) Aᴾ
      ⊑ ⇑ᵗ (embedImprecise (core W) Aᴵ))
    (r★ : impEnv (core W) I.⊢ embedPrecise (core W) Rᴾ ⊑ ★)
  → AliasAvoid★ᵖ (Fin.suc c) body-related
  → AliasAvoid★ᵖ c
      (openRightBodyImprecision {W = W} body-related r★)
open-right-body-avoid★ {W = W} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} {Rᴾ = Rᴾ}
    {c = c} body-related r★ avoid =
  alias-avoid★-any rebuilt
    (openRightBodyImprecision {W = W} body-related r★)
    refl refl rebuilt-avoid
  where
  ρᴾ = toRenameᵗ (preciseEmbedding (core W))
  Rᴾ⋆ = embedPrecise (core W) Rᴾ

  same : ∀ X → impEnv (core W) I.⊢
      singleSubᵗ Rᴾ⋆ X ⊑ singleSubᵗ ★ X
  same Fin.zero = r★
  same (Fin.suc X) = I.X⊑X

  star : ∀ X → I.instᵐ (impEnv (core W)) X ≡ I.X⊑★
    → impEnv (core W) I.⊢ singleSubᵗ Rᴾ⋆ X ⊑ ★
  star Fin.zero eq = r★
  star (Fin.suc X) eq = I.X⊑★ (I.lift-star-inv eq)

  core-subst = subst₂-⊑ same star
    (open-head-alias-map Rᴾ⋆ (λ ())) body-related

  rebuilt : Aᴾ [ Rᴾ ]ᵗ ⊑ᵂ⟨ core W ⟩ Aᴵ
  rebuilt = subst≡
    (λ L → impEnv (core W) I.⊢ L
      ⊑ embedImprecise (core W) Aᴵ)
    (sym (rename-openᵗ ρᴾ Aᴾ Rᴾ))
    (subst≡
      (λ R → impEnv (core W) I.⊢
        renameᵗ (extᵗ ρᴾ) Aᴾ [ Rᴾ⋆ ]ᵗ ⊑ R)
      (shift-openᵗ (embedImprecise (core W) Aᴵ) ★)
      core-subst)

  sa : ∀ X → AliasAvoid★ᵖ c (same X)
  sa Fin.zero = star-avoid★ᵖ r★
  sa (Fin.suc X) = unit

  hav : ∀ X {T} → I.instᵐ (impEnv (core W)) X ≡ I.X⊑ᵗ T
    → Fin.suc c ∉ᵗ T → c ∉ᵗ substᵗ (singleSubᵗ Rᴾ⋆) T
  hav Fin.zero ()
  hav (Fin.suc X) eq c∉T with I.lift-alias-inv eq
  hav (Fin.suc X) eq c∉T | T₀ , mode , refl =
    subst≡ (c ∉ᵗ_) (sym (shift-openᵗ T₀ Rᴾ⋆))
      (renameᵗ-reflects-∉ᵗ Fin.suc T₀ c∉T)

  rebuilt-avoid : AliasAvoid★ᵖ c rebuilt
  rebuilt-avoid =
    alias-avoid★-subst-left (sym (rename-openᵗ ρᴾ Aᴾ Rᴾ))
      (alias-avoid★-subst-rightᵉ
        (shift-openᵗ (embedImprecise (core W) Aᴵ) ★)
        (subst₂-avoid★ same star
          (open-head-alias-map Rᴾ⋆ (λ ()))
          sa hav body-related avoid))

------------------------------------------------------------------------
-- The imprecise-only heads
------------------------------------------------------------------------

-- The precise endpoint is untouched, so no β-step is involved: the
-- source chain's head is taken at the canonical instantiation of the
-- source body, and the imprecise reveal wraps the returned values
-- through the one-sided frame composition.  The center cannot occur
-- in the shared precise endpoint because it cannot occur in the
-- replaced imprecise endpoint (the slot variable is gone and the
-- store binds the representative before the slot exists).

reveal-imprecise-right-head : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
  → AliasAvoid★ᵖ (Fin.suc (center s)) p₀
  → UniShape Bᴵ
  → Fin.suc (center s) ∉ᵗ Ac
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Ac)
  → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Bc)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvar occurs p₀ B₀ᴾ Bᴵ (suc k) Vᴵ Vᴾ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′) (W≼W′ : Future W W′)
      (Rᴾ : Ty Δᴾ′)
      (r★ : impEnv (core W′) I.⊢ embedPrecise (core W′) Rᴾ ⊑ ★)
      (t : liftPreciseBody W≼W′ B₀ᴾ [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩
          liftImpreciseTy W≼W′
            (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ))
  → ComputationsRelated W′
      (PostBindValueRelation
        (future-precise (future-refl {W = W′}) r★) t) (suc k)
      (liftImpreciseTerm W≼W′
        (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗))
      (liftPreciseTerm W≼W′ Vᴾ
        ⦂∀ liftPreciseBody W≼W′ B₀ᴾ [ Rᴾ ])
reveal-imprecise-right-head W s {B₀ᴾ = B₀ᴾ} {Bᴵ = Bᴵ} {Ac = Ac}
    {Bc = Bc} nonvar occurs p₀ avoidᵇ shape no-occurᵇ
    sourceᴾ sourceᴵ {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} dat
    W′ W≼W′ Rᴾ r★ t =
  ClosureProof.computations-related-post-bind-reindex t t
    refl refl (sym (lifted-reveal-imprecise s W≼W′ Vᴵ Bᴵ)) refl
    composed
  where
  s′ = slot-future s W≼W′
  Bᴵ′ = liftImpreciseTy W≼W′ Bᴵ
  Vᴵ′ = liftImpreciseTerm W≼W′ Vᴵ
  Vᴾapp = liftPreciseTerm W≼W′ Vᴾ
    ⦂∀ liftPreciseBody W≼W′ B₀ᴾ [ Rᴾ ]
  shape′ = shape-lift W≼W′ shape
  step = future-precise (future-refl {W = W′}) r★

  base-imp : BodyImprecision W B₀ᴾ Bᴵ
  base-imp = body-imprecision-of nonvar occurs p₀ sourceᴾ sourceᴵ

  imp′ = body-imprecision-future W≼W′ base-imp

  t″ : liftPreciseBody W≼W′ B₀ᴾ [ Rᴾ ]ᵗ ⊑ᵂ⟨ core W′ ⟩ Bᴵ′
  t″ = openRightBodyImprecision {W = W′} (bodyP imp′) r★

  avoid-lift : AliasAvoid★ᵖ (Fin.suc (center s′)) (bodyP imp′)
  avoid-lift = alias-avoid★-any
    (liftCenterDynamicBodyImprecision W≼W′ p₀) (bodyP imp′)
    (trans (cong (liftCenterBody W≼W′)
      (sym (ty-all-injective sourceᴾ)))
      (sym (embedPreciseBody-lift W≼W′ B₀ᴾ)))
    (trans (cong (liftCenterBody W≼W′) (cong ⇑ᵗ (sym sourceᴵ)))
      (trans (liftCenterBody-shift W≼W′
        (embedImprecise (core W) Bᴵ))
        (cong ⇑ᵗ (sym (embedImprecise-lift W≼W′ Bᴵ)))))
    (alias-avoid★-lift-dynamic-body W≼W′ (center s) p₀ avoidᵇ)

  avoid-t″ : AliasAvoid★ᵖ (center s′) t″
  avoid-t″ = open-right-body-avoid★ {W = W′} (bodyP imp′) r★
    avoid-lift

  imprecise-eq : liftImpreciseTy W≼W′
      (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
      ≡ replaceTy (slotXᴵ s′) (slotRᴵ s′) Bᴵ′
  imprecise-eq = trans
    (liftImpreciseTy-replace W≼W′ (slotXᴵ s) (slotRᴵ s) Bᴵ)
    (cong₂ (λ Xv R → replaceTy Xv R Bᴵ′)
      (sym (slot-imprecise-variable-lift s W≼W′))
      (sym (slot-imprecise-rep-lift s W≼W′)))

  no-occur-t″ : center s′ ∉ᵗ
      embedPrecise (core W′) (liftPreciseBody W≼W′ B₀ᴾ [ Rᴾ ]ᵗ)
  no-occur-t″ = paired-no-occurrence (center s′) (mode-eq s′) t
    (subst≡ (center s′ ∉ᵗ_)
      (sym (cong (embedImprecise (core W′)) imprecise-eq))
      (subst≡ (_∉ᵗ embedImprecise (core W′)
          (replaceTy (slotXᴵ s′) (slotRᴵ s′) Bᴵ′))
        (impreciseAligned (atom s′))
        (renameᵗ-∉ᵗ (toRenameᵗ (impreciseEmbedding (core W′)))
          (toRenameᵗ-injective (impreciseEmbedding (core W′)))
          (replaceTy-self-∉ (slotXᴵ s′) (slotRᴵ s′) Bᴵ′
            (store-∋-∉ (impreciseBound (atom s′)))))))

  src-head : ComputationsRelated W′
      (PostBindValueRelation step t″) (suc k) Vᴵ′ Vᴾapp
  src-head = proj₁ (data-chain dat) W′ W≼W′ Rᴾ r★ t″

  plug-values : RevealImprecisePlugValues W′
      (PostBindValueRelation step t″)
      (PostBindValueRelation step t)
      (suc k) (reveal-frm 〖 slotXᴵ s′ , slotRᴵ s′ ↑ Bᴵ′ 〗)
  plug-values {W′ = Wf} W′≼Wf {χsᴾ = χsᴾ} {χsᴵ = χsᴵ}
      storeᴵ storeᴾ termsᴵ termsᴾ {j = i} i≤k
      {Vᴵ = Uᴵ} {Vᴾ = Uᴾ} (b≼Wf , factor , val) =
    related-values-return
      (subst≡ Value (sym term-eq)
        (imprecise-value endpoints-f
          ↑ reveal-value-of (shape-lift W′≼Wf shape′)))
      (precise-value endpoints-f)
      (λ j′ j′≤i → b≼Wf , factor ,
        subst≡
          (λ M → ValueImprecisionᵏ j′ Wf
            (liftCenterImprecision W′≼Wf t) M Uᴾ)
          (sym term-eq)
          (imprecise-reveal-value {k = j′} Wf
            (slot-future s′ W′≼Wf)
            (shape-lift W′≼Wf shape′)
            (liftCenterImprecision W′≼Wf t″)
            (alias-avoid★-lift-center W′≼Wf (center s′) t″
              avoid-t″)
            (lift-center-∉ᵗ W′≼Wf no-occur-t″)
            (embedImprecise-lift W′≼Wf Bᴵ′)
            (liftCenterImprecision W′≼Wf t)
            targetᴵf
            (value-imprecision-downward-to j′≤i val)))
    where
    endpoints-f = ClosureProof.value-imprecision-endpoints
      {W = Wf} {p = liftCenterImprecision W′≼Wf t″} {k = i} val

    term-eq : Frame.plug revealFrame
        (Frame.transports revealFrame χsᴵ
          (reveal-frm 〖 slotXᴵ s′ , slotRᴵ s′ ↑ Bᴵ′ 〗)) Uᴵ
        ≡ Uᴵ ↑ 〖 slotXᴵ (slot-future s′ W′≼Wf)
              , slotRᴵ (slot-future s′ W′≼Wf)
              ↑ liftImpreciseTy W′≼Wf Bᴵ′ 〗
    term-eq = transported-reveal-eq χsᴵ Vᴵ′ (slotXᴵ s′)
      (slotRᴵ s′) Bᴵ′
      (trans (termsᴵ (Vᴵ′ ↑ 〖 slotXᴵ s′ , slotRᴵ s′ ↑ Bᴵ′ 〗))
        (trans (lifted-reveal-imprecise s′ W′≼Wf Vᴵ′ Bᴵ′)
          (cong (λ M → M ↑ _) (sym (termsᴵ Vᴵ′)))))
      Uᴵ

    targetᴵf : embedImprecise (core Wf)
        (replaceTy (slotXᴵ (slot-future s′ W′≼Wf))
          (slotRᴵ (slot-future s′ W′≼Wf))
          (liftImpreciseTy W′≼Wf Bᴵ′))
        ≡ liftCenterTy W′≼Wf
            (embedImprecise (core W′)
              (liftImpreciseTy W≼W′
                (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)))
    targetᴵf = trans
      (cong (embedImprecise (core Wf))
        (replace-imprecise-lift s′ W′≼Wf Bᴵ′))
      (trans
        (embedImprecise-lift W′≼Wf
          (replaceTy (slotXᴵ s′) (slotRᴵ s′) Bᴵ′))
        (cong (liftCenterTy W′≼Wf)
          (cong (embedImprecise (core W′)) (sym imprecise-eq))))

  composed : ComputationsRelated W′
      (PostBindValueRelation step t) (suc k)
      (Vᴵ′ ↑ 〖 slotXᴵ s′ , slotRᴵ s′ ↑ Bᴵ′ 〗) Vᴾapp
  composed = reveal-imprecise-composition
    {R = PostBindValueRelation step t″}
    {S = PostBindValueRelation step t}
    (reveal-frm 〖 slotXᴵ s′ , slotRᴵ s′ ↑ Bᴵ′ 〗) (suc k)
    Vᴵ′ Vᴾapp plug-values src-head

conceal-imprecise-right-head : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    {Acʳ : Ty (suc Δᶜ)} {Bcʳ : Ty Δᶜ}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
    (nonvarʳ : NonVar Acʳ) (occursʳ : Fin.zero ∈ᵗ Acʳ)
    (q₀ : I.instᵐ (impEnv (core W)) I.⊢ Acʳ ⊑ ⇑ᵗ Bcʳ)
  → AliasAvoid★ᵖ (Fin.suc (center s)) p₀
  → UniShape Bᴵ
  → Fin.suc (center s) ∉ᵗ Ac
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Ac)
  → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Bc)
  → (targetᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Acʳ)
  → (targetᴵ : embedImprecise (core W)
      (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) ≡ Bcʳ)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvarʳ occursʳ q₀ B₀ᴾ
      (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) (suc k) Vᴵ Vᴾ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′) (W≼W′ : Future W W′)
      (Rᴾ : Ty Δᴾ′)
      (r★ : impEnv (core W′) I.⊢ embedPrecise (core W′) Rᴾ ⊑ ★)
      (t : liftPreciseBody W≼W′ B₀ᴾ [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseTy W≼W′ Bᴵ)
  → ComputationsRelated W′
      (PostBindValueRelation
        (future-precise (future-refl {W = W′}) r★) t) (suc k)
      (liftImpreciseTerm W≼W′
        (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ))
      (liftPreciseTerm W≼W′ Vᴾ
        ⦂∀ liftPreciseBody W≼W′ B₀ᴾ [ Rᴾ ])
conceal-imprecise-right-head W s {B₀ᴾ = B₀ᴾ} {Bᴵ = Bᴵ} {Ac = Ac}
    {Bc = Bc} nonvar occurs p₀ nonvarʳ occursʳ q₀ avoidᵇ shape
    no-occurᵇ sourceᴾ sourceᴵ targetᴾ targetᴵ
    {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} dat W′ W≼W′ Rᴾ r★ t =
  ClosureProof.computations-related-post-bind-reindex tᶜ t
    refl refl (sym (lifted-conceal-imprecise s W≼W′ Vᴵ Bᴵ)) refl
    composed
  where
  s′ = slot-future s W≼W′
  Bᴵ′ = liftImpreciseTy W≼W′ Bᴵ
  Vᴵ′ = liftImpreciseTerm W≼W′ Vᴵ
  Vᴾapp = liftPreciseTerm W≼W′ Vᴾ
    ⦂∀ liftPreciseBody W≼W′ B₀ᴾ [ Rᴾ ]
  shape′ = shape-lift W≼W′ shape
  step = future-precise (future-refl {W = W′}) r★

  base-imp : BodyImprecision W B₀ᴾ Bᴵ
  base-imp = body-imprecision-of nonvar occurs p₀ sourceᴾ sourceᴵ

  imp′ = body-imprecision-future W≼W′ base-imp

  tᶜ : liftPreciseBody W≼W′ B₀ᴾ [ Rᴾ ]ᵗ ⊑ᵂ⟨ core W′ ⟩ Bᴵ′
  tᶜ = openRightBodyImprecision {W = W′} (bodyP imp′) r★

  base-impʳ : BodyImprecision W B₀ᴾ
      (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
  base-impʳ = body-imprecision-of nonvarʳ occursʳ q₀
    targetᴾ targetᴵ

  impʳ = body-imprecision-future W≼W′ base-impʳ

  t‴ : liftPreciseBody W≼W′ B₀ᴾ [ Rᴾ ]ᵗ ⊑ᵂ⟨ core W′ ⟩
      liftImpreciseTy W≼W′ (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
  t‴ = openRightBodyImprecision {W = W′} (bodyP impʳ) r★

  avoid-lift : AliasAvoid★ᵖ (Fin.suc (center s′)) (bodyP imp′)
  avoid-lift = alias-avoid★-any
    (liftCenterDynamicBodyImprecision W≼W′ p₀) (bodyP imp′)
    (trans (cong (liftCenterBody W≼W′)
      (sym (ty-all-injective sourceᴾ)))
      (sym (embedPreciseBody-lift W≼W′ B₀ᴾ)))
    (trans (cong (liftCenterBody W≼W′) (cong ⇑ᵗ (sym sourceᴵ)))
      (trans (liftCenterBody-shift W≼W′
        (embedImprecise (core W) Bᴵ))
        (cong ⇑ᵗ (sym (embedImprecise-lift W≼W′ Bᴵ)))))
    (alias-avoid★-lift-dynamic-body W≼W′ (center s) p₀ avoidᵇ)

  avoid-tᶜ : AliasAvoid★ᵖ (center s′) tᶜ
  avoid-tᶜ = open-right-body-avoid★ {W = W′} (bodyP imp′) r★
    avoid-lift

  imprecise-eq : liftImpreciseTy W≼W′
      (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
      ≡ replaceTy (slotXᴵ s′) (slotRᴵ s′) Bᴵ′
  imprecise-eq = trans
    (liftImpreciseTy-replace W≼W′ (slotXᴵ s) (slotRᴵ s) Bᴵ)
    (cong₂ (λ Xv R → replaceTy Xv R Bᴵ′)
      (sym (slot-imprecise-variable-lift s W≼W′))
      (sym (slot-imprecise-rep-lift s W≼W′)))

  no-occur-tᶜ : center s′ ∉ᵗ
      embedPrecise (core W′) (liftPreciseBody W≼W′ B₀ᴾ [ Rᴾ ]ᵗ)
  no-occur-tᶜ = paired-no-occurrence (center s′) (mode-eq s′) t‴
    (subst≡ (center s′ ∉ᵗ_)
      (sym (cong (embedImprecise (core W′)) imprecise-eq))
      (subst≡ (_∉ᵗ embedImprecise (core W′)
          (replaceTy (slotXᴵ s′) (slotRᴵ s′) Bᴵ′))
        (impreciseAligned (atom s′))
        (renameᵗ-∉ᵗ (toRenameᵗ (impreciseEmbedding (core W′)))
          (toRenameᵗ-injective (impreciseEmbedding (core W′)))
          (replaceTy-self-∉ (slotXᴵ s′) (slotRᴵ s′) Bᴵ′
            (store-∋-∉ (impreciseBound (atom s′)))))))

  src-head : ComputationsRelated W′
      (PostBindValueRelation step t‴) (suc k) Vᴵ′ Vᴾapp
  src-head = proj₁ (data-chain dat) W′ W≼W′ Rᴾ r★ t‴

  plug-values : ConcealImprecisePlugValues W′
      (PostBindValueRelation step t‴)
      (PostBindValueRelation step tᶜ)
      (suc k)
      (conceal-frm (makeConceal (slotXᴵ s′) (slotRᴵ s′) Bᴵ′))
  plug-values {W′ = Wf} W′≼Wf {χsᴾ = χsᴾ} {χsᴵ = χsᴵ}
      storeᴵ storeᴾ termsᴵ termsᴾ {j = i} i≤k
      {Vᴵ = Uᴵ} {Vᴾ = Uᴾ} (b≼Wf , factor , val) =
    related-values-return
      (subst≡ Value (sym term-eq)
        (imprecise-value endpoints-f
          ↓ conceal-value-of (shape-lift W′≼Wf shape′)))
      (precise-value endpoints-f)
      (λ j′ j′≤i → b≼Wf , factor ,
        subst≡
          (λ M → ValueImprecisionᵏ j′ Wf
            (liftCenterImprecision W′≼Wf tᶜ) M Uᴾ)
          (sym term-eq)
          (imprecise-conceal-value {k = j′} Wf
            (slot-future s′ W′≼Wf)
            (shape-lift W′≼Wf shape′)
            (liftCenterImprecision W′≼Wf tᶜ)
            (alias-avoid★-lift-center W′≼Wf (center s′) tᶜ
              avoid-tᶜ)
            (lift-center-∉ᵗ W′≼Wf no-occur-tᶜ)
            (embedImprecise-lift W′≼Wf Bᴵ′)
            (liftCenterImprecision W′≼Wf t‴)
            targetᴵf
            (value-imprecision-downward-to j′≤i val)))
    where
    endpoints-f = ClosureProof.value-imprecision-endpoints
      {W = Wf} {p = liftCenterImprecision W′≼Wf t‴} {k = i} val

    term-eq : Frame.plug concealFrame
        (Frame.transports concealFrame χsᴵ
          (conceal-frm
            (makeConceal (slotXᴵ s′) (slotRᴵ s′) Bᴵ′))) Uᴵ
        ≡ Uᴵ ↓ makeConceal (slotXᴵ (slot-future s′ W′≼Wf))
              (slotRᴵ (slot-future s′ W′≼Wf))
              (liftImpreciseTy W′≼Wf Bᴵ′)
    term-eq = transported-conceal-eq χsᴵ Vᴵ′ (slotXᴵ s′)
      (slotRᴵ s′) Bᴵ′
      (trans (termsᴵ (Vᴵ′
          ↓ makeConceal (slotXᴵ s′) (slotRᴵ s′) Bᴵ′))
        (trans (lifted-conceal-imprecise s′ W′≼Wf Vᴵ′ Bᴵ′)
          (cong (λ M → M ↓ _) (sym (termsᴵ Vᴵ′)))))
      Uᴵ

    targetᴵf : embedImprecise (core Wf)
        (replaceTy (slotXᴵ (slot-future s′ W′≼Wf))
          (slotRᴵ (slot-future s′ W′≼Wf))
          (liftImpreciseTy W′≼Wf Bᴵ′))
        ≡ liftCenterTy W′≼Wf
            (embedImprecise (core W′)
              (liftImpreciseTy W≼W′
                (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)))
    targetᴵf = trans
      (cong (embedImprecise (core Wf))
        (replace-imprecise-lift s′ W′≼Wf Bᴵ′))
      (trans
        (embedImprecise-lift W′≼Wf
          (replaceTy (slotXᴵ s′) (slotRᴵ s′) Bᴵ′))
        (cong (liftCenterTy W′≼Wf)
          (cong (embedImprecise (core W′)) (sym imprecise-eq))))

  composed : ComputationsRelated W′
      (PostBindValueRelation step tᶜ) (suc k)
      (Vᴵ′ ↓ makeConceal (slotXᴵ s′) (slotRᴵ s′) Bᴵ′) Vᴾapp
  composed = conceal-imprecise-composition
    {R = PostBindValueRelation step t‴}
    {S = PostBindValueRelation step tᶜ}
    (conceal-frm (makeConceal (slotXᴵ s′) (slotRᴵ s′) Bᴵ′))
    (suc k) Vᴵ′ Vᴾapp plug-values src-head

------------------------------------------------------------------------
-- Extending a chain by one imprecise-only reveal or conceal
------------------------------------------------------------------------

reveal-imprecise-chain : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
  → AliasAvoid★ᵖ (Fin.suc (center s)) p₀
  → UniShape Bᴵ
  → Fin.suc (center s) ∉ᵗ Ac
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Ac)
  → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Bc)
  → ∀ {Acʳ : Ty (suc Δᶜ)} {Bcʳ : Ty Δᶜ}
      (q₀ : I.instᵐ (impEnv (core W)) I.⊢ Acʳ ⊑ ⇑ᵗ Bcʳ)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvar occurs p₀ B₀ᴾ Bᴵ k Vᴵ Vᴾ
  → RightUniversalsRelated W q₀ B₀ᴾ
      (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) k
      (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗) Vᴾ
reveal-imprecise-chain W s nonvar occurs p₀ avoidᵇ shape
    no-occurᵇ sourceᴾ sourceᴵ q₀ {k = zero} dat = tt
reveal-imprecise-chain W s nonvar occurs p₀ avoidᵇ shape
    no-occurᵇ sourceᴾ sourceᴵ q₀ {k = suc m} dat =
  (λ W′ W≼W′ Rᴾ r★ t →
    reveal-imprecise-right-head W s nonvar occurs p₀ avoidᵇ
      shape no-occurᵇ sourceᴾ sourceᴵ dat W′ W≼W′ Rᴾ r★ t) ,
  reveal-imprecise-chain W s nonvar occurs p₀ avoidᵇ shape
    no-occurᵇ sourceᴾ sourceᴵ q₀ (data-downward dat)

conceal-imprecise-chain : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    {Acʳ : Ty (suc Δᶜ)} {Bcʳ : Ty Δᶜ}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
    (nonvarʳ : NonVar Acʳ) (occursʳ : Fin.zero ∈ᵗ Acʳ)
    (q₀ : I.instᵐ (impEnv (core W)) I.⊢ Acʳ ⊑ ⇑ᵗ Bcʳ)
  → AliasAvoid★ᵖ (Fin.suc (center s)) p₀
  → UniShape Bᴵ
  → Fin.suc (center s) ∉ᵗ Ac
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Ac)
  → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Bc)
  → (targetᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Acʳ)
  → (targetᴵ : embedImprecise (core W)
      (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) ≡ Bcʳ)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvarʳ occursʳ q₀ B₀ᴾ
      (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ) k Vᴵ Vᴾ
  → RightUniversalsRelated W p₀ B₀ᴾ Bᴵ k
      (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ) Vᴾ
conceal-imprecise-chain W s nonvar occurs p₀ nonvarʳ occursʳ q₀
    avoidᵇ shape no-occurᵇ sourceᴾ sourceᴵ targetᴾ targetᴵ
    {k = zero} dat = tt
conceal-imprecise-chain W s nonvar occurs p₀ nonvarʳ occursʳ q₀
    avoidᵇ shape no-occurᵇ sourceᴾ sourceᴵ targetᴾ targetᴵ
    {k = suc m} dat =
  (λ W′ W≼W′ Rᴾ r★ t →
    conceal-imprecise-right-head W s nonvar occurs p₀
      nonvarʳ occursʳ q₀ avoidᵇ shape no-occurᵇ
      sourceᴾ sourceᴵ targetᴾ targetᴵ dat W′ W≼W′ Rᴾ r★ t) ,
  conceal-imprecise-chain W s nonvar occurs p₀ nonvarʳ occursʳ q₀
    avoidᵇ shape no-occurᵇ sourceᴾ sourceᴵ targetᴾ targetᴵ
    (data-downward dat)

------------------------------------------------------------------------
-- Chain data at an unspecified derivation
------------------------------------------------------------------------

-- Every wrapper step changes the value's imprecision derivation, and
-- the family's statement never mentions it (the chain is phantom in
-- its derivation), so the iteration carries it existentially.

record SomeData {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (Bᴾ : Ty (suc Δᴾ)) (Bᴵ : Ty Δᴵ) (k : ℕ)
    (Vᴵ : Term Δᴵ) (Vᴾ : Term Δᴾ) : Set where
  constructor some-data
  field
    someImp : BodyImprecision W Bᴾ Bᴵ
    someBody : RightUniversalData W
      (bodyNonvar someImp) (bodyOccurs someImp) (bodyP someImp)
      Bᴾ Bᴵ k Vᴵ Vᴾ

open SomeData public

------------------------------------------------------------------------
-- One wrapper step
------------------------------------------------------------------------

extend-wrap : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {Bᴾ Bᴾ′ : Ty (suc Δᴾ)} {Bᴵ Bᴵ′ : Ty Δᴵ} {k : ℕ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    (w : UniWrap W Bᴾ Bᴵ Bᴾ′ Bᴵ′)
  → SomeData W Bᴾ Bᴵ k Vᴵ Vᴾ
  → SomeData W Bᴾ′ Bᴵ′ k (wrapTermᴵ₁ w Vᴵ) (wrapTermᴾ₁ w Vᴾ)
extend-wrap {W = W} (reveal-paired s B C sh i av) (some-data j dat) =
  some-data i (universal-data
    (revealed-endpoints W s (I.∀⊑ (bodyNonvar j) (bodyOccurs j)
      (bodyP j)) refl refl
      (I.∀⊑ (bodyNonvar i) (bodyOccurs i) (bodyP i))
      refl refl (data-endpoints dat)
      (imprecise-value (data-endpoints dat) ↑ reveal-value-of sh)
      (precise-value (data-endpoints dat) ↑ all))
    refl refl
    (reveal-paired-chain W s (bodyNonvar j) (bodyOccurs j) (bodyP j)
      (av j) refl refl
      (bodyP i) dat))
extend-wrap {W = W} (conceal-paired s B C sh i av) (some-data j dat) =
  some-data i (universal-data
    (concealed-endpoints W s (I.∀⊑ (bodyNonvar i) (bodyOccurs i)
      (bodyP i)) refl refl
      (I.∀⊑ (bodyNonvar j) (bodyOccurs j) (bodyP j))
      refl refl (data-endpoints dat)
      (imprecise-value (data-endpoints dat) ↓ conceal-value-of sh)
      (precise-value (data-endpoints dat) ↓ all))
    refl refl
    (conceal-paired-chain W s (bodyNonvar i) (bodyOccurs i) (bodyP i)
      (bodyNonvar j) (bodyOccurs j) (bodyP j) (av i)
      refl refl refl refl
      dat))
extend-wrap {W = W} (reveal-dyn d B C i) (some-data j dat) =
  some-data i (universal-data
    (dyn-reveal-endpoints W d (I.∀⊑ (bodyNonvar j) (bodyOccurs j)
      (bodyP j)) refl
      (I.∀⊑ (bodyNonvar i) (bodyOccurs i) (bodyP i))
      refl (data-endpoints dat)
      (precise-value (data-endpoints dat) ↑ all))
    refl refl
    (reveal-dyn-chain W d (bodyNonvar j) (bodyOccurs j) (bodyP j)
      refl refl
      (bodyP i) dat))
extend-wrap {W = W} (conceal-dyn d B C i) (some-data j dat) =
  some-data i (universal-data
    (dyn-conceal-endpoints W d (I.∀⊑ (bodyNonvar i) (bodyOccurs i)
      (bodyP i)) refl
      (I.∀⊑ (bodyNonvar j) (bodyOccurs j) (bodyP j))
      refl (data-endpoints dat)
      (precise-value (data-endpoints dat) ↓ all))
    refl refl
    (conceal-dyn-chain W d (bodyNonvar i) (bodyOccurs i) (bodyP i)
      (bodyNonvar j) (bodyOccurs j) (bodyP j)
      refl refl refl dat))
extend-wrap {W = W} (reveal-alias-slot a B C i) (some-data j dat) =
  some-data i (universal-data
    (alias-reveal-endpoints W a
      (I.∀⊑ (bodyNonvar j) (bodyOccurs j) (bodyP j)) refl
      (I.∀⊑ (bodyNonvar i) (bodyOccurs i) (bodyP i))
      refl (data-endpoints dat)
      (precise-value (data-endpoints dat) ↑ all))
    refl refl
    (reveal-alias-chain W a (bodyNonvar j) (bodyOccurs j) (bodyP j)
      refl refl (bodyP i) dat))
extend-wrap {W = W} (conceal-alias-slot a B C i) (some-data j dat) =
  some-data i (universal-data
    (alias-conceal-endpoints W a
      (I.∀⊑ (bodyNonvar i) (bodyOccurs i) (bodyP i)) refl
      (I.∀⊑ (bodyNonvar j) (bodyOccurs j) (bodyP j))
      refl (data-endpoints dat)
      (precise-value (data-endpoints dat) ↓ all))
    refl refl
    (conceal-alias-chain W a (bodyNonvar i) (bodyOccurs i) (bodyP i)
      (bodyNonvar j) (bodyOccurs j) (bodyP j)
      refl refl refl dat))
extend-wrap {W = W} (reveal-inert s B C avoid i)
    (some-data j dat) =
  some-data j (universal-data
    (precise-reveal-endpoints W s
      (I.∀⊑ (bodyNonvar j) (bodyOccurs j) (bodyP j))
      avoid refl (data-endpoints dat)
      (precise-value (data-endpoints dat) ↑ all))
    refl refl
    (subst≡
      (λ T → RightUniversalsRelated W (bodyP j) T C _
        (wrapTermᴵ₁ (reveal-inert s B C avoid i) _)
        (wrapTermᴾ₁ (reveal-inert s B C avoid i) _))
      absent-eq
      (reveal-inert-chain W s (bodyNonvar j) (bodyOccurs j)
        (bodyP j) refl refl avoid (bodyP j) dat)))
  where
  absent-eq : replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B ≡ B
  absent-eq = replaceTy-absent (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s))
    (∉-all-inv avoid)
extend-wrap {W = W} (conceal-inert s B C avoid i)
    (some-data j dat) =
  some-data j (universal-data
    (precise-conceal-endpoints W s
      (I.∀⊑ (bodyNonvar j) (bodyOccurs j) (bodyP j))
      avoid refl (data-endpoints dat)
      (precise-value (data-endpoints dat) ↓ all))
    refl refl
    (conceal-inert-chain W s (bodyNonvar j) (bodyOccurs j) (bodyP j)
      (bodyNonvar j) (bodyOccurs j) (bodyP j)
      refl refl
      (cong (λ T → embedPrecise (core W) (`∀ T)) absent-eq)
      avoid refl
      (subst≡
        (λ T → RightUniversalData W (bodyNonvar j) (bodyOccurs j)
          (bodyP j) T C _ _ _)
        (sym absent-eq) dat)))
  where
  absent-eq : replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B ≡ B
  absent-eq = replaceTy-absent (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s))
    (∉-all-inv avoid)
extend-wrap {W = W} (reveal-imprecise s B C sh ∉ᵇ i av)
    (some-data j dat) =
  some-data i (universal-data
    (imp-reveal-endpoints W s
      (I.∀⊑ (bodyNonvar j) (bodyOccurs j) (bodyP j)) refl
      (I.∀⊑ (bodyNonvar i) (bodyOccurs i) (bodyP i)) refl
      (data-endpoints dat)
      (imprecise-value (data-endpoints dat)
        ↑ reveal-value-of sh))
    refl refl
    (reveal-imprecise-chain W s (bodyNonvar j) (bodyOccurs j)
      (bodyP j) (av j) sh ∉ᵇ refl refl
      (bodyP i) dat))
extend-wrap {W = W} (conceal-imprecise s B C sh ∉ᵇ i av)
    (some-data j dat) =
  some-data i (universal-data
    (imp-conceal-endpoints W s
      (I.∀⊑ (bodyNonvar i) (bodyOccurs i) (bodyP i)) refl
      (I.∀⊑ (bodyNonvar j) (bodyOccurs j) (bodyP j)) refl
      (data-endpoints dat)
      (imprecise-value (data-endpoints dat)
        ↓ conceal-value-of sh))
    refl refl
    (conceal-imprecise-chain W s (bodyNonvar i) (bodyOccurs i)
      (bodyP i) (bodyNonvar j) (bodyOccurs j) (bodyP j)
      (av i) sh ∉ᵇ refl refl refl refl dat))

endpoints-retype : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {Aᴾ Aᴵ Cᴾ Cᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    (q : impEnv (core W) I.⊢ Cᴾ ⊑ Cᴵ)
  → Aᴾ ≡ Cᴾ → Aᴵ ≡ Cᴵ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → TypedEndpoints W p Vᴵ Vᴾ
  → TypedEndpoints W q Vᴵ Vᴾ
endpoints-retype p q refl refl e =
  ClosureProof.typed-endpoints-derivation-reindex p q e

------------------------------------------------------------------------
-- Iterating along a wrapper sequence
------------------------------------------------------------------------

extend-wraps : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {Bᴾ Bᴾ′ : Ty (suc Δᴾ)} {Bᴵ Bᴵ′ : Ty Δᴵ} {k : ℕ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    (σ : UniWraps W Bᴾ Bᴵ Bᴾ′ Bᴵ′)
  → SomeData W Bᴾ Bᴵ k Vᴵ Vᴾ
  → SomeData W Bᴾ′ Bᴵ′ k (wrapTermᴵ σ Vᴵ) (wrapTermᴾ σ Vᴾ)
extend-wraps [] d = d
extend-wraps (w ∷ σ) d = extend-wraps σ (extend-wrap w d)

------------------------------------------------------------------------
-- The replacement-closure kit
------------------------------------------------------------------------

-- Lifting the chain data to a future world.

data-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    {nonvar : NonVar Ac} {occurs : Fin.zero ∈ᵗ Ac}
    {p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ} {k : ℕ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    (W≼W′ : Future W W′)
  → RightUniversalData W nonvar occurs p₀ Bᴾ Bᴵ k Vᴵ Vᴾ
  → SomeData W′ (liftPreciseBody W≼W′ Bᴾ)
      (liftImpreciseTy W≼W′ Bᴵ) k
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
data-future {W′ = W′} {nonvar = nonvar} {occurs = occurs} {p₀ = p₀}
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} W≼W′ dat = some-data imp′ (universal-data
  (endpoints-retype
    (liftCenterImprecision W≼W′ (I.∀⊑ nonvar occurs p₀))
    (I.∀⊑ (bodyNonvar imp′) (bodyOccurs imp′) (bodyP imp′))
    eqᴾ eqᴵ
    (ClosureProof.typed-endpoints-future W≼W′ (data-endpoints dat)))
  refl refl
  (ClosureProof.right-universals-phantom
    (liftCenterDynamicBodyImprecision W≼W′ p₀) (bodyP imp′)
    (ClosureProof.right-universals-related-future
      {p = p₀} {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} W≼W′ (data-chain dat))))
  where
  eqᴾ = sym (trans
    (cong (embedPrecise (core W′))
      (sym (liftPreciseTy-universal W≼W′ Bᴾ)))
    (trans (embedPrecise-lift W≼W′ (`∀ Bᴾ))
      (cong (liftCenterTy W≼W′) (data-embedᴾ dat))))

  eqᴵ = sym (trans (embedImprecise-lift W≼W′ Bᴵ)
    (cong (liftCenterTy W≼W′) (data-embedᴵ dat)))

  imp′ = body-imprecision-future W≼W′
    (body-imprecision-of nonvar occurs p₀
      (data-embedᴾ dat) (data-embedᴵ dat))

-- The kit itself: iterate the wrapper extensions along the sequence
-- and project the chain, transported to the family's own derivation.

universal-family-kit : RightUniversalFamilyKit
universal-family-kit = record { to-family = family }
  where
  family : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
      {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ} {k : ℕ}
      {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
      {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
      {nonvar : NonVar Ac} {occurs : Fin.zero ∈ᵗ Ac}
      {p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc}
    → RightUniversalData W nonvar occurs p₀ Bᴾ Bᴵ k Vᴵ Vᴾ
    → RightUniversalFamily W p₀ Bᴾ Bᴵ k Vᴵ Vᴾ
  family {p₀ = p₀} dat W≼W′ σ =
    ClosureProof.right-universals-phantom
      (bodyP (someImp (extend-wraps σ (data-future W≼W′ dat))))
      (liftCenterDynamicBodyImprecision W≼W′ p₀)
      (data-chain (someBody (extend-wraps σ (data-future W≼W′ dat))))

------------------------------------------------------------------------
-- The `Λ` introduction no longer needs the kit as an argument
------------------------------------------------------------------------

right-universal-value-compatible : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ : CTI.CtxImp (forgetWorld W)}
    {Aᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {p : Aᴾ CTI.⊑ᵂ⟨
      CTI.liftWorldLeft I.X⊑★ (forgetWorld W) ⟩ Bᴵ}
    {Γ′ : CTI.CtxImp
      (CTI.liftWorldLeft I.X⊑★ (forgetWorld W))}
    {Vᴾ : Term (suc Δᴾ)} {Vᴵ : Term Δᴵ}
  → (nonvar : NonVar Aᴾ)
  → (occurs : Fin.zero ∈ᵗ Aᴾ)
  → (liftΓ : CTI.LiftCtxᴸ I.X⊑★ Γ Γ′)
  → (vVᴾ : Value Vᴾ)
  → (vVᴵ : Value Vᴵ)
  → ⟨ _ , CTI.targetStoreʷ (forgetWorld W) ,
        CTI.tgtCtxʷ Γ ⟩ ⊢ Vᴵ ⦂ Bᴵ
  → CTIR._∣_⊢²_⊑_∶_
      (CTI.liftWorldLeft I.X⊑★ (forgetWorld W)) Γ′ Vᴾ Vᴵ p
  → (q : `∀ Aᴾ ⊑ᵂ⟨ core W ⟩ Bᴵ)
  → (∀ i → i ≤ k →
      CompiledRightUniversalTestRelation {W = W}
        (UniversalProof.right-universal-body-imprecision {W = W} p)
        Aᴾ Bᴵ i Γ Vᴾ Vᴵ)
  → CompiledTermRelation {W = W} q k Γ (Λ Vᴾ) Vᴵ
right-universal-value-compatible =
  UniversalProof.right-universal-value-compatible-from-body
    universal-family-kit
