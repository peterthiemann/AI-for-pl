module proof.LR-narrow.IntegratedSuite where

-- File Charter:
--   * Shared operational regression suite interpreted by IntegratedModel.
--   * Each checked CTI program pair is observed in imprecise-first order,
--     at every index, preserving any pre-existing nominal world.
--   * These are whole-run observations, NOT primitive cast compatibility.
--     Value-level and producer tests live in their respective proof modules.
--   * Imports retain the earlier nominal/type counterexamples as controls.

open import Data.Nat using (ℕ)
open import Data.Product using (_,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import TyStore
open import CastTerms
open import Reduction
open import Primitives using (κℕ)
open import Interpreter
import Eval as E
open import LR-narrow.LogicalRelation using (same-natural)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.IntegratedModel
import proof.LR-narrow.IntegratedWorld as IW
import proof.LR-narrow.WrapperImprecisionExamples as W
import proof.LR-narrow.DynamicWrapperExamples as D
import proof.LR-narrow.RepeatedCastExamples as C
import proof.LR-narrow.RepeatedSealExamples as S
import proof.LR-narrow.MixedBoundaryExamples as M
import proof.LR-narrow.RepeatedBoundaryControls as N
import proof.LR-narrow.NominalObservationExamples
import proof.LR-narrow.ReplacementImprecisionExamples

module Runs {ΔI ΔP} (ΣI : TyStore ΔI) (ΣP : TyStore ΔP) where

  open Model ΣI ΣP
  open IW.Worlds ΣI ΣP

  natural-runs : ∀ {M N n gasI gasP} (W : World root root) k
    → (∃[ ΔI′ ] ∃[ χI ] ∃[ trI ]
        interpretFrom ΣI gasI M ≡ returned
          (E.result ΔI′ χI ($ (κℕ n)) trI ($ (κℕ n))))
    → (∃[ ΔP′ ] ∃[ χP ] ∃[ trP ]
        interpretFrom ΣP gasP N ≡ returned
          (E.result ΔP′ χP ($ (κℕ n)) trP ($ (κℕ n))))
    → Observed natural W k M N
  natural-runs {n = n} {gasI} {gasP} W k
      (ΔI′ , χI , trI , retI) (ΔP′ , χP , trP , retP) =
    observed-from-returns {gasI = gasI} {gasP = gasP} retI retP
      (advance-world-future W χI χP) (same-natural n)

module Empty = Model store-empty store-empty
module EmptyWorld = IW.Worlds store-empty store-empty
module EmptyRuns = Runs store-empty store-empty
module Chain = Model S.chain-store S.chain-store
module ChainWorld = IW.Worlds S.chain-store S.chain-store
module ChainRuns = Runs S.chain-store S.chain-store
module Named = Model S.one-name-store S.one-name-store
module NamedWorld = IW.Worlds S.one-name-store S.one-name-store
module NamedRuns = Runs S.one-name-store S.one-name-store
module Mixed = Model M.nat-store M.nat-store
module MixedWorld = IW.Worlds M.nat-store M.nat-store
module MixedRuns = Runs M.nat-store M.nat-store
module Decayed = Model M.star-store M.nat-store
module DecayedWorld = IW.Worlds M.star-store M.nat-store
module Controls = Model N.two-names N.two-names
module ControlWorld = IW.Worlds N.two-names N.two-names
module ControlRuns = Runs N.two-names N.two-names

E1 : ∀ (W : EmptyWorld.World root root) n k
  → Empty.Observed Empty.natural W k
      (W.constant-reveal-runtime n) (W.constant-source-runtime n)
E1 W n k = EmptyRuns.natural-runs {gasI = 5} {gasP = 2} W k
  (_ , _ , _ , W.constant-reveal-runtime-return n)
  (_ , _ , _ , W.constant-source-runtime-return n)

E2 : ∀ (W : EmptyWorld.World root root) n k
  → Empty.Observed Empty.natural W k
      (W.identity-reveal-runtime n) (W.identity-source-runtime n)
E2 W n k = EmptyRuns.natural-runs {gasI = 8} {gasP = 4} W k
  (_ , _ , _ , W.identity-reveal-runtime-return n)
  (_ , _ , _ , W.identity-source-runtime-return n)

E3 : ∀ (W : EmptyWorld.World root root) n k
  → Empty.Observed Empty.natural W k
      (W.identity-conceal-runtime n) (W.identity-source-runtime n)
E3 W n k = EmptyRuns.natural-runs {gasI = 16} {gasP = 4} W k
  (W.identity-conceal-runtime-return n)
  (_ , _ , _ , W.identity-source-runtime-return n)

E4 : ∀ (W : EmptyWorld.World root root) n k
  → Empty.Observed Empty.natural W k
      (W.identity-mixed-runtime n) (W.identity-source-runtime n)
E4 W n k = EmptyRuns.natural-runs {gasI = 20} {gasP = 4} W k
  (W.identity-mixed-runtime-return n)
  (_ , _ , _ , W.identity-source-runtime-return n)

E5 : ∀ (W : EmptyWorld.World root root) n k
  → Empty.Observed Empty.natural W k
      (W.higher-runtime n) (W.higher-source-runtime n)
E5 W n k = EmptyRuns.natural-runs {gasI = 16} {gasP = 16} W k
  (W.higher-runtime-return n) (W.higher-source-runtime-return n)

E14 : ∀ (W : EmptyWorld.World root root) n k
  → Empty.Observed Empty.natural W k
      (D.wrapped-check-runtime n) (D.check-runtime n)
E14 W n k = EmptyRuns.natural-runs {gasI = 16} {gasP = 8} W k
  (D.wrapped-check-runtime-return n) (D.check-runtime-return n)

E16 : ∀ (W : EmptyWorld.World root root) n k
  → Empty.Observed Empty.natural W k
      (C.first-order-target n) (C.first-order-source n)
E16 W n k = EmptyRuns.natural-runs {gasI = 40} {gasP = 4} W k
  (C.first-order-target-return n) (C.first-order-source-return n)

E18 : ∀ (W : EmptyWorld.World root root) n k
  → Empty.Observed Empty.natural W k
      (C.poly-cycle-target n) (C.poly-cycle-source n)
E18 W n k = EmptyRuns.natural-runs {gasI = 120} {gasP = 6} W k
  (C.poly-cycle-target-return n) (C.poly-cycle-source-return n)

E19 : ∀ (W : ChainWorld.World root root) n k
  → Chain.Observed Chain.natural W k
      (S.s1-target n) (S.s1-source n)
E19 W n k = ChainRuns.natural-runs {gasI = 30} {gasP = 20} W k
  (S.s1-target-return n) (S.s1-source-return n)

E20 : ∀ (W : NamedWorld.World root root) n k
  → Named.Observed Named.natural W k
      (S.s2-target n) (S.s2-source n)
E20 W n k = NamedRuns.natural-runs {gasI = 24} {gasP = 18} W k
  (S.s2-target-return n) (S.s2-source-return n)

E21 : ∀ (W : NamedWorld.World root root) n k
  → Named.Observed Named.natural W k
      (S.s3-target n) (S.s3-source n)
E21 W n k = NamedRuns.natural-runs {gasI = 50} {gasP = 40} W k
  (S.s3-target-return n) (S.s3-source-return n)

E22 : ∀ (W : MixedWorld.World root root) n k
  → Mixed.Observed Mixed.natural W k
      (M.interleaved-target n) (M.interleaved-source n)
E22 W n k = MixedRuns.natural-runs {gasI = 64} {gasP = 32} W k
  (M.interleaved-target-return n) (M.interleaved-source-return n)

E23 : ∀ (W : MixedWorld.World root root) n k
  → Mixed.Observed Mixed.natural W k
      (M.allocating-target n) (M.allocating-source n)
E23 W n k = MixedRuns.natural-runs {gasI = 128} {gasP = 64} W k
  (M.allocating-target-return n) (M.allocating-source-return n)

N1 : ∀ (W : ControlWorld.World root root) n k
  → Controls.Observed Controls.natural W k
      (N.observe N.X n) (N.observe N.X n)
N1 W n k = ControlRuns.natural-runs {gasI = 64} {gasP = 64} W k
  (N.matching-return n) (N.matching-return n)

E17 : ∀ (W : EmptyWorld.World root root) k
  → Empty.Observed Empty.natural W k
      C.higher-order-target C.higher-order-source
E17 W k = EmptyRuns.natural-runs {gasI = 100} {gasP = 8} W k
  C.higher-order-target-return C.higher-order-source-return

E13 : ∀ (W : EmptyWorld.World root root) n k
  → Empty.Observed Empty.natural W k
      (D.wrapped-payload-runtime n) (D.payload-runtime n)
E13 W n k =
  Empty.observed-from-right-blame {gas = 8} (D.payload-runtime-blame n)

E15 : ∀ (W : EmptyWorld.World root root) n k
  → Empty.Observed Empty.natural W k
      (D.erased-runtime n) (D.payload-runtime n)
E15 W n k =
  Empty.observed-from-right-blame {gas = 8} (D.payload-runtime-blame n)

E24 : ∀ (W : DecayedWorld.World root root) n k
  → Decayed.Observed Decayed.natural W k
      (M.mixed-latent-target n) (M.mixed-latent-source n)
E24 W n k =
  Decayed.observed-from-right-blame {gas = 128} (M.mixed-latent-source-blame n)

N2 : ∀ (W : ControlWorld.World root root) n k
  → Controls.Observed Controls.natural W k
      (N.observe N.Y n) (N.observe N.Y n)
N2 W n k =
  Controls.observed-from-right-blame {gas = 64} (N.mismatching-blame n)
