module proof.LR-narrow.RevealObligationsCounterexample where

-- File Charter:
--   * Refutes the unchanged live RevealObligations package using the
--     already checked inert universal wrapper in ScopeExperiment.
--   * Obtains the required smaller-index statements from the hypothetical
--     package via RevealStructural, then contradicts closure at index six.
--   * This is an obstruction to the old raw-store return interface, not
--     a counterexample to the scoped model or the dynamic gradual guarantee.

open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (refl)

open import Types
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.SlotSequence using (PairedSlot; paired-slot)
open import proof.LR-narrow.RevealStatements
import proof.LR-narrow.RevealStructural as Structural
import proof.LR-narrow.ScopeExperiment as Counterexample

private
  initial-slot : PairedSlot Counterexample.initial
  initial-slot = paired-slot Fin.zero
    (fresh-semantic-atom (core emptyWorld) (‵ `ℕ) (‵ `ℕ) I.ι⊑ι)
    refl refl

reveal-obligations-impossible : RevealObligations → ⊥
reveal-obligations-impossible ob =
  Counterexample.inert-universal-reveal-not-closed
    (RevealObligations.blocked-precise-reveal ob {k = 6} {n = 0}
      (λ j m smaller → Proof.statements-all j m)
      Counterexample.initial initial-slot {B₁ = ‵ `ℕ}
      I.ι⊑ι (∉-all ∉-base) refl)
  where
  module Proof = Structural ob
