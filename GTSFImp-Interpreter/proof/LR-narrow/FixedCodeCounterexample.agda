module proof.LR-narrow.FixedCodeCounterexample where

-- File Charter:
--   * Same-endpoint fixed codes need not have interchangeable meanings.
--   * One nominal argument code is inhabited; another conflicts with a
--     persistent match and is empty in every future. Its arrow is vacuous.
--   * Matched nominal packets hide functions returning different naturals;
--     actual matching projection, unseal, and application expose the gap.
--   * Refutes endpoint-only recoding, not exact-code elimination or the live
--     LR. No semantic definition, world rule, or CTI rule is changed.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; ∃-syntax; proj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import CastTerms
open import Conversion using (seal)
open import Primitives using (κℕ)
open import Reduction using (keep; []; _∷_)
open import Interpreter
import Eval as E
open import LR-narrow.LogicalRelation using (SameBaseValue; same-natural)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.IntegratedLocal
open import proof.LR-narrow.IntegratedLocalCodes
import proof.LR-narrow.IntegratedLocalStructure as Structure
import proof.LR-narrow.IntegratedLocalNominal as Nominal
open import proof.LR-narrow.TargetEvaluation using (return-result-unique)
open import proof.LR-narrow.FixedCodeCounterexampleTerms

open Local store-empty store-empty
open Worlds
open Codes store-empty store-empty
open Structure.LocalStructure store-empty store-empty
open Nominal.LocalNominal store-empty store-empty

-- Named slots: X↦Nat, P↦X⇒Nat on the imprecise side; Z↦Nat, Y↦Z,
-- Q↦Y⇒Nat on the precise side. X/Y and P/Q are matched; Z is precise-only.

W : World S T
W = extend-paired
  (extend-paired (extend-only empty (‵ `ℕ)) (‵ `ℕ) (＇ Fin.zero))
  (＇ Fin.zero ⇒ ‵ `ℕ) (＇ Fin.zero ⇒ ‵ `ℕ)

inhabited-argument-code :
  Code S T (＇ (Fin.suc Fin.zero)) (＇ (Fin.suc Fin.zero))
inhabited-argument-code =
  paired-code entryX entryY (precise-code entryZ (base-code `ℕ))

empty-argument-code :
  Code S T (＇ (Fin.suc Fin.zero)) (＇ (Fin.suc Fin.zero))
empty-argument-code =
  precise-code entryY (paired-code entryX entryZ (base-code `ℕ))

arguments-related : ∀ k
  → related (denote inhabited-argument-code) stay stay W k argI argP
arguments-related k = paired-seal-values
  ($ (κℕ 7)) ($ (κℕ 7) ↓ seal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ))
  (precise-seal-values ($ (κℕ 7)) ($ (κℕ 7))
    (same-natural 7) refl refl
    (old-only-paired (old-only-paired new-precise-only)))
  refl refl (old-paired new-paired)

-- The conflicting capability cannot appear even if a future adds other
-- capabilities at unchanged scopes: the old X/Y match must persist.
empty-arguments-in-every-future : ∀ {ΔI ΔP}
    {S′ : PhysicalScope store-empty ΔI}
    {T′ : PhysicalScope store-empty ΔP} {W′ : World S′ T′} {k U V}
  → (p : ScopeFuture S S′) → (q : ScopeFuture T T′)
  → Future p q W W′
  → related (denote empty-argument-code) p q W′ k U V → ⊥
empty-arguments-in-every-future p q ext rel =
  only-not-matched-at (PreciseSealValues.precise-only-slot rel)
    (matched-future ext (old-paired new-paired))

functions-related-vacuously : ∀ k
  → related (denote (arrow-code empty-argument-code (base-code `ℕ)))
      stay stay W k F G
functions-related-vacuously k =
  arrow-values (ƛ ($ (κℕ 0))) (ƛ ($ (κℕ 1))) F-⊢ G-⊢
    (λ p q ext j<k args →
      ⊥-elim (empty-arguments-in-every-future p q ext args))

packet-payload-code : Code S T (＇ Fin.zero) (＇ Fin.zero)
packet-payload-code = paired-code entryP entryQ
  (arrow-code empty-argument-code (base-code `ℕ))

reader-payload-code : Code S T (＇ Fin.zero) (＇ Fin.zero)
reader-payload-code = paired-code entryP entryQ
  (arrow-code inhabited-argument-code (base-code `ℕ))

packet-payload-related : ∀ k
  → related (denote packet-payload-code) stay stay W k sealedF sealedG
packet-payload-related k = paired-seal-values F G
  (functions-related-vacuously k) refl refl new-paired

-- Only the code is chosen existentially. Both nominal endpoints and the
-- interpretation function are fixed, and payload membership is supplied.
existential-packet-payload : ∀ k
  → ∃[ a ] related (denote {AI = ＇ Fin.zero} {AP = ＇ Fin.zero} a)
      stay stay W k sealedF sealedG
existential-packet-payload k = packet-payload-code , packet-payload-related k

-- Positive control: retaining the exact code across the same actual
-- projections preserves all three observations at every index.
projection-preserves-exact-code : ∀ k
  → Observed (denote packet-payload-code) stay stay W k
      source-projection target-projection
projection-preserves-exact-code k = observed-from-returns {gasI = 1} {gasP = 1}
  (proj₂ source-projection-return) (proj₂ target-projection-return)
  future-refl (packet-payload-related k)

different-natural-values : ∀ {ΔI ΔP}
  → SameBaseValue {Δᴾ = ΔP} {Δᴵ = ΔI} `ℕ ($ (κℕ 0)) ($ (κℕ 1)) → ⊥
different-natural-values ()

direct-applications-separate : ∀ {W′ : World S T}
  → Observed (base `ℕ) stay stay W′ 2 direct-source direct-target → ⊥
direct-applications-separate obs
    with direct-source-return | direct-target-return
direct-applications-separate obs | trI , retI | trP , retP
    with Observed.backward-return obs {n = 1}
      {outP = E.result 3 (keep ∷ []) ($ (κℕ 1)) trP ($ (κℕ 1))}
      (s≤s (s≤s z≤n)) retP
direct-applications-separate obs | trI , retI | trP , retP
    | gasI , outI , retI′ , W′ , ext , rel
    with return-result-unique {Σ = scopeStore S}
      {leftGas = gasI} {rightGas = 1} {left = outI}
      {right = E.result 2 (keep ∷ []) ($ (κℕ 0)) trI ($ (κℕ 0))}
      retI′ retI
direct-applications-separate obs | trI , retI | trP , retP
    | gasI , outI , retI′ , W′ , ext , rel | refl =
  different-natural-values rel

reader-functions-rejected : ∀ {W′ : World S T}
  → Future stay stay W W′
  → related (denote (arrow-code inhabited-argument-code (base-code `ℕ)))
      stay stay W′ 3 F G → ⊥
reader-functions-rejected ext rel = direct-applications-separate
  (ArrowValues.call rel stay stay future-refl ≤-refl
    (future-closed (denote inhabited-argument-code) stay stay ext
      (arguments-related 2)))

reader-payload-rejected : ∀ {W′ : World S T}
  → Future stay stay W W′
  → related (denote reader-payload-code) stay stay W′ 3 sealedF sealedG → ⊥
reader-payload-rejected ext (paired-seal-values .F .G rel refl refl m) =
  reader-functions-rejected ext rel

endpoint-recoding-impossible :
  (related (denote packet-payload-code) stay stay W 3 sealedF sealedG
    → related (denote reader-payload-code) stay stay W 3 sealedF sealedG)
  → ⊥
endpoint-recoding-impossible recode =
  reader-payload-rejected future-refl (recode (packet-payload-related 3))

-- Matching nominal tag checks return the original sealed functions. Even
-- allowing arbitrary imprecise fuel and a new future world cannot make those
-- functions belong to the separate reader code at the residual index.
projection-to-reader-impossible :
  Observed (denote reader-payload-code) stay stay W 4
    source-projection target-projection → ⊥
projection-to-reader-impossible obs
    with source-projection-return | target-projection-return
projection-to-reader-impossible obs | trI , retI | trP , retP
    with Observed.backward-return obs {n = 1}
      {outP = E.result 3 (keep ∷ []) sealedG trP sealedG-value}
      (s≤s (s≤s z≤n)) retP
projection-to-reader-impossible obs | trI , retI | trP , retP
    | gasI , outI , retI′ , W′ , ext , rel
    with return-result-unique {Σ = scopeStore S}
      {leftGas = gasI} {rightGas = 1} {left = outI}
      {right = E.result 2 (keep ∷ []) sealedF trI sealedF-value}
      retI′ retI
projection-to-reader-impossible obs | trI , retI | trP , retP
    | gasI , outI , retI′ , W′ , ext , rel | refl =
  reader-payload-rejected ext rel

existential-payload-projection-impossible :
  ((∃[ a ] related (denote {AI = ＇ Fin.zero} {AP = ＇ Fin.zero} a)
      stay stay W 4 sealedF sealedG)
    → Observed (denote reader-payload-code) stay stay W 4
        source-projection target-projection) → ⊥
existential-payload-projection-impossible project =
  projection-to-reader-impossible (project (existential-packet-payload 4))

-- The whole dynamic elimination is distinguishable by data, not merely by
-- observing a higher-order result or failing to construct a semantic proof.
runtime-separates :
  Observed (base `ℕ) stay stay W 4 source-runtime target-runtime → ⊥
runtime-separates obs with source-runtime-return | target-runtime-return
runtime-separates obs | trI , retI | trP , retP
    with Observed.backward-return obs {n = 3}
      {outP = E.result 3 (keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ 1)) trP ($ (κℕ 1))}
      (s≤s (s≤s (s≤s (s≤s z≤n)))) retP
runtime-separates obs | trI , retI | trP , retP
    | gasI , outI , retI′ , W′ , ext , rel
    with return-result-unique {Σ = scopeStore S}
      {leftGas = gasI} {rightGas = 3} {left = outI}
      {right = E.result 2 (keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ 0)) trI ($ (κℕ 0))}
      retI′ retI
runtime-separates obs | trI , retI | trP , retP
    | gasI , outI , retI′ , W′ , ext , rel | refl =
  different-natural-values rel
