module proof.LR-narrow.ScopedRightFreshBodyCompatibilityExperiment where

-- File Charter:
--   * Concrete right-fresh body regression over one old visible natural name.
--   * Reuses the right-only runtime fixture from
--     `ScopedRightBodyCompatibilityExperiment`; this file adds only the
--     fresh-target visible-environment setup and the canonical API tests.
--   * Exercises canonical reveal/conceal observations at arbitrary
--     independent futures and the shifted generated conversions at a
--     two-allocation target future.

import Consistency as Emb
import Data.Fin as Fin
open import Data.Nat using (zero)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans)

open import Types
open import TyStore
open import CastTerms
open import Conversion using (〖_,_↑_〗; makeConceal)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedConversionTransport
  using (scope↑; scope↓)
open import proof.LR-narrow.TypeRenamingComposition using (pack↑; pack↓)
open import proof.LR-narrow.VisibleEnvironment
open import proof.LR-narrow.ScopedIdentity as SI
import proof.LR-narrow.ScopedBodyInterpretation as BI
import proof.LR-narrow.ScopedConversionCompatibility as CC
import proof.LR-narrow.ScopedRightFreshBodyCompatibility as RFresh
import proof.LR-narrow.ScopedRightBodyConversion as RBC
import proof.LR-narrow.ScopedRightBodyCompatibilityExperiment as Prior
open Prior using (argument-body; fixture-body; one-more-source; two-more-target)

module Old = Model Prior.source-store Prior.source-store

initialEnvironment : VisibleEnvironment Prior.source-store Prior.source-store 1
initialEnvironment = record
  { impreciseNames = Emb.id↪ᵗ
  ; preciseNames = Emb.id↪ᵗ
  ; representation = λ { Fin.zero → Old.natural }
  ; impreciseEntry = λ { Fin.zero → Z∋ refl }
  ; preciseEntry = λ { Fin.zero → Z∋ refl }
  }

module Fresh = RFresh.Fresh initialEnvironment Old.natural
module New = Fresh.R.New
module I = BI.Interpretation Prior.source-store Prior.target-store
module Values = CC.Compatibility Prior.source-store Prior.target-store
module BC = RBC.Conversions Prior.source-store Prior.target-store
module OldI = BI.Interpretation Prior.source-store Prior.source-store

abstract-argument : New.ScopedType
abstract-argument = I.interpret-body argument-body Fresh.extended-meaning

public-argument : New.ScopedType
public-argument = Fresh.R.rebase
  (OldI.interpret-body argument-body
    (OldI.extend-meaning Old.natural (meaning initialEnvironment)))

public-fixture : New.ScopedType
public-fixture = Fresh.R.rebase
  (OldI.interpret-body fixture-body
    (OldI.extend-meaning Old.natural (meaning initialEnvironment)))

abstract-identity-observed : ∀ {Δᴵ Δᴾ}
    {S : PhysicalScope Prior.source-store Δᴵ}
    {T : PhysicalScope Prior.target-store Δᴾ}
    (p : ScopeFuture root S) (q : ScopeFuture root T) k
  → New.ObservedComputations
      (I.interpret-body fixture-body Fresh.extended-meaning)
      S T k (liftTerm p (ƛ (` zero))) (liftTerm q (ƛ (` zero)))
abstract-identity-observed p q k =
  Values.values-observed (I.interpret-body fixture-body Fresh.extended-meaning)
    (New.future-closed
      (I.interpret-body fixture-body Fresh.extended-meaning)
      p q (SI.identity-related abstract-argument k))

public-identity-observed : ∀ {Δᴵ Δᴾ}
    {S : PhysicalScope Prior.source-store Δᴵ}
    {T : PhysicalScope Prior.target-store Δᴾ}
    (p : ScopeFuture root S) (q : ScopeFuture root T) k
  → New.ObservedComputations public-fixture
      S T k (liftTerm p (ƛ (` zero))) (liftTerm q (ƛ (` zero)))
public-identity-observed p q k =
  Values.values-observed public-fixture
    (New.future-closed public-fixture p q
      (Fresh.R.arrow-from
        (OldI.interpret-body argument-body
          (OldI.extend-meaning Old.natural (meaning initialEnvironment)))
        (OldI.interpret-body argument-body
          (OldI.extend-meaning Old.natural (meaning initialEnvironment)))
        (SI.identity-related public-argument k)))

canonical-reveal-identity-observed : ∀ {Δᴵ Δᴾ}
    {S : PhysicalScope Prior.source-store Δᴵ}
    {T : PhysicalScope Prior.target-store Δᴾ}
    (p : ScopeFuture root S) (q : ScopeFuture root T) k
  → New.ObservedComputations public-fixture S T k
      (liftTerm p (ƛ (` zero)))
      (liftTerm q (ƛ (` zero))
        ↑ 〖 scopeVar T Fin.zero , scopeTy T (‵ `ℕ)
            ↑ scopeTy T Prior.fixtureTy 〗)
canonical-reveal-identity-observed p q k =
  Fresh.canonical-reveal-observed fixture-body
    (abstract-identity-observed p q k)

canonical-conceal-identity-observed : ∀ {Δᴵ Δᴾ}
    {S : PhysicalScope Prior.source-store Δᴵ}
    {T : PhysicalScope Prior.target-store Δᴾ}
    (p : ScopeFuture root S) (q : ScopeFuture root T) k
  → New.ObservedComputations
      (I.interpret-body fixture-body Fresh.extended-meaning) S T k
      (liftTerm p (ƛ (` zero)))
      (liftTerm q (ƛ (` zero))
        ↓ makeConceal (scopeVar T Fin.zero)
            (scopeTy T (‵ `ℕ)) (scopeTy T Prior.fixtureTy))
canonical-conceal-identity-observed p q k =
  Fresh.canonical-conceal-observed fixture-body
    (public-identity-observed p q k)

runtime-conversion-agrees : pack↑ (BC.revealᴾ fixture-body Fresh.assignment)
  ≡ pack↑ Prior.target-reveal
runtime-conversion-agrees = trans (Fresh.revealᴾ-generated fixture-body root)
  (sym (cong pack↑ Prior.target-reveal-generated))

revealᴾ-generated-two-more : pack↑
    (scope↑ two-more-target (BC.revealᴾ fixture-body Fresh.assignment))
  ≡ pack↑ 〖 Fin.suc (Fin.suc Fin.zero) , ‵ `ℕ
      ↑ ((＇ Fin.suc (Fin.suc Fin.zero)
            ⇒ ＇ Fin.suc (Fin.suc (Fin.suc Fin.zero))) ⇒
         (＇ Fin.suc (Fin.suc Fin.zero)
            ⇒ ＇ Fin.suc (Fin.suc (Fin.suc Fin.zero)))) 〗
revealᴾ-generated-two-more =
  Fresh.revealᴾ-generated fixture-body two-more-target

concealᴾ-generated-two-more : pack↓
    (scope↓ two-more-target (BC.concealᴾ fixture-body Fresh.assignment))
  ≡ pack↓ (makeConceal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ)
      ((＇ Fin.suc (Fin.suc Fin.zero)
          ⇒ ＇ Fin.suc (Fin.suc (Fin.suc Fin.zero))) ⇒
       (＇ Fin.suc (Fin.suc Fin.zero)
          ⇒ ＇ Fin.suc (Fin.suc (Fin.suc Fin.zero)))))
concealᴾ-generated-two-more =
  Fresh.concealᴾ-generated fixture-body two-more-target

canonical-reveal-identity-mixed : ∀ k
  → New.ObservedComputations public-fixture
      one-more-source two-more-target k (ƛ (` zero))
      ((ƛ (` zero)) ↑ 〖 Fin.suc (Fin.suc Fin.zero) , ‵ `ℕ
        ↑ ((＇ Fin.suc (Fin.suc Fin.zero)
              ⇒ ＇ Fin.suc (Fin.suc (Fin.suc Fin.zero))) ⇒
           (＇ Fin.suc (Fin.suc Fin.zero)
              ⇒ ＇ Fin.suc (Fin.suc (Fin.suc Fin.zero)))) 〗)
canonical-reveal-identity-mixed k =
  canonical-reveal-identity-observed (grow stay) (grow (grow stay)) k
