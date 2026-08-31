module proof.LR-narrow.IntegratedUniversalExperiments where

-- File Charter:
--   * Regression tests for the Nat-only integrated universal producer
--     interface.
--   * Checks that wrapped instantiation preserves old matched/precise-only
--     capabilities, that the universal value relation is exercised through
--     NaturalUniversalValues.instantiate after unequal futures, and that the
--     concrete emitted nominal packets can be decoded operationally.
--   * This file does not claim arbitrary type instantiation, arbitrary
--     universal bodies, or general alias-query compatibility.

open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ; zero; suc; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; proj₂; ∃-syntax)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import TermCtx using (Z)
import Consistency as C
open C using (Env∼; _⊢_∼★)
open import CastTerms
open import Conversion
open import Reduction
open import Primitives using (κℕ)
open import Interpreter
import Eval as E
open import LR-narrow.LogicalRelation using (same-natural; groundInjection)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.IntegratedModel
import proof.LR-narrow.IntegratedWorld as IW
import proof.LR-narrow.IntegratedProducer as Producer
import proof.LR-narrow.IntegratedProducerSteps as PS
import proof.LR-narrow.IntegratedUniversal as IU
import proof.LR-narrow.IntegratedUniversalSteps as US
import proof.LR-narrow.DynamicWrapperExamples as D

module Empty = Model store-empty store-empty
module Wds = IW.Worlds store-empty store-empty
module Universals = IU.Universals store-empty store-empty
module ProducerAt = Producer.ProducerAt store-empty store-empty

open Empty
open Wds
open ProducerAt using (payload-family)

-- A nonempty starting world with one old matched name and one old
-- precise-only target name.  The wrapped producer then allocates two source
-- names and one target name; this test makes sure those old facts are not
-- dropped when the fresh Y/Z producer match is installed.

matched-source : PhysicalScope store-empty 1
matched-source = allocate root (‵ `ℕ)

matched-target : PhysicalScope store-empty 1
matched-target = allocate root (‵ `ℕ)

nonempty-source : PhysicalScope store-empty 1
nonempty-source = matched-source

nonempty-target : PhysicalScope store-empty 2
nonempty-target = allocate matched-target (‵ `ℕ)

nonempty-world : World nonempty-source nonempty-target
nonempty-world = extend-only-nat (extend-paired empty (‵ `ℕ) (‵ `ℕ))

old-match : Matched nonempty-world Fin.zero (Fin.suc Fin.zero)
old-match = old-only-nat-match new-paired

old-only : PreciseOnly nonempty-world Fin.zero
old-only = new-precise-only-nat

wrapped-postworld :
  World (allocate (allocate nonempty-source (‵ `ℕ)) (＇ Fin.zero))
        (allocate nonempty-target (‵ `ℕ))
wrapped-postworld =
  extend-paired (extend-privateI nonempty-world (‵ `ℕ))
    (＇ Fin.zero) (‵ `ℕ)

old-match-survives-wrapped :
  Matched wrapped-postworld
    (Fin.suc (Fin.suc Fin.zero)) (Fin.suc (Fin.suc Fin.zero))
old-match-survives-wrapped =
  matched-future (Universals.wrapped-instantiation-future nonempty-world)
    old-match

old-only-survives-wrapped :
  PreciseOnly wrapped-postworld (Fin.suc Fin.zero)
old-only-survives-wrapped =
  only-future (Universals.wrapped-instantiation-future nonempty-world)
    old-only

fresh-match-wrapped :
  Matched wrapped-postworld Fin.zero Fin.zero
fresh-match-wrapped = new-paired

-- The universal relation must be exercised through the NaturalUniversalValues
-- eliminator, after independent future growth.  This remains Nat-only:
-- instantiation is fixed at ℕ and the result family is payload-body[ℕ].

left-future-scope : PhysicalScope store-empty 1
left-future-scope = allocate root (‵ `ℕ)

right-future-scope : PhysicalScope store-empty 2
right-future-scope = allocate (allocate root (‵ `ℕ)) ★

future-world : World left-future-scope right-future-scope
future-world =
  extend-privateP (extend-paired empty (‵ `ℕ) (‵ `ℕ)) ★

future-from-root :
  Future (grow stay) (grow (grow stay))
    (empty {S = root} {T = root}) future-world
future-from-root = record
  { matched-future = λ ()
  ; only-future = λ ()
  }

left-grow : ScopeFuture root left-future-scope
left-grow = grow stay

right-grow : ScopeFuture root right-future-scope
right-grow = grow (grow stay)

base-gate : C.instᵐ (C.idᶜ {0}) ⊢ ＇ Fin.zero ∼★
base-gate = C.X∼★ᵍ refl

original-producer-related : ∀ k
  → related (naturalUniversal payload-family) (empty {S = root} {T = root}) k
      D.payload-function D.payload-function
original-producer-related k =
  Universals.producer-related {W = empty {S = root} {T = root}}
    {gateI = base-gate} {gateP = base-gate} k

original-wrapper-related : ∀ k
  → related (naturalUniversal payload-family) (empty {S = root} {T = root}) k
      (D.payload-function ↑ D.payload-reveal) D.payload-function
original-wrapper-related k =
  Universals.wrapper-related {W = empty {S = root} {T = root}}
    {gateI = base-gate} {gateP = base-gate} k

wrapped-universal-instantiates-after-unequal-futures : ∀ k
  → Observed (arrow natural ProducerAt.Data.dataDynamic) future-world k
      (liftTerm left-grow (US.wrapped-producer-function base-gate)
        ⦂∀ scopeBody left-future-scope PS.payload-body [ ‵ `ℕ ])
      (liftTerm right-grow (US.producer-function base-gate)
        ⦂∀ scopeBody right-future-scope PS.payload-body [ ‵ `ℕ ])
wrapped-universal-instantiates-after-unequal-futures k =
  NaturalUniversalValues.instantiate
    (Universals.wrapper-related {W = empty {S = root} {T = root}}
      {gateI = base-gate} {gateP = base-gate} (suc k))
    left-grow right-grow future-from-root (s≤s ≤-refl)

producer-universal-instantiates-after-unequal-futures : ∀ k
  → Observed (arrow natural ProducerAt.Data.dataDynamic) future-world k
      (liftTerm left-grow (US.producer-function base-gate)
        ⦂∀ scopeBody left-future-scope PS.payload-body [ ‵ `ℕ ])
      (liftTerm right-grow (US.producer-function base-gate)
        ⦂∀ scopeBody right-future-scope PS.payload-body [ ‵ `ℕ ])
producer-universal-instantiates-after-unequal-futures k =
  NaturalUniversalValues.instantiate
    (Universals.producer-related {W = empty {S = root} {T = root}}
      {gateI = base-gate} {gateP = base-gate} (suc k))
    left-grow right-grow future-from-root (s≤s ≤-refl)

-- Operational packet decoders for the actual values returned by the producer
-- instantiations.  The source packet is tagged at Y and then unsealed through
-- Y↦X and X↦Nat.  The target packet is tagged at Z and unsealed through
-- Z↦Nat.  These are concrete evaluator checks, not a general nominal-query
-- theorem for alias-chain query types.

sourceY? : C.genᵐ (C.idᶜ {1}) C.⊢ ★ ∼ ＇ Fin.zero
sourceY? = C.？ (C.id (＇ Fin.zero))

targetZ? : C.genᵐ (C.idᶜ {0}) C.⊢ ★ ∼ ＇ Fin.zero
targetZ? = C.？ (C.id (＇ Fin.zero))

source-packet-gate :
  C.renameEnv∼ (C.keep C.wk↪ᵗ) (C.instᵐ (C.idᶜ {0}))
    ⊢ ＇ Fin.zero ∼★
source-packet-gate = C.X∼★ᵍ refl

target-packet-gate : C.instᵐ (C.idᶜ {0}) ⊢ ＇ Fin.zero ∼★
target-packet-gate = C.X∼★ᵍ refl

source-emitted-packet : ℕ → Term (suc (suc zero))
source-emitted-packet n =
  PS.two-adapters-result (Fin.suc Fin.zero) Fin.zero source-packet-gate n

target-emitted-packet : ℕ → Term (suc zero)
target-emitted-packet n =
  PS.one-adapter-result Fin.zero target-packet-gate n

source-query-scope : PhysicalScope store-empty (suc (suc zero))
source-query-scope = allocate (allocate root (‵ `ℕ)) (＇ Fin.zero)

target-query-scope : PhysicalScope store-empty (suc zero)
target-query-scope = allocate root (‵ `ℕ)

source-alias-query : ℕ → Term (suc (suc zero))
source-alias-query n =
  ((source-emitted-packet n
      ⟨ sourceY? ⟩)
    ↑ unseal Fin.zero (＇ (Fin.suc Fin.zero)))
    ↑ unseal (Fin.suc Fin.zero) (‵ `ℕ)

target-direct-query : ℕ → Term (suc zero)
target-direct-query n =
  (target-emitted-packet n ⟨ targetZ? ⟩)
    ↑ unseal Fin.zero (‵ `ℕ)

source-packet-⊢ : ∀ n
  → ⟨ suc (suc zero) , scopeStore source-query-scope , [] ⟩
      ⊢ source-emitted-packet n ⦂ ★
source-packet-⊢ n =
  PS.two-adapters-result-⊢ n (S-bind∋ (Z∋ refl) refl) (Z∋ refl)

target-packet-⊢ : ∀ n
  → ⟨ suc zero , scopeStore target-query-scope , [] ⟩
      ⊢ target-emitted-packet n ⦂ ★
target-packet-⊢ n = PS.one-adapter-result-⊢ n (Z∋ refl)

source-alias-query-⊢ : ∀ n
  → ⟨ suc (suc zero) , scopeStore source-query-scope , [] ⟩
      ⊢ source-alias-query n ⦂ ‵ `ℕ
source-alias-query-⊢ n =
  ⊢reveal (⊢↑-unseal (S-bind∋ (Z∋ refl) refl))
    (⊢reveal (⊢↑-unseal (Z∋ refl))
      (⊢⟨⟩ (source-packet-⊢ n) sourceY?))

target-direct-query-⊢ : ∀ n
  → ⟨ suc zero , scopeStore target-query-scope , [] ⟩
      ⊢ target-direct-query n ⦂ ‵ `ℕ
target-direct-query-⊢ n =
  ⊢reveal (⊢↑-unseal (Z∋ refl))
    (⊢⟨⟩ (target-packet-⊢ n) targetZ?)

source-alias-query-return : ∀ n
  → ∃[ tr ] interpretFrom (scopeStore source-query-scope)
      (suc (suc (suc zero)))
      (source-alias-query n)
      ≡ returned (E.result (suc (suc zero))
        (keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ n)) tr ($ (κℕ n)))
source-alias-query-return n = _ , refl

target-direct-query-return : ∀ n
  → ∃[ tr ] interpretFrom (scopeStore target-query-scope)
      (suc (suc zero))
      (target-direct-query n)
      ≡ returned (E.result (suc zero) (keep ∷ keep ∷ [])
        ($ (κℕ n)) tr ($ (κℕ n)))
target-direct-query-return n = _ , refl

packet-query-observed : ∀ n k
  → Observed natural
      (extend-paired (extend-privateI (empty {S = root} {T = root})
        (‵ `ℕ)) (＇ Fin.zero) (‵ `ℕ))
      k (source-alias-query n) (target-direct-query n)
packet-query-observed n k =
  observed-from-returns {gasI = 3} {gasP = 2}
    (proj₂ (source-alias-query-return n))
    (proj₂ (target-direct-query-return n))
    future-refl (same-natural n)
