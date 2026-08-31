module proof.LR-narrow.IntegratedLocalUniversalIdentityExperiments where

-- File Charter:
--   * Regression tests for the occurring-binder polymorphic identity in the
--     scope-local universal interface.
--   * Exercises UniversalValues.instantiate at future-local fresh nominal
--     codes and at precise-only function codes with preserved capabilities.
--   * Adds typed, data-ending evaluator companions for concrete uses.
--   * This file does not claim general body compatibility, general dynamic
--     payloads, arbitrary Ty instantiation, or wrapper closure.

open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; ∃-syntax)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import TermCtx using (Z)
open import CastTerms
open import Conversion using (seal; unseal; ⊢↓-seal; ⊢↑-unseal)
open import Reduction
open import Primitives using (κℕ)
open import Interpreter
import Eval as E
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.IntegratedLocal
open import proof.LR-narrow.IntegratedLocalCodes
open import proof.LR-narrow.IntegratedLocalUniversal
import proof.LR-narrow.IntegratedLocalUniversalIdentity as Identity
import proof.LR-narrow.IntegratedLocalExperiments as LocalEx
import proof.LR-narrow.ScopedUniversalExperiment as SU
import proof.LR-narrow.IntegratedWorld as IW

module L = Local store-empty store-empty
module LC = Codes store-empty store-empty
module U = Universals store-empty store-empty
module IU = Identity.IdentityUniversal store-empty store-empty
module Wds = IW.Worlds store-empty store-empty

open L
open LC
open U
open Wds

seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

-- Semantic elimination through the universal relation, not a direct call to
-- the identity-instantiation helper.  The argument code lives at scopes
-- allocated after the root and has endpoint X⇒X.

fresh-X⇒X-instantiation-through-universal : ∀ k
  → Observed
      (denote (arrow-code LocalEx.fresh-X⇒X-code
        LocalEx.fresh-X⇒X-code))
      stay stay LocalEx.fresh-world k
      (liftTerm {S = root} {T = LocalEx.fresh-source}
        (grow stay) SU.polymorphic-identity
        ⦂∀ liftBody {S = root} {T = LocalEx.fresh-source}
          (grow stay) (＇ Fin.zero ⇒ ＇ Fin.zero)
          [ ＇ Fin.zero ⇒ ＇ Fin.zero ])
      (liftTerm {S = root} {T = LocalEx.fresh-target}
        (grow stay) SU.polymorphic-identity
        ⦂∀ liftBody {S = root} {T = LocalEx.fresh-target}
          (grow stay) (＇ Fin.zero ⇒ ＇ Fin.zero)
          [ ＇ Fin.zero ⇒ ＇ Fin.zero ])
fresh-X⇒X-instantiation-through-universal k =
  U.UniversalValues.instantiate
    (IU.polymorphic-identity-related
      {S = root} {T = root} {p = stay} {q = stay}
      {W = empty {S = root} {T = root}} (suc k))
    (grow stay) (grow stay) (extend-paired-future empty)
    ≤-refl LocalEx.fresh-X⇒X-code

-- Same universal elimination at a precise-only function code.  The target
-- argument endpoint is the nominal slot itself, while its representation is
-- Nat⇒Nat and the old PreciseOnly capability is preserved.

precise-function-instantiation-through-universal : ∀ k
  → Observed
      (denote (arrow-code LocalEx.precise-function-code
        LocalEx.precise-function-code))
      stay stay LocalEx.precise-world k
      (SU.polymorphic-identity
        ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ‵ `ℕ ⇒ ‵ `ℕ ])
      (SU.polymorphic-identity
        ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ＇ Fin.zero ])
precise-function-instantiation-through-universal k =
  U.UniversalValues.instantiate
    (IU.polymorphic-identity-related
      {S = root} {T = LocalEx.precise-target}
      {p = stay} {q = stay} {W = LocalEx.precise-world} (suc k))
    stay stay future-refl ≤-refl LocalEx.precise-function-code

-- Concrete fresh nominal program:
-- instantiate identity at X⇒X, pass the local identity function, apply it to a
-- sealed 7, then unseal the result back to Nat.

fresh-identity-program : Term 1
fresh-identity-program =
  ((((SU.polymorphic-identity
      ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ＇ Fin.zero ⇒ ＇ Fin.zero ])
    · (ƛ (` 0)))
    · ($ (κℕ seven) ↓ seal Fin.zero (‵ `ℕ)))
    ↑ unseal Fin.zero (‵ `ℕ))

fresh-identity-program-⊢ :
  ⟨ suc zero , scopeStore LocalEx.fresh-source , [] ⟩
    ⊢ fresh-identity-program ⦂ ‵ `ℕ
fresh-identity-program-⊢ =
  ⊢reveal (⊢↑-unseal (Z∋ refl))
    (⊢·
      (⊢· (⊢• SU.polymorphic-identity-⊢) (⊢ƛ (⊢` Z)))
      (⊢conceal (⊢↓-seal (Z∋ refl)) (⊢$ (κℕ seven))))

fresh-identity-program-return :
  ∃[ tr ] interpretFrom (scopeStore LocalEx.fresh-source)
      (suc (suc (suc (suc (suc (suc zero)))))) fresh-identity-program
    ≡ returned (E.result (suc (suc zero))
        (bind (＇ Fin.zero ⇒ ＇ Fin.zero)
          ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ seven)) tr ($ (κℕ seven)))
fresh-identity-program-return = _ , refl

-- Concrete asymmetric precise-only function program.  The source instantiates
-- at Nat⇒Nat.  The target instantiates at its precise-only nominal function
-- slot, then unseals before applying to 7.

source-function-program : Term 0
source-function-program =
  ((SU.polymorphic-identity
    ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ‵ `ℕ ⇒ ‵ `ℕ ])
    · (ƛ (` 0))) · $ (κℕ seven)

target-function-program : Term 1
target-function-program =
  (((SU.polymorphic-identity
    ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ＇ Fin.zero ])
    · ((ƛ (` 0)) ↓ seal Fin.zero (‵ `ℕ ⇒ ‵ `ℕ)))
    ↑ unseal Fin.zero (‵ `ℕ ⇒ ‵ `ℕ)) · $ (κℕ seven)

source-function-program-⊢ :
  ⟨ zero , store-empty , [] ⟩ ⊢ source-function-program ⦂ ‵ `ℕ
source-function-program-⊢ =
  ⊢·
    (⊢· (⊢• SU.polymorphic-identity-⊢) (⊢ƛ (⊢` Z)))
    (⊢$ (κℕ seven))

target-function-program-⊢ :
  ⟨ suc zero , scopeStore LocalEx.precise-target , [] ⟩
    ⊢ target-function-program ⦂ ‵ `ℕ
target-function-program-⊢ =
  ⊢·
    (⊢reveal (⊢↑-unseal (Z∋ refl))
      (⊢· (⊢• SU.polymorphic-identity-⊢)
        (⊢conceal (⊢↓-seal (Z∋ refl)) (⊢ƛ (⊢` Z)))))
    (⊢$ (κℕ seven))

source-function-program-return :
  ∃[ tr ] interpretFrom store-empty
      (suc (suc (suc (suc (suc zero))))) source-function-program
    ≡ returned (E.result (suc zero)
        (bind (‵ `ℕ ⇒ ‵ `ℕ) ∷ keep ∷ keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ seven)) tr ($ (κℕ seven)))
source-function-program-return = _ , refl

target-function-program-return :
  ∃[ tr ] interpretFrom (scopeStore LocalEx.precise-target)
      (suc (suc (suc (suc (suc (suc zero)))))) target-function-program
    ≡ returned (E.result (suc (suc zero))
        (bind (＇ Fin.zero) ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ seven)) tr ($ (κℕ seven)))
target-function-program-return = _ , refl
