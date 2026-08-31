module proof.LR-narrow.IntegratedSteps where

-- File Charter:
--   * Actual pure-step prefix expansion for the integrated observations.
--   * Each direction preserves the returned nominal world and all three
--     observation clauses. No step-index credit is assumed from the LR.
--   * Finite prefixes compose in their written order, including silent-side
--     boundaries. Allocating/frame composition is a separate obligation.

open import Data.Maybe using (just; nothing)
open import Data.Nat using (suc; _<_; _∸_; s≤s)
open import Data.Nat.Properties using (≤-trans; n≤1+n; ∸-monoʳ-≤)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import TyStore
open import CastTerms
open import Reduction
open import Interpreter
import Eval as E
open import LR-narrow.Computation using (BlamesFrom)
open import proof.LR-narrow.Application using (prepend-result)
open import proof.LR-narrow.StepExpansion using
  (pure-step-return-invert; pure-step-return; pure-step-return-expand;
   pure-step-blame-invert; pure-step-blame; pure-step-blame-expand)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.IntegratedModel
import proof.LR-narrow.IntegratedWorld as IW

module Steps {ΔI0 ΔP0} (ΣI0 : TyStore ΔI0) (ΣP0 : TyStore ΔP0) where

  open Model ΣI0 ΣP0
  open IW.Worlds ΣI0 ΣP0

  observed-right-step : ∀ {ΔI ΔP} {A : SemanticType}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {W : World S T} {k M N N′}
    → N ≢ blame → E.value? N ≡ nothing → (step : N —→ N′)
    → E.step? (scopeStore T) N ≡ just
        (E.step-result keep N′ (pure-step step))
    → Observed A W k M N′ → Observed A W k M N
  observed-right-step {A = A} {S} {T} {W} {k} {M} {N} {N′}
      not val step eq c = record
    { forward-return = forward
    ; backward-return = backward
    ; forward-blame = blames
    }
    where
    forward : ∀ {n} {outI : E.EvalResult M}
      → n < k → interpretFrom (scopeStore S) n M ≡ returned outI
      → (∃[ m ] ∃[ outP ]
          (interpretFrom (scopeStore T) m N ≡ returned outP)
          × ∃[ W′ ] Future (advance-future S (E.changes outI))
              (advance-future T (E.changes outP)) W W′
            × related A W′ (k ∸ n) (E.term outI) (E.term outP))
        ⊎ (∃[ m ] BlamesFrom (scopeStore T) m N)
    forward n<k ret with Observed.forward-return c n<k ret
    forward n<k ret | inj₁ (m , outP , retP , W′ , ext , r) =
      inj₁ (suc m , prepend-result (pure-step step) outP ,
        pure-step-return-expand {Σ = scopeStore T} {gas = m}
          not val step eq retP , W′ , ext , r)
    forward n<k ret | inj₂ (m , bl) =
      inj₂ (suc m , pure-step-blame-expand {Σ = scopeStore T} {gas = m}
        not val step eq bl)

    backward : ∀ {n} {outP : E.EvalResult N}
      → n < k → interpretFrom (scopeStore T) n N ≡ returned outP
      → ∃[ m ] ∃[ outI ]
          (interpretFrom (scopeStore S) m M ≡ returned outI)
          × ∃[ W′ ] Future (advance-future S (E.changes outI))
              (advance-future T (E.changes outP)) W W′
            × related A W′ (k ∸ n) (E.term outI) (E.term outP)
    backward {n} n<k ret with pure-step-return-invert
      {Σ = scopeStore T} {n = n} not val step eq ret
    backward n<k ret | pure-step-return {gas} out bodyRet refl
        with Observed.backward-return c
          (≤-trans (s≤s (n≤1+n gas)) n<k) bodyRet
    backward n<k ret | pure-step-return {gas} out bodyRet refl
        | m , outI , retI , W′ , ext , r =
      m , outI , retI , W′ , ext ,
        downward A (∸-monoʳ-≤ k (n≤1+n gas)) r

    blames : ∀ {n} → n < k → BlamesFrom (scopeStore S) n M
      → ∃[ m ] BlamesFrom (scopeStore T) m N
    blames n<k bl with Observed.forward-blame c n<k bl
    blames n<k bl | m , blP =
      suc m , pure-step-blame-expand {Σ = scopeStore T} {gas = m}
        not val step eq blP

  observed-left-step : ∀ {ΔI ΔP} {A : SemanticType}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {W : World S T} {k M M′ N}
    → M ≢ blame → E.value? M ≡ nothing → (step : M —→ M′)
    → E.step? (scopeStore S) M ≡ just
        (E.step-result keep M′ (pure-step step))
    → Observed A W k M′ N → Observed A W k M N
  observed-left-step {A = A} {S} {T} {W} {k} {M} {M′} {N}
      not val step eq c = record
    { forward-return = forward
    ; backward-return = backward
    ; forward-blame = blames
    }
    where
    forward : ∀ {n} {outI : E.EvalResult M}
      → n < k → interpretFrom (scopeStore S) n M ≡ returned outI
      → (∃[ m ] ∃[ outP ]
          (interpretFrom (scopeStore T) m N ≡ returned outP)
          × ∃[ W′ ] Future (advance-future S (E.changes outI))
              (advance-future T (E.changes outP)) W W′
            × related A W′ (k ∸ n) (E.term outI) (E.term outP))
        ⊎ (∃[ m ] BlamesFrom (scopeStore T) m N)
    forward {n} n<k ret with pure-step-return-invert
      {Σ = scopeStore S} {n = n} not val step eq ret
    forward n<k ret | pure-step-return {gas} out bodyRet refl
        with Observed.forward-return c
          (≤-trans (s≤s (n≤1+n gas)) n<k) bodyRet
    forward n<k ret | pure-step-return {gas} out bodyRet refl
        | inj₁ (m , outP , retP , W′ , ext , r) =
      inj₁ (m , outP , retP , W′ , ext ,
        downward A (∸-monoʳ-≤ k (n≤1+n gas)) r)
    forward n<k ret | pure-step-return {gas} out bodyRet refl | inj₂ b =
      inj₂ b

    backward : ∀ {n} {outP : E.EvalResult N}
      → n < k → interpretFrom (scopeStore T) n N ≡ returned outP
      → ∃[ m ] ∃[ outI ]
          (interpretFrom (scopeStore S) m M ≡ returned outI)
          × ∃[ W′ ] Future (advance-future S (E.changes outI))
              (advance-future T (E.changes outP)) W W′
            × related A W′ (k ∸ n) (E.term outI) (E.term outP)
    backward n<k ret with Observed.backward-return c n<k ret
    backward n<k ret | m , outI , retI , W′ , ext , r =
      suc m , prepend-result (pure-step step) outI ,
        pure-step-return-expand {Σ = scopeStore S} {gas = m}
          not val step eq retI , W′ , ext , r

    blames : ∀ {n} → n < k → BlamesFrom (scopeStore S) n M
      → ∃[ m ] BlamesFrom (scopeStore T) m N
    blames {n} n<k bl with pure-step-blame-invert
      {Σ = scopeStore S} {n = n} not val step eq bl
    blames n<k bl | pure-step-blame {gas} bodyBlame =
      Observed.forward-blame c (≤-trans (s≤s (n≤1+n gas)) n<k) bodyBlame
