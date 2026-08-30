module proof.LR-narrow.ScopedRightFrameComposition where

-- File Charter:
--   * Right-only scoped composition for evaluation frames.
--   * If source/target operands are observed at A, and each related returned
--     operand pair is observed after plugging only the target into a
--     transported frame, the original source computation is observed against
--     framed target computation at B.
--   * Source syntax and source histories are preserved exactly; only the
--     target side is split/assembled through FramePhases.

open import Data.List using ([])
open import Data.Nat using (_+_; _∸_; _≤_; _<_; zero)
open import Data.Nat.Properties using (m<n⇒0<n∸m; m∸n≤m)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
open import Reduction
import Eval as E
open import Interpreter
open import LR-narrow.Computation using (BlamesFrom)
open import proof.LR-narrow.Application using
  (_++ˢ_; first-of-two<; drop-left-<; subtract-phases;
   return-store-reindex; blame-store-reindex; value-return-exact)
open import proof.LR-narrow.CastComposition using (sum-bound-from-split)
open import proof.LR-narrow.FramePhases
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.TargetEvaluation using (return-result-unique)

module Composition (F : Frame) {Δᴵ₀ Δᴾ₀}
    (Σᴵ₀ : TyStore Δᴵ₀) (Σᴾ₀ : TyStore Δᴾ₀) where

  private
    module P = Frame F
    open Model Σᴵ₀ Σᴾ₀

    advance-append : ∀ {Δ₀ Δ Δ′ Δ″} {Σ₀ : TyStore Δ₀}
        (S : PhysicalScope Σ₀ Δ) (χs : StoreChanges Δ Δ′)
        (ψs : StoreChanges Δ′ Δ″)
      → advance (advance S χs) ψs ≡ advance S (χs ++ˢ ψs)
    advance-append S [] ψs = refl
    advance-append S (keep ∷ χs) ψs = advance-append S χs ψs
    advance-append S (bind A ∷ χs) ψs =
      advance-append (allocate S A) χs ψs

    result-related-right : ∀ {Δᴵ Δᴾ Δᴵ′ Δᴾ′ Δᴾ″}
        {A : ScopedType}
        {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ}
        {χsᴵ : StoreChanges Δᴵ Δᴵ′}
        {χsᴾ : StoreChanges Δᴾ Δᴾ′}
        {ψsᴾ : StoreChanges Δᴾ′ Δᴾ″}
        {j U V}
      → related A (advance S χsᴵ) (advance (advance T χsᴾ) ψsᴾ)
          j U V
      → related A (advance S χsᴵ) (advance T (χsᴾ ++ˢ ψsᴾ))
          j U V
    result-related-right {A = A} {S = S} {T} {χsᴵ} {χsᴾ}
        {ψsᴾ} {j} {U} {V} r =
      subst≡ (λ T′ → related A (advance S χsᴵ) T′ j U V)
        (advance-append T χsᴾ ψsᴾ) r

  right-frame-observed : ∀ {Δᴵ Δᴾ} {A B : ScopedType}
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ}
      {k M N}
      (f : P.Frm Δᴾ)
    → (∀ {Δᴵ′ Δᴾ′}
        (χsᴵ : StoreChanges Δᴵ Δᴵ′)
        (χsᴾ : StoreChanges Δᴾ Δᴾ′)
        {j U V}
      → j ≤ k
      → related A (advance S χsᴵ) (advance T χsᴾ) j U V
      → ObservedComputations B (advance S χsᴵ) (advance T χsᴾ) j
          U (P.plug (P.transports χsᴾ f) V))
    → ObservedComputations A S T k M N
    → ObservedComputations B S T k M (P.plug f N)
  right-frame-observed {A = A} {B} {S} {T} {k} {M} {N}
      f plug-values operand-related = record
    { forward-return = forward
    ; backward-return = backward
    ; forward-blame = forward-blame-frame
    }
    where
    forward : ∀ {n} {resultᴵ : E.EvalResult M}
      → n < k
      → interpretFrom (scopeStore S) n M ≡ returned resultᴵ
      → (∃[ m ] ∃[ resultᴾ ]
          (interpretFrom (scopeStore T) m (P.plug f N) ≡ returned resultᴾ)
          × related B (advance S (E.changes resultᴵ))
              (advance T (E.changes resultᴾ)) (k ∸ n)
              (E.term resultᴵ) (E.term resultᴾ))
        ⊎ (∃[ m ] BlamesFrom (scopeStore T) m (P.plug f N))
    forward {n = n} {resultᴵ = resultᴵ} n<k result-eq
        with ObservedComputations.forward-return operand-related
          {n = n} {outᴵ = resultᴵ} n<k result-eq
    forward {n = n} n<k result-eq
        | inj₂ (operandGasᴾ , operandBlameᴾ)
        with P.operand-blame-expand
          {Σ = scopeStore T} {operandGas = operandGasᴾ}
          f {M = N} operandBlameᴾ
    forward {n = n} n<k result-eq
        | inj₂ (operandGasᴾ , operandBlameᴾ)
        | wholeGasᴾ , wholeBlameᴾ = inj₂ (wholeGasᴾ , wholeBlameᴾ)
    forward {n = n} {resultᴵ = resultᴵ} n<k result-eq
        | inj₁ (operandGasᴾ , operandResultᴾ , operandReturnᴾ ,
            operandValueRelated)
        with ObservedComputations.forward-return call-related
          {n = zero}
          (m<n⇒0<n∸m n<k)
          (value-return-exact {Σ = scopeStore
            (advance S (E.changes resultᴵ))} zero
            (imprecise-value A operandValueRelated))
      where
      call-related : ObservedComputations B
        (advance S (E.changes resultᴵ))
        (advance T (E.changes operandResultᴾ)) (k ∸ n)
        (E.term resultᴵ)
        (P.plug (P.transports (E.changes operandResultᴾ) f)
          (E.term operandResultᴾ))
      call-related = plug-values
        (E.changes resultᴵ) (E.changes operandResultᴾ)
        {j = k ∸ n} (m∸n≤m k n) operandValueRelated
    forward {n = n} n<k result-eq
        | inj₁ (operandGasᴾ , operandResultᴾ , operandReturnᴾ ,
            operandValueRelated)
        | inj₂ (callGasᴾ , callBlameᴾ)
        with P.call-blame-expand
          {Σ = scopeStore T}
          {operandGas = operandGasᴾ} {callGas = callGasᴾ}
          f {M = N} {operandResult = operandResultᴾ}
          operandReturnᴾ
          (blame-store-reindex {gas = callGasᴾ}
            (sym (advance-store T (E.changes operandResultᴾ)))
            callBlameᴾ)
    forward {n = n} n<k result-eq
        | inj₁ (operandGasᴾ , operandResultᴾ , operandReturnᴾ ,
            operandValueRelated)
        | inj₂ (callGasᴾ , callBlameᴾ)
        | wholeGasᴾ , wholeBlameᴾ = inj₂ (wholeGasᴾ , wholeBlameᴾ)
    forward {n = n} {resultᴵ = resultᴵ} n<k result-eq
        | inj₁ (operandGasᴾ , operandResultᴾ , operandReturnᴾ ,
            operandValueRelated)
        | inj₁ (callGasᴾ , callResultᴾ , callReturnᴾ , callValueRelated)
        with P.return-expand {Σ = scopeStore T}
          {operandGas = operandGasᴾ} {callGas = callGasᴾ}
          f {M = N} {operandResult = operandResultᴾ}
          {callResult = callResultᴾ} operandReturnᴾ
          (return-store-reindex {gas = callGasᴾ}
            {result = callResultᴾ}
            (sym (advance-store T (E.changes operandResultᴾ)))
            callReturnᴾ)
    forward {n = n} {resultᴵ = resultᴵ} n<k result-eq
        | inj₁ (operandGasᴾ , operandResultᴾ , operandReturnᴾ ,
            operandValueRelated)
        | inj₁ (callGasᴾ , callResultᴾ , callReturnᴾ , callValueRelated)
        | wholeGasᴾ , wholeReturnᴾ =
      inj₁ (wholeGasᴾ , P.sequence-result f operandResultᴾ callResultᴾ ,
        wholeReturnᴾ , assembled)
      where
      assembled = result-related-right {A = B} {S = S} {T = T}
        {χsᴵ = E.changes resultᴵ}
        {χsᴾ = E.changes operandResultᴾ}
        {ψsᴾ = E.changes callResultᴾ}
        callValueRelated

    backward : ∀ {n} {resultᴾ : E.EvalResult (P.plug f N)}
      → n < k
      → interpretFrom (scopeStore T) n (P.plug f N) ≡ returned resultᴾ
      → ∃[ m ] ∃[ resultᴵ ]
          (interpretFrom (scopeStore S) m M ≡ returned resultᴵ)
          × related B (advance S (E.changes resultᴵ))
              (advance T (E.changes resultᴾ)) (k ∸ n)
              (E.term resultᴵ) (E.term resultᴾ)
    backward {n = n} {resultᴾ = resultᴾ} n<k result-eq
        with P.return-phases-of {Σ = scopeStore T} {gas = n}
          f {M = N} {result = resultᴾ} result-eq
    backward {n = n} {resultᴾ = resultᴾ} n<k result-eq
        | P.return-phases operandGas operandResultᴾ operandReturn
            callGas callResultᴾ callReturn result-split gas-split
        with ObservedComputations.backward-return operand-related
          {n = operandGas} {outᴾ = operandResultᴾ}
          operandGas<k operandReturn
      where
      phases<k : operandGas + callGas < k
      phases<k = sum-bound-from-split
        {a = operandGas} {b = callGas} {n = n} {k = k}
        gas-split n<k

      operandGas<k = first-of-two<
        {a = operandGas} {b = callGas} {k = k} phases<k
    backward {n = n} {resultᴾ = resultᴾ} n<k result-eq
        | P.return-phases operandGas operandResultᴾ operandReturn
            callGas callResultᴾ callReturn result-split gas-split
        | operandGasᴵ , operandResultᴵ , operandReturnᴵ ,
            operandValueRelated
        with ObservedComputations.backward-return call-related
          {n = callGas} {outᴾ = callResultᴾ}
          callGas<k callReturn-at-scope
      where
      phases<k : operandGas + callGas < k
      phases<k = sum-bound-from-split
        {a = operandGas} {b = callGas} {n = n} {k = k}
        gas-split n<k

      callGas<k : callGas < k ∸ operandGas
      callGas<k = drop-left-<
        {a = operandGas} {b = callGas} {k = k} phases<k

      callReturn-at-scope = return-store-reindex
        {gas = callGas} {result = callResultᴾ}
        (advance-store T (E.changes operandResultᴾ)) callReturn

      call-related : ObservedComputations B
        (advance S (E.changes operandResultᴵ))
        (advance T (E.changes operandResultᴾ)) (k ∸ operandGas)
        (E.term operandResultᴵ)
        (P.plug (P.transports (E.changes operandResultᴾ) f)
          (E.term operandResultᴾ))
      call-related = plug-values
        (E.changes operandResultᴵ) (E.changes operandResultᴾ)
        {j = k ∸ operandGas} (m∸n≤m k operandGas)
        operandValueRelated
    backward {n = n} {resultᴾ = resultᴾ} n<k result-eq
        | P.return-phases operandGas operandResultᴾ operandReturn
            callGas callResultᴾ callReturn result-split gas-split
        | operandGasᴵ , operandResultᴵ , operandReturnᴵ ,
            operandValueRelated
        | callGasᴵ , callResultᴵ , callReturnᴵ , callValueRelated =
      operandGasᴵ , operandResultᴵ , operandReturnᴵ ,
      subst≡ (λ out → related B (advance S (E.changes operandResultᴵ))
        (advance T (E.changes out)) (k ∸ n)
        (E.term operandResultᴵ) (E.term out)) (sym result-split) assembled
      where
      valueResultᴵ : E.EvalResult (E.term operandResultᴵ)
      valueResultᴵ = E.result (E.Δ′ operandResultᴵ) [] (E.term operandResultᴵ)
        (E.term operandResultᴵ ∎[])
        (imprecise-value A operandValueRelated)

      valueReturnᴵ : interpretFrom
          (scopeStore (advance S (E.changes operandResultᴵ))) callGasᴵ
          (E.term operandResultᴵ)
        ≡ returned valueResultᴵ
      valueReturnᴵ = value-return-exact
        {Σ = scopeStore (advance S (E.changes operandResultᴵ))}
        callGasᴵ (imprecise-value A operandValueRelated)

      source-result-eq : callResultᴵ ≡ valueResultᴵ
      source-result-eq = return-result-unique
        {Σ = scopeStore (advance S (E.changes operandResultᴵ))}
        {leftGas = callGasᴵ} {rightGas = callGasᴵ}
        {M = E.term operandResultᴵ}
        {left = callResultᴵ} {right = valueResultᴵ}
        callReturnᴵ valueReturnᴵ

      index-eq = trans (subtract-phases k operandGas callGas)
        (cong (k ∸_) gas-split)

      callValueRelated-indexed : related B
        (advance (advance S (E.changes operandResultᴵ))
          (E.changes callResultᴵ))
        (advance (advance T (E.changes operandResultᴾ))
          (E.changes callResultᴾ))
        (k ∸ n) (E.term callResultᴵ) (E.term callResultᴾ)
      callValueRelated-indexed =
        subst≡ (λ j → related B
            (advance (advance S (E.changes operandResultᴵ))
              (E.changes callResultᴵ))
            (advance (advance T (E.changes operandResultᴾ))
              (E.changes callResultᴾ))
            j (E.term callResultᴵ) (E.term callResultᴾ))
          index-eq
          callValueRelated

      callValueRelated-source-collapsed : related B
        (advance S (E.changes operandResultᴵ))
        (advance (advance T (E.changes operandResultᴾ))
          (E.changes callResultᴾ))
        (k ∸ n) (E.term operandResultᴵ) (E.term callResultᴾ)
      callValueRelated-source-collapsed =
        subst≡ (λ callResult → related B
            (advance (advance S (E.changes operandResultᴵ))
              (E.changes callResult))
            (advance (advance T (E.changes operandResultᴾ))
              (E.changes callResultᴾ))
            (k ∸ n) (E.term callResult) (E.term callResultᴾ))
          source-result-eq
          callValueRelated-indexed

      assembled : related B (advance S (E.changes operandResultᴵ))
        (advance T (E.changes
          (P.sequence-result f operandResultᴾ callResultᴾ)))
        (k ∸ n) (E.term operandResultᴵ)
        (E.term (P.sequence-result f operandResultᴾ callResultᴾ))
      assembled = result-related-right
        {A = B} {S = S} {T = T}
        {χsᴵ = E.changes operandResultᴵ}
        {χsᴾ = E.changes operandResultᴾ}
        {ψsᴾ = E.changes callResultᴾ}
        callValueRelated-source-collapsed

    forward-blame-frame : ∀ {n}
      → n < k
      → BlamesFrom (scopeStore S) n M
      → ∃[ m ] BlamesFrom (scopeStore T) m (P.plug f N)
    forward-blame-frame {n = n} n<k blaming
        with ObservedComputations.forward-blame operand-related n<k blaming
    forward-blame-frame {n = n} n<k blaming
        | operandGasᴾ , operandBlameᴾ
        with P.operand-blame-expand
          {Σ = scopeStore T} {operandGas = operandGasᴾ}
          f {M = N} operandBlameᴾ
    forward-blame-frame {n = n} n<k blaming
        | operandGasᴾ , operandBlameᴾ
        | wholeGasᴾ , wholeBlameᴾ = wholeGasᴾ , wholeBlameᴾ
