module proof.LR-narrow.ScopedFrameComposition where

-- File Charter:
--   * Generic scoped composition for paired evaluation frames.
--   * If operands are observed at a scoped semantic type and plugging every
--     pair of related returned values into transported frames is observed at
--     the result type, then the framed computations are observed.
--   * Reuses FramePhases for evaluator splitting/assembly and preserves the
--     exact physical result scopes induced by both operand and call histories.

open import Data.List using ([])
open import Data.Nat using (ℕ; _+_; _∸_; _≤_; _<_; s≤s)
open import Data.Nat.Properties using (≤-trans; m∸n≤m)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
  renaming (subst to subst≡; subst₂ to subst₂≡)

open import Types
open import TyStore
open import CastTerms
open import Reduction
import Eval as E
open import Interpreter
open import LR-narrow.Computation using (BlamesFrom)
open import proof.LR-narrow.Application using
  (_++ˢ_; first-of-two<; drop-left-<; subtract-phases;
   return-store-reindex; blame-store-reindex)
open import proof.LR-narrow.CastComposition using (sum-bound-from-split)
open import proof.LR-narrow.FramePhases
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior

module Composition (Fᴵ Fᴾ : Frame) {Δᴵ₀ Δᴾ₀}
    (Σᴵ₀ : TyStore Δᴵ₀) (Σᴾ₀ : TyStore Δᴾ₀) where

  private
    module I = Frame Fᴵ
    module P = Frame Fᴾ
    open Model Σᴵ₀ Σᴾ₀

    advance-append : ∀ {Δ₀ Δ Δ′ Δ″} {Σ₀ : TyStore Δ₀}
        (S : PhysicalScope Σ₀ Δ) (χs : StoreChanges Δ Δ′)
        (ψs : StoreChanges Δ′ Δ″)
      → advance (advance S χs) ψs ≡ advance S (χs ++ˢ ψs)
    advance-append S [] ψs = refl
    advance-append S (keep ∷ χs) ψs = advance-append S χs ψs
    advance-append S (bind A ∷ χs) ψs =
      advance-append (allocate S A) χs ψs

    result-related : ∀ {Δᴵ Δᴾ Δᴵ′ Δᴾ′ Δᴵ″ Δᴾ″}
        {A : ScopedType}
        {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ}
        {χsᴵ : StoreChanges Δᴵ Δᴵ′}
        {χsᴾ : StoreChanges Δᴾ Δᴾ′}
        {ψsᴵ : StoreChanges Δᴵ′ Δᴵ″}
        {ψsᴾ : StoreChanges Δᴾ′ Δᴾ″}
        {j U V}
      → related A (advance (advance S χsᴵ) ψsᴵ)
          (advance (advance T χsᴾ) ψsᴾ) j U V
      → related A (advance S (χsᴵ ++ˢ ψsᴵ))
          (advance T (χsᴾ ++ˢ ψsᴾ)) j U V
    result-related {A = A} {S = S} {T} {χsᴵ} {χsᴾ}
        {ψsᴵ} {ψsᴾ} {j} {U} {V} r =
      subst₂≡ (λ S′ T′ → related A S′ T′ j U V)
        (advance-append S χsᴵ ψsᴵ)
        (advance-append T χsᴾ ψsᴾ) r

    result-related′ : ∀ {Δᴵ Δᴾ}
        {A : ScopedType}
        {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ}
        {k L R}
        {resultᴵ resultᴵ′ : E.EvalResult L}
        {resultᴾ resultᴾ′ : E.EvalResult R}
      → resultᴵ ≡ resultᴵ′
      → resultᴾ ≡ resultᴾ′
      → related A (advance S (E.changes resultᴵ′))
          (advance T (E.changes resultᴾ′)) k
          (E.term resultᴵ′) (E.term resultᴾ′)
      → related A (advance S (E.changes resultᴵ))
          (advance T (E.changes resultᴾ)) k
          (E.term resultᴵ) (E.term resultᴾ)
    result-related′ refl refl r = r

  frame-observed : ∀ {Δᴵ Δᴾ} {A B : ScopedType}
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ}
      {k M N}
      (fᴵ : I.Frm Δᴵ) (fᴾ : P.Frm Δᴾ)
    → (∀ {Δᴵ′ Δᴾ′}
        (χsᴵ : StoreChanges Δᴵ Δᴵ′)
        (χsᴾ : StoreChanges Δᴾ Δᴾ′)
        {j U V}
      → j ≤ k
      → related A (advance S χsᴵ) (advance T χsᴾ) j U V
      → ObservedComputations B (advance S χsᴵ) (advance T χsᴾ) j
          (I.plug (I.transports χsᴵ fᴵ) U)
          (P.plug (P.transports χsᴾ fᴾ) V))
    → ObservedComputations A S T k M N
    → ObservedComputations B S T k (I.plug fᴵ M) (P.plug fᴾ N)
  frame-observed {A = A} {B} {S} {T} {k} {M} {N}
      fᴵ fᴾ plug-values operand-related = record
    { forward-return = forward
    ; backward-return = backward
    ; forward-blame = forward-blame-frame
    }
    where
    forward : ∀ {n} {resultᴵ : E.EvalResult (I.plug fᴵ M)}
      → n < k
      → interpretFrom (scopeStore S) n (I.plug fᴵ M) ≡ returned resultᴵ
      → (∃[ m ] ∃[ resultᴾ ]
          (interpretFrom (scopeStore T) m (P.plug fᴾ N) ≡ returned resultᴾ)
          × related B (advance S (E.changes resultᴵ))
              (advance T (E.changes resultᴾ)) (k ∸ n)
              (E.term resultᴵ) (E.term resultᴾ))
        ⊎ (∃[ m ] BlamesFrom (scopeStore T) m (P.plug fᴾ N))
    forward {n = n} {resultᴵ = resultᴵ} n<k result-eq
        with I.return-phases-of {Σ = scopeStore S} {gas = n}
          fᴵ {M = M} {result = resultᴵ} result-eq
    forward {n = n} {resultᴵ = resultᴵ} n<k result-eq
        | I.return-phases operandGas operandResult operandReturn
            callGas callResult callReturn result-split gas-split
        with ObservedComputations.forward-return operand-related
          {n = operandGas} {outᴵ = operandResult}
          operandGas<k operandReturn
      where
      phases<k : operandGas + callGas < k
      phases<k = sum-bound-from-split
        {a = operandGas} {b = callGas} {n = n} {k = k}
        gas-split n<k

      operandGas<k = first-of-two<
        {a = operandGas} {b = callGas} {k = k} phases<k
    forward {n = n} n<k result-eq
        | I.return-phases operandGas operandResult operandReturn
            callGas callResult callReturn result-split gas-split
        | inj₂ (operandGasᴾ , operandBlameᴾ)
        with P.operand-blame-expand
          {Σ = scopeStore T} {operandGas = operandGasᴾ}
          fᴾ {M = N} operandBlameᴾ
    forward {n = n} n<k result-eq
        | I.return-phases operandGas operandResult operandReturn
            callGas callResult callReturn result-split gas-split
        | inj₂ (operandGasᴾ , operandBlameᴾ)
        | wholeGasᴾ , wholeBlameᴾ = inj₂ (wholeGasᴾ , wholeBlameᴾ)
    forward {n = n} {resultᴵ = resultᴵ} n<k result-eq
        | I.return-phases operandGas operandResultᴵ operandReturn
            callGas callResultᴵ callReturn result-split gas-split
        | inj₁ (operandGasᴾ , operandResultᴾ , operandReturnᴾ ,
            operandValueRelated)
        with ObservedComputations.forward-return call-related
          {n = callGas} {outᴵ = callResultᴵ}
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
        {gas = callGas} {result = callResultᴵ}
        (advance-store S (E.changes operandResultᴵ)) callReturn

      call-related : ObservedComputations B
        (advance S (E.changes operandResultᴵ))
        (advance T (E.changes operandResultᴾ)) (k ∸ operandGas)
        (I.plug (I.transports (E.changes operandResultᴵ) fᴵ)
          (E.term operandResultᴵ))
        (P.plug (P.transports (E.changes operandResultᴾ) fᴾ)
          (E.term operandResultᴾ))
      call-related = plug-values
        (E.changes operandResultᴵ) (E.changes operandResultᴾ)
        {j = k ∸ operandGas} (m∸n≤m k operandGas)
        operandValueRelated
    forward {n = n} n<k result-eq
        | I.return-phases operandGas operandResultᴵ operandReturn
            callGas callResultᴵ callReturn result-split gas-split
        | inj₁ (operandGasᴾ , operandResultᴾ , operandReturnᴾ ,
            operandValueRelated)
        | inj₂ (callGasᴾ , callBlameᴾ)
        with P.call-blame-expand
          {Σ = scopeStore T}
          {operandGas = operandGasᴾ} {callGas = callGasᴾ}
          fᴾ {M = N} {operandResult = operandResultᴾ}
          operandReturnᴾ
          (blame-store-reindex {gas = callGasᴾ}
            (sym (advance-store T (E.changes operandResultᴾ)))
            callBlameᴾ)
    forward {n = n} n<k result-eq
        | I.return-phases operandGas operandResultᴵ operandReturn
            callGas callResultᴵ callReturn result-split gas-split
        | inj₁ (operandGasᴾ , operandResultᴾ , operandReturnᴾ ,
            operandValueRelated)
        | inj₂ (callGasᴾ , callBlameᴾ)
        | wholeGasᴾ , wholeBlameᴾ = inj₂ (wholeGasᴾ , wholeBlameᴾ)
    forward {n = n} {resultᴵ = resultᴵ} n<k result-eq
        | I.return-phases operandGas operandResultᴵ operandReturn
            callGas callResultᴵ callReturn result-split gas-split
        | inj₁ (operandGasᴾ , operandResultᴾ , operandReturnᴾ ,
            operandValueRelated)
        | inj₁ (callGasᴾ , callResultᴾ , callReturnᴾ , callValueRelated)
        with P.return-expand {Σ = scopeStore T}
          {operandGas = operandGasᴾ} {callGas = callGasᴾ}
          fᴾ {M = N} {operandResult = operandResultᴾ}
          {callResult = callResultᴾ} operandReturnᴾ
          (return-store-reindex {gas = callGasᴾ}
            {result = callResultᴾ}
            (sym (advance-store T (E.changes operandResultᴾ)))
            callReturnᴾ)
    forward {n = n} {resultᴵ = resultᴵ} n<k result-eq
        | I.return-phases operandGas operandResultᴵ operandReturn
            callGas callResultᴵ callReturn result-split gas-split
        | inj₁ (operandGasᴾ , operandResultᴾ , operandReturnᴾ ,
            operandValueRelated)
        | inj₁ (callGasᴾ , callResultᴾ , callReturnᴾ , callValueRelated)
        | wholeGasᴾ , wholeReturnᴾ =
      inj₁ (wholeGasᴾ , P.sequence-result fᴾ operandResultᴾ callResultᴾ ,
        wholeReturnᴾ ,
        result-related′ {A = B} {S = S} {T = T} {k = k ∸ n}
          {resultᴵ = resultᴵ}
          {resultᴵ′ = I.sequence-result fᴵ operandResultᴵ callResultᴵ}
          {resultᴾ = P.sequence-result fᴾ operandResultᴾ callResultᴾ}
          {resultᴾ′ = P.sequence-result fᴾ operandResultᴾ callResultᴾ}
          result-split refl assembled)
      where
      index-eq = trans (subtract-phases k operandGas callGas)
        (cong (k ∸_) gas-split)

      assembled = result-related {A = B} {S = S} {T = T}
        {χsᴵ = E.changes operandResultᴵ}
        {χsᴾ = E.changes operandResultᴾ}
        {ψsᴵ = E.changes callResultᴵ}
        {ψsᴾ = E.changes callResultᴾ}
        (subst≡ (λ j → related B
            (advance (advance S (E.changes operandResultᴵ))
              (E.changes callResultᴵ))
            (advance (advance T (E.changes operandResultᴾ))
              (E.changes callResultᴾ))
            j (E.term callResultᴵ) (E.term callResultᴾ))
          index-eq
          callValueRelated)

    backward : ∀ {n} {resultᴾ : E.EvalResult (P.plug fᴾ N)}
      → n < k
      → interpretFrom (scopeStore T) n (P.plug fᴾ N) ≡ returned resultᴾ
      → ∃[ m ] ∃[ resultᴵ ]
          (interpretFrom (scopeStore S) m (I.plug fᴵ M) ≡ returned resultᴵ)
          × related B (advance S (E.changes resultᴵ))
              (advance T (E.changes resultᴾ)) (k ∸ n)
              (E.term resultᴵ) (E.term resultᴾ)
    backward {n = n} {resultᴾ = resultᴾ} n<k result-eq
        with P.return-phases-of {Σ = scopeStore T} {gas = n}
          fᴾ {M = N} {result = resultᴾ} result-eq
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
        (I.plug (I.transports (E.changes operandResultᴵ) fᴵ)
          (E.term operandResultᴵ))
        (P.plug (P.transports (E.changes operandResultᴾ) fᴾ)
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
        | callGasᴵ , callResultᴵ , callReturnᴵ , callValueRelated
        with I.return-expand {Σ = scopeStore S}
          {operandGas = operandGasᴵ} {callGas = callGasᴵ}
          fᴵ {M = M} {operandResult = operandResultᴵ}
          {callResult = callResultᴵ} operandReturnᴵ
          (return-store-reindex {gas = callGasᴵ}
            {result = callResultᴵ}
            (sym (advance-store S (E.changes operandResultᴵ)))
            callReturnᴵ)
    backward {n = n} {resultᴾ = resultᴾ} n<k result-eq
        | P.return-phases operandGas operandResultᴾ operandReturn
            callGas callResultᴾ callReturn result-split gas-split
        | operandGasᴵ , operandResultᴵ , operandReturnᴵ ,
            operandValueRelated
        | callGasᴵ , callResultᴵ , callReturnᴵ , callValueRelated
        | wholeGasᴵ , wholeReturnᴵ =
      wholeGasᴵ , I.sequence-result fᴵ operandResultᴵ callResultᴵ ,
      wholeReturnᴵ ,
      result-related′ {A = B} {S = S} {T = T} {k = k ∸ n}
        {resultᴵ = I.sequence-result fᴵ operandResultᴵ callResultᴵ}
        {resultᴵ′ = I.sequence-result fᴵ operandResultᴵ callResultᴵ}
        {resultᴾ = resultᴾ}
        {resultᴾ′ = P.sequence-result fᴾ operandResultᴾ callResultᴾ}
        refl result-split assembled
      where
      index-eq = trans (subtract-phases k operandGas callGas)
        (cong (k ∸_) gas-split)

      assembled = result-related {A = B} {S = S} {T = T}
        {χsᴵ = E.changes operandResultᴵ}
        {χsᴾ = E.changes operandResultᴾ}
        {ψsᴵ = E.changes callResultᴵ}
        {ψsᴾ = E.changes callResultᴾ}
        (subst≡ (λ j → related B
            (advance (advance S (E.changes operandResultᴵ))
              (E.changes callResultᴵ))
            (advance (advance T (E.changes operandResultᴾ))
              (E.changes callResultᴾ))
            j (E.term callResultᴵ) (E.term callResultᴾ))
          index-eq
          callValueRelated)

    forward-blame-frame : ∀ {n}
      → n < k
      → BlamesFrom (scopeStore S) n (I.plug fᴵ M)
      → ∃[ m ] BlamesFrom (scopeStore T) m (P.plug fᴾ N)
    forward-blame-frame {n = n} n<k blaming
        with I.blame-phases-of {Σ = scopeStore S} {gas = n}
          fᴵ {M = M} blaming
    forward-blame-frame {n = n} n<k blaming
        | I.operand-phase-blames operandGas operandBlame operandGas≤n
        with ObservedComputations.forward-blame operand-related
          (≤-trans (s≤s operandGas≤n) n<k) operandBlame
    forward-blame-frame {n = n} n<k blaming
        | I.operand-phase-blames operandGas operandBlame operandGas≤n
        | operandGasᴾ , operandBlameᴾ
        with P.operand-blame-expand
          {Σ = scopeStore T} {operandGas = operandGasᴾ}
          fᴾ {M = N} operandBlameᴾ
    forward-blame-frame {n = n} n<k blaming
        | I.operand-phase-blames operandGas operandBlame operandGas≤n
        | operandGasᴾ , operandBlameᴾ
        | wholeGasᴾ , wholeBlameᴾ = wholeGasᴾ , wholeBlameᴾ
    forward-blame-frame {n = n} n<k blaming
        | I.call-phase-blames operandGas operandResultᴵ operandReturn
            callGas callBlame phases≤n
        with ObservedComputations.forward-return operand-related
          {n = operandGas} {outᴵ = operandResultᴵ}
          operandGas<k operandReturn
      where
      phases<k = ≤-trans (s≤s phases≤n) n<k
      operandGas<k = first-of-two< phases<k
    forward-blame-frame {n = n} n<k blaming
        | I.call-phase-blames operandGas operandResultᴵ operandReturn
            callGas callBlame phases≤n
        | inj₂ (operandGasᴾ , operandBlameᴾ)
        with P.operand-blame-expand
          {Σ = scopeStore T} {operandGas = operandGasᴾ}
          fᴾ {M = N} operandBlameᴾ
    forward-blame-frame {n = n} n<k blaming
        | I.call-phase-blames operandGas operandResultᴵ operandReturn
            callGas callBlame phases≤n
        | inj₂ (operandGasᴾ , operandBlameᴾ)
        | wholeGasᴾ , wholeBlameᴾ = wholeGasᴾ , wholeBlameᴾ
    forward-blame-frame {n = n} n<k blaming
        | I.call-phase-blames operandGas operandResultᴵ operandReturn
            callGas callBlame phases≤n
        | inj₁ (operandGasᴾ , operandResultᴾ , operandReturnᴾ ,
            operandValueRelated)
        with ObservedComputations.forward-blame call-related
          callGas<k callBlame-at-scope
      where
      phases<k = ≤-trans (s≤s phases≤n) n<k
      callGas<k : callGas < k ∸ operandGas
      callGas<k = drop-left-<
        {a = operandGas} {b = callGas} {k = k} phases<k
      callBlame-at-scope = blame-store-reindex {gas = callGas}
        (advance-store S (E.changes operandResultᴵ)) callBlame

      call-related : ObservedComputations B
        (advance S (E.changes operandResultᴵ))
        (advance T (E.changes operandResultᴾ)) (k ∸ operandGas)
        (I.plug (I.transports (E.changes operandResultᴵ) fᴵ)
          (E.term operandResultᴵ))
        (P.plug (P.transports (E.changes operandResultᴾ) fᴾ)
          (E.term operandResultᴾ))
      call-related = plug-values
        (E.changes operandResultᴵ) (E.changes operandResultᴾ)
        {j = k ∸ operandGas} (m∸n≤m k operandGas)
        operandValueRelated
    forward-blame-frame {n = n} n<k blaming
        | I.call-phase-blames operandGas operandResultᴵ operandReturn
            callGas callBlame phases≤n
        | inj₁ (operandGasᴾ , operandResultᴾ , operandReturnᴾ ,
            operandValueRelated)
        | callGasᴾ , callBlameᴾ
        with P.call-blame-expand
          {Σ = scopeStore T}
          {operandGas = operandGasᴾ} {callGas = callGasᴾ}
          fᴾ {M = N} {operandResult = operandResultᴾ}
          operandReturnᴾ
          (blame-store-reindex {gas = callGasᴾ}
            (sym (advance-store T (E.changes operandResultᴾ)))
            callBlameᴾ)
    forward-blame-frame {n = n} n<k blaming
        | I.call-phase-blames operandGas operandResultᴵ operandReturn
            callGas callBlame phases≤n
        | inj₁ (operandGasᴾ , operandResultᴾ , operandReturnᴾ ,
            operandValueRelated)
        | callGasᴾ , callBlameᴾ
        | wholeGasᴾ , wholeBlameᴾ = wholeGasᴾ , wholeBlameᴾ
