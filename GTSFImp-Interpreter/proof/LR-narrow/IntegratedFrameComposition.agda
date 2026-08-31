module proof.LR-narrow.IntegratedFrameComposition where

-- File Charter:
--   * Generic frame composition for IntegratedModel observations.
--   * If operands are observed at an integrated world-indexed semantic type
--     and every pair of related returned values can be plugged into
--     transported frames, then the framed computations are observed.
--   * Return witnesses thread the existential future world produced by the
--     operand observation through the call observation and compose futures
--     along the concrete evaluator histories.

open import Data.List using ([])
open import Data.Nat using (ℕ; _+_; _∸_; _≤_; _<_; s≤s)
open import Data.Nat.Properties using (≤-trans; m∸n≤m)
import Data.Fin as Fin
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
open import proof.LR-narrow.IntegratedModel

module Composition (Fᴵ Fᴾ : Frame) {ΔI₀ ΔP₀}
    (ΣI₀ : TyStore ΔI₀) (ΣP₀ : TyStore ΔP₀) where

  private
    module I = Frame Fᴵ
    module P = Frame Fᴾ
    open Model ΣI₀ ΣP₀
    open Worlds

    advance-append : ∀ {Δ₀ Δ Δ′ Δ″} {Σ₀ : TyStore Δ₀}
        (S : PhysicalScope Σ₀ Δ) (χs : StoreChanges Δ Δ′)
        (ψs : StoreChanges Δ′ Δ″)
      → advance (advance S χs) ψs ≡ advance S (χs ++ˢ ψs)
    advance-append S [] ψs = refl
    advance-append S (keep ∷ χs) ψs = advance-append S χs ψs
    advance-append S (bind A ∷ χs) ψs =
      advance-append (allocate S A) χs ψs

    lift-var-advance-append : ∀ {Δ₀ Δ Δ′ Δ″} {Σ₀ : TyStore Δ₀}
        (S : PhysicalScope Σ₀ Δ) (χs : StoreChanges Δ Δ′)
        (ψs : StoreChanges Δ′ Δ″) (X : TyVar Δ)
      → liftVar (advance-future S (χs ++ˢ ψs)) X
        ≡ liftVar (advance-future (advance S χs) ψs)
            (liftVar (advance-future S χs) X)
    lift-var-advance-append S [] ψs X = refl
    lift-var-advance-append S (keep ∷ χs) ψs X =
      lift-var-advance-append S χs ψs X
    lift-var-advance-append S (bind A ∷ χs) ψs X =
      lift-var-advance-append (allocate S A) χs ψs (Fin.suc X)

    lift-var-advance-scope-trans : ∀ {Δ₀ Δ Δ′ Δ″} {Σ₀ : TyStore Δ₀}
        (S : PhysicalScope Σ₀ Δ) (χs : StoreChanges Δ Δ′)
        (ψs : StoreChanges Δ′ Δ″) (X : TyVar Δ)
      → liftVar (scope-trans (advance-future S χs)
          (advance-future (advance S χs) ψs)) X
        ≡ liftVar (advance-future S (χs ++ˢ ψs)) X
    lift-var-advance-scope-trans S χs ψs X =
      trans (lift-var-comp (advance-future S χs)
               (advance-future (advance S χs) ψs) X)
            (sym (lift-var-advance-append S χs ψs X))

    reassoc-source : ∀ {ΔI ΔP ΔI′ ΔI″}
        {S : PhysicalScope ΣI₀ ΔI} {T : PhysicalScope ΣP₀ ΔP}
        (χs : StoreChanges ΔI ΔI′) (ψs : StoreChanges ΔI′ ΔI″)
      → World (advance (advance S χs) ψs) T
      → World (advance S (χs ++ˢ ψs)) T
    reassoc-source [] ψs W′ = W′
    reassoc-source (keep ∷ χs) ψs W′ = reassoc-source χs ψs W′
    reassoc-source {S = S} (bind A ∷ χs) ψs W′ =
      reassoc-source {S = allocate S A} χs ψs W′

    reassoc-target : ∀ {ΔI ΔP ΔP′ ΔP″}
        {S : PhysicalScope ΣI₀ ΔI} {T : PhysicalScope ΣP₀ ΔP}
        (χs : StoreChanges ΔP ΔP′) (ψs : StoreChanges ΔP′ ΔP″)
      → World S (advance (advance T χs) ψs)
      → World S (advance T (χs ++ˢ ψs))
    reassoc-target [] ψs W′ = W′
    reassoc-target (keep ∷ χs) ψs W′ = reassoc-target χs ψs W′
    reassoc-target {T = T} (bind A ∷ χs) ψs W′ =
      reassoc-target {T = allocate T A} χs ψs W′

    reassoc-source-related : ∀ {ΔI ΔP ΔI′ ΔI″}
        {B : SemanticType}
        {S : PhysicalScope ΣI₀ ΔI} {T : PhysicalScope ΣP₀ ΔP}
        {χs : StoreChanges ΔI ΔI′} {ψs : StoreChanges ΔI′ ΔI″}
        {W′ : World (advance (advance S χs) ψs) T} {j U V}
      → related B W′ j U V
      → related B (reassoc-source χs ψs W′) j U V
    reassoc-source-related {χs = []} r = r
    reassoc-source-related {B = B} {χs = keep ∷ χs} {ψs = ψs} r =
      reassoc-source-related {B = B} {χs = χs} {ψs = ψs} r
    reassoc-source-related {B = B} {S = S}
        {χs = bind A ∷ χs} {ψs = ψs} r =
      reassoc-source-related {B = B} {S = allocate S A}
        {χs = χs} {ψs = ψs} r

    reassoc-target-related : ∀ {ΔI ΔP ΔP′ ΔP″}
        {B : SemanticType}
        {S : PhysicalScope ΣI₀ ΔI} {T : PhysicalScope ΣP₀ ΔP}
        {χs : StoreChanges ΔP ΔP′} {ψs : StoreChanges ΔP′ ΔP″}
        {W′ : World S (advance (advance T χs) ψs)} {j U V}
      → related B W′ j U V
      → related B (reassoc-target χs ψs W′) j U V
    reassoc-target-related {χs = []} r = r
    reassoc-target-related {B = B} {χs = keep ∷ χs} {ψs = ψs} r =
      reassoc-target-related {B = B} {χs = χs} {ψs = ψs} r
    reassoc-target-related {B = B} {T = T}
        {χs = bind A ∷ χs} {ψs = ψs} r =
      reassoc-target-related {B = B} {T = allocate T A}
        {χs = χs} {ψs = ψs} r

    reassoc-source-matched : ∀ {ΔI ΔP ΔI′ ΔI″}
        {S : PhysicalScope ΣI₀ ΔI} {T : PhysicalScope ΣP₀ ΔP}
        {χs : StoreChanges ΔI ΔI′} {ψs : StoreChanges ΔI′ ΔI″}
        {W′ : World (advance (advance S χs) ψs) T} {X Y}
      → Matched W′ X Y
      → Matched (reassoc-source χs ψs W′) X Y
    reassoc-source-matched {χs = []} p = p
    reassoc-source-matched {χs = keep ∷ χs} {ψs = ψs} p =
      reassoc-source-matched {χs = χs} {ψs = ψs} p
    reassoc-source-matched {S = S} {χs = bind A ∷ χs} {ψs = ψs} p =
      reassoc-source-matched {S = allocate S A} {χs = χs} {ψs = ψs} p

    reassoc-target-matched : ∀ {ΔI ΔP ΔP′ ΔP″}
        {S : PhysicalScope ΣI₀ ΔI} {T : PhysicalScope ΣP₀ ΔP}
        {χs : StoreChanges ΔP ΔP′} {ψs : StoreChanges ΔP′ ΔP″}
        {W′ : World S (advance (advance T χs) ψs)} {X Y}
      → Matched W′ X Y
      → Matched (reassoc-target χs ψs W′) X Y
    reassoc-target-matched {χs = []} p = p
    reassoc-target-matched {χs = keep ∷ χs} {ψs = ψs} p =
      reassoc-target-matched {χs = χs} {ψs = ψs} p
    reassoc-target-matched {T = T} {χs = bind A ∷ χs} {ψs = ψs} p =
      reassoc-target-matched {T = allocate T A} {χs = χs} {ψs = ψs} p

    reassoc-source-only : ∀ {ΔI ΔP ΔI′ ΔI″}
        {S : PhysicalScope ΣI₀ ΔI} {T : PhysicalScope ΣP₀ ΔP}
        {χs : StoreChanges ΔI ΔI′} {ψs : StoreChanges ΔI′ ΔI″}
        {W′ : World (advance (advance S χs) ψs) T} {Y}
      → PreciseOnly W′ Y
      → PreciseOnly (reassoc-source χs ψs W′) Y
    reassoc-source-only {χs = []} p = p
    reassoc-source-only {χs = keep ∷ χs} {ψs = ψs} p =
      reassoc-source-only {χs = χs} {ψs = ψs} p
    reassoc-source-only {S = S} {χs = bind A ∷ χs} {ψs = ψs} p =
      reassoc-source-only {S = allocate S A} {χs = χs} {ψs = ψs} p

    reassoc-target-only : ∀ {ΔI ΔP ΔP′ ΔP″}
        {S : PhysicalScope ΣI₀ ΔI} {T : PhysicalScope ΣP₀ ΔP}
        {χs : StoreChanges ΔP ΔP′} {ψs : StoreChanges ΔP′ ΔP″}
        {W′ : World S (advance (advance T χs) ψs)} {Y}
      → PreciseOnly W′ Y
      → PreciseOnly (reassoc-target χs ψs W′) Y
    reassoc-target-only {χs = []} p = p
    reassoc-target-only {χs = keep ∷ χs} {ψs = ψs} p =
      reassoc-target-only {χs = χs} {ψs = ψs} p
    reassoc-target-only {T = T} {χs = bind A ∷ χs} {ψs = ψs} p =
      reassoc-target-only {T = allocate T A} {χs = χs} {ψs = ψs} p

    result-world : ∀ {ΔI ΔP ΔI′ ΔP′ ΔI″ ΔP″}
        {S : PhysicalScope ΣI₀ ΔI} {T : PhysicalScope ΣP₀ ΔP}
        {χsI : StoreChanges ΔI ΔI′}
        {χsP : StoreChanges ΔP ΔP′}
        {ψsI : StoreChanges ΔI′ ΔI″}
        {ψsP : StoreChanges ΔP′ ΔP″}
      → World (advance (advance S χsI) ψsI)
          (advance (advance T χsP) ψsP)
      → World (advance S (χsI ++ˢ ψsI))
          (advance T (χsP ++ˢ ψsP))
    result-world {χsI = χsI} {χsP = χsP} {ψsI = ψsI} {ψsP = ψsP} W′ =
      reassoc-target χsP ψsP (reassoc-source χsI ψsI W′)

    result-related : ∀ {ΔI ΔP ΔI′ ΔP′ ΔI″ ΔP″}
        {B : SemanticType}
        {S : PhysicalScope ΣI₀ ΔI} {T : PhysicalScope ΣP₀ ΔP}
        {χsI : StoreChanges ΔI ΔI′}
        {χsP : StoreChanges ΔP ΔP′}
        {ψsI : StoreChanges ΔI′ ΔI″}
        {ψsP : StoreChanges ΔP′ ΔP″}
        {W′ : World (advance (advance S χsI) ψsI)
                (advance (advance T χsP) ψsP)}
        {j U V}
      → related B W′ j U V
      → related B (result-world {S = S} {T = T} {χsI = χsI}
          {χsP = χsP} {ψsI = ψsI} {ψsP = ψsP} W′) j U V
    result-related {B = B} {S = S} {T} {χsI} {χsP} {ψsI} {ψsP} r
      = reassoc-target-related {B = B} {χs = χsP} {ψs = ψsP}
          (reassoc-source-related {B = B} {χs = χsI} {ψs = ψsI} r)

    result-future : ∀ {ΔI ΔP ΔI′ ΔP′ ΔI″ ΔP″}
        {S : PhysicalScope ΣI₀ ΔI} {T : PhysicalScope ΣP₀ ΔP}
        {χsI : StoreChanges ΔI ΔI′}
        {χsP : StoreChanges ΔP ΔP′}
        {ψsI : StoreChanges ΔI′ ΔI″}
        {ψsP : StoreChanges ΔP′ ΔP″}
        {W : World S T}
        {W′ : World (advance S χsI) (advance T χsP)}
        {W″ : World (advance (advance S χsI) ψsI)
                (advance (advance T χsP) ψsP)}
      → Future (advance-future S χsI) (advance-future T χsP) W W′
      → Future (advance-future (advance S χsI) ψsI)
          (advance-future (advance T χsP) ψsP) W′ W″
      → Future (advance-future S (χsI ++ˢ ψsI))
          (advance-future T (χsP ++ˢ ψsP)) W
          (result-world {S = S} {T = T} {χsI = χsI}
            {χsP = χsP} {ψsI = ψsI} {ψsP = ψsP} W″)
    result-future {S = S} {T} {χsI} {χsP} {ψsI} {ψsP} f g
        = record
      { matched-future = λ {X} {Y} m →
          subst₂≡
            (λ X′ Y′ →
              Matched (result-world {S = S} {T = T} {χsI = χsI}
                {χsP = χsP} {ψsI = ψsI} {ψsP = ψsP} _) X′ Y′)
            (lift-var-advance-scope-trans S χsI ψsI X)
            (lift-var-advance-scope-trans T χsP ψsP Y)
            (reassoc-target-matched {χs = χsP} {ψs = ψsP}
              (reassoc-source-matched {χs = χsI} {ψs = ψsI}
                (matched-future (future-trans f g) m)))
      ; only-future = λ {Y} o →
          subst≡
            (λ Y′ →
              PreciseOnly (result-world {S = S} {T = T} {χsI = χsI}
                {χsP = χsP} {ψsI = ψsI} {ψsP = ψsP} _) Y′)
            (lift-var-advance-scope-trans T χsP ψsP Y)
            (reassoc-target-only {χs = χsP} {ψs = ψsP}
              (reassoc-source-only {χs = χsI} {ψs = ψsI}
                (only-future (future-trans f g) o)))
      }

    result-pack : ∀ {ΔI ΔP}
        {B : SemanticType}
        {S : PhysicalScope ΣI₀ ΔI} {T : PhysicalScope ΣP₀ ΔP}
        {k L R}
      → (resultI resultI′ : E.EvalResult L)
      → (resultP resultP′ : E.EvalResult R)
        {W : World S T}
        {W′ : World (advance S (E.changes resultI′))
                (advance T (E.changes resultP′))}
      → resultI ≡ resultI′
      → resultP ≡ resultP′
      → Future (advance-future S (E.changes resultI′))
          (advance-future T (E.changes resultP′)) W W′
      → related B W′ k (E.term resultI′) (E.term resultP′)
      → ∃[ W″ ]
          Future (advance-future S (E.changes resultI))
            (advance-future T (E.changes resultP)) W W″
          × related B W″ k (E.term resultI) (E.term resultP)
    result-pack _ _ _ _ refl refl ext r = _ , ext , r

  frame-observed : ∀ {ΔI ΔP} {A B : SemanticType}
      {S : PhysicalScope ΣI₀ ΔI} {T : PhysicalScope ΣP₀ ΔP}
      {W : World S T} {k M N}
      (fI : I.Frm ΔI) (fP : P.Frm ΔP)
    → (∀ {ΔI′ ΔP′}
        (χsI : StoreChanges ΔI ΔI′)
        (χsP : StoreChanges ΔP ΔP′)
        {W′ : World (advance S χsI) (advance T χsP)}
        {j U V}
      → Future (advance-future S χsI) (advance-future T χsP) W W′
      → j ≤ k
      → related A W′ j U V
      → Observed B W′ j
          (I.plug (I.transports χsI fI) U)
          (P.plug (P.transports χsP fP) V))
    → Observed A W k M N
    → Observed B W k (I.plug fI M) (P.plug fP N)
  frame-observed {A = A} {B} {S} {T} {W} {k} {M} {N}
      fI fP plug-values operand-related = record
    { forward-return = forward
    ; backward-return = backward
    ; forward-blame = forward-blame-frame
    }
    where
    forward : ∀ {n} {resultI : E.EvalResult (I.plug fI M)}
      → n < k
      → interpretFrom (scopeStore S) n (I.plug fI M) ≡ returned resultI
      → (∃[ m ] ∃[ resultP ]
          (interpretFrom (scopeStore T) m (P.plug fP N) ≡ returned resultP)
          × ∃[ W′ ]
            Future (advance-future S (E.changes resultI))
              (advance-future T (E.changes resultP)) W W′
            × related B W′ (k ∸ n) (E.term resultI) (E.term resultP))
        ⊎ (∃[ m ] BlamesFrom (scopeStore T) m (P.plug fP N))
    forward {n = n} {resultI = resultI} n<k result-eq
        with I.return-phases-of {Σ = scopeStore S} {gas = n}
          fI {M = M} {result = resultI} result-eq
    forward {n = n} {resultI = resultI} n<k result-eq
        | I.return-phases operandGas operandResultI operandReturn
            callGas callResultI callReturn result-split gas-split
        with Observed.forward-return operand-related
          {n = operandGas} {outI = operandResultI}
          operandGas<k operandReturn
      where
      phases<k : operandGas + callGas < k
      phases<k = sum-bound-from-split
        {a = operandGas} {b = callGas} {n = n} {k = k}
        gas-split n<k

      operandGas<k = first-of-two<
        {a = operandGas} {b = callGas} {k = k} phases<k
    forward {n = n} n<k result-eq
        | I.return-phases operandGas operandResultI operandReturn
            callGas callResultI callReturn result-split gas-split
        | inj₂ (operandGasP , operandBlameP)
        with P.operand-blame-expand
          {Σ = scopeStore T} {operandGas = operandGasP}
          fP {M = N} operandBlameP
    forward {n = n} n<k result-eq
        | I.return-phases operandGas operandResultI operandReturn
            callGas callResultI callReturn result-split gas-split
        | inj₂ (operandGasP , operandBlameP)
        | wholeGasP , wholeBlameP = inj₂ (wholeGasP , wholeBlameP)
    forward {n = n} {resultI = resultI} n<k result-eq
        | I.return-phases operandGas operandResultI operandReturn
            callGas callResultI callReturn result-split gas-split
        | inj₁ (operandGasP , operandResultP , operandReturnP ,
            Wop , operandFuture , operandValueRelated)
        with Observed.forward-return call-related
          {n = callGas} {outI = callResultI}
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
        {gas = callGas} {result = callResultI}
        (advance-store S (E.changes operandResultI)) callReturn

      call-related : Observed B Wop (k ∸ operandGas)
        (I.plug (I.transports (E.changes operandResultI) fI)
          (E.term operandResultI))
        (P.plug (P.transports (E.changes operandResultP) fP)
          (E.term operandResultP))
      call-related = plug-values
        (E.changes operandResultI) (E.changes operandResultP)
        {j = k ∸ operandGas} operandFuture (m∸n≤m k operandGas)
        operandValueRelated
    forward {n = n} n<k result-eq
        | I.return-phases operandGas operandResultI operandReturn
            callGas callResultI callReturn result-split gas-split
        | inj₁ (operandGasP , operandResultP , operandReturnP ,
            Wop , operandFuture , operandValueRelated)
        | inj₂ (callGasP , callBlameP)
        with P.call-blame-expand
          {Σ = scopeStore T}
          {operandGas = operandGasP} {callGas = callGasP}
          fP {M = N} {operandResult = operandResultP}
          operandReturnP
          (blame-store-reindex {gas = callGasP}
            (sym (advance-store T (E.changes operandResultP)))
            callBlameP)
    forward {n = n} n<k result-eq
        | I.return-phases operandGas operandResultI operandReturn
            callGas callResultI callReturn result-split gas-split
        | inj₁ (operandGasP , operandResultP , operandReturnP ,
            Wop , operandFuture , operandValueRelated)
        | inj₂ (callGasP , callBlameP)
        | wholeGasP , wholeBlameP = inj₂ (wholeGasP , wholeBlameP)
    forward {n = n} {resultI = resultI} n<k result-eq
        | I.return-phases operandGas operandResultI operandReturn
            callGas callResultI callReturn result-split gas-split
        | inj₁ (operandGasP , operandResultP , operandReturnP ,
            Wop , operandFuture , operandValueRelated)
        | inj₁ (callGasP , callResultP , callReturnP ,
            Wcall , callFuture , callValueRelated)
        with P.return-expand {Σ = scopeStore T}
          {operandGas = operandGasP} {callGas = callGasP}
          fP {M = N} {operandResult = operandResultP}
          {callResult = callResultP} operandReturnP
          (return-store-reindex {gas = callGasP}
            {result = callResultP}
            (sym (advance-store T (E.changes operandResultP)))
            callReturnP)
    forward {n = n} {resultI = resultI} n<k result-eq
        | I.return-phases operandGas operandResultI operandReturn
            callGas callResultI callReturn result-split gas-split
        | inj₁ (operandGasP , operandResultP , operandReturnP ,
            Wop , operandFuture , operandValueRelated)
        | inj₁ (callGasP , callResultP , callReturnP ,
            Wcall , callFuture , callValueRelated)
        | wholeGasP , wholeReturnP
        with result-pack {B = B} {S = S} {T = T}
          resultI (I.sequence-result fI operandResultI callResultI)
          (P.sequence-result fP operandResultP callResultP)
          (P.sequence-result fP operandResultP callResultP)
          {W = W}
          result-split refl
          (result-future {S = S} {T = T}
            {χsI = E.changes operandResultI}
            {χsP = E.changes operandResultP}
            {ψsI = E.changes callResultI}
            {ψsP = E.changes callResultP}
            operandFuture callFuture)
          (result-related {B = B} {S = S} {T = T}
            {χsI = E.changes operandResultI}
            {χsP = E.changes operandResultP}
            {ψsI = E.changes callResultI}
            {ψsP = E.changes callResultP}
            (subst≡ (λ j → related B Wcall j
                (E.term callResultI) (E.term callResultP))
              (trans (subtract-phases k operandGas callGas)
                (cong (k ∸_) gas-split))
              callValueRelated))
    ... | Wfinal , finalFuture , finalRelated =
      inj₁ (wholeGasP , P.sequence-result fP operandResultP callResultP ,
        wholeReturnP , Wfinal , finalFuture , finalRelated)
    backward : ∀ {n} {resultP : E.EvalResult (P.plug fP N)}
      → n < k
      → interpretFrom (scopeStore T) n (P.plug fP N) ≡ returned resultP
      → ∃[ m ] ∃[ resultI ]
          (interpretFrom (scopeStore S) m (I.plug fI M) ≡ returned resultI)
          × ∃[ W′ ]
            Future (advance-future S (E.changes resultI))
              (advance-future T (E.changes resultP)) W W′
            × related B W′ (k ∸ n) (E.term resultI) (E.term resultP)
    backward {n = n} {resultP = resultP} n<k result-eq
        with P.return-phases-of {Σ = scopeStore T} {gas = n}
          fP {M = N} {result = resultP} result-eq
    backward {n = n} {resultP = resultP} n<k result-eq
        | P.return-phases operandGas operandResultP operandReturn
            callGas callResultP callReturn result-split gas-split
        with Observed.backward-return operand-related
          {n = operandGas} {outP = operandResultP}
          operandGas<k operandReturn
      where
      phases<k : operandGas + callGas < k
      phases<k = sum-bound-from-split
        {a = operandGas} {b = callGas} {n = n} {k = k}
        gas-split n<k

      operandGas<k = first-of-two<
        {a = operandGas} {b = callGas} {k = k} phases<k
    backward {n = n} {resultP = resultP} n<k result-eq
        | P.return-phases operandGas operandResultP operandReturn
            callGas callResultP callReturn result-split gas-split
        | operandGasI , operandResultI , operandReturnI ,
            Wop , operandFuture , operandValueRelated
        with Observed.backward-return call-related
          {n = callGas} {outP = callResultP}
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
        {gas = callGas} {result = callResultP}
        (advance-store T (E.changes operandResultP)) callReturn

      call-related : Observed B Wop (k ∸ operandGas)
        (I.plug (I.transports (E.changes operandResultI) fI)
          (E.term operandResultI))
        (P.plug (P.transports (E.changes operandResultP) fP)
          (E.term operandResultP))
      call-related = plug-values
        (E.changes operandResultI) (E.changes operandResultP)
        {j = k ∸ operandGas} operandFuture (m∸n≤m k operandGas)
        operandValueRelated
    backward {n = n} {resultP = resultP} n<k result-eq
        | P.return-phases operandGas operandResultP operandReturn
            callGas callResultP callReturn result-split gas-split
        | operandGasI , operandResultI , operandReturnI ,
            Wop , operandFuture , operandValueRelated
        | callGasI , callResultI , callReturnI ,
            Wcall , callFuture , callValueRelated
        with I.return-expand {Σ = scopeStore S}
          {operandGas = operandGasI} {callGas = callGasI}
          fI {M = M} {operandResult = operandResultI}
          {callResult = callResultI} operandReturnI
          (return-store-reindex {gas = callGasI}
            {result = callResultI}
            (sym (advance-store S (E.changes operandResultI)))
            callReturnI)
    backward {n = n} {resultP = resultP} n<k result-eq
        | P.return-phases operandGas operandResultP operandReturn
            callGas callResultP callReturn result-split gas-split
        | operandGasI , operandResultI , operandReturnI ,
            Wop , operandFuture , operandValueRelated
        | callGasI , callResultI , callReturnI ,
            Wcall , callFuture , callValueRelated
        | wholeGasI , wholeReturnI
        with result-pack {B = B} {S = S} {T = T}
          (I.sequence-result fI operandResultI callResultI)
          (I.sequence-result fI operandResultI callResultI)
          resultP (P.sequence-result fP operandResultP callResultP)
          {W = W}
          refl result-split
          (result-future {S = S} {T = T}
            {χsI = E.changes operandResultI}
            {χsP = E.changes operandResultP}
            {ψsI = E.changes callResultI}
            {ψsP = E.changes callResultP}
            operandFuture callFuture)
          (result-related {B = B} {S = S} {T = T}
            {χsI = E.changes operandResultI}
            {χsP = E.changes operandResultP}
            {ψsI = E.changes callResultI}
            {ψsP = E.changes callResultP}
            (subst≡ (λ j → related B Wcall j
                (E.term callResultI) (E.term callResultP))
              (trans (subtract-phases k operandGas callGas)
                (cong (k ∸_) gas-split))
              callValueRelated))
    ... | Wfinal , finalFuture , finalRelated =
      wholeGasI , I.sequence-result fI operandResultI callResultI ,
      wholeReturnI , Wfinal , finalFuture , finalRelated
    forward-blame-frame : ∀ {n}
      → n < k
      → BlamesFrom (scopeStore S) n (I.plug fI M)
      → ∃[ m ] BlamesFrom (scopeStore T) m (P.plug fP N)
    forward-blame-frame {n = n} n<k blaming
        with I.blame-phases-of {Σ = scopeStore S} {gas = n}
          fI {M = M} blaming
    forward-blame-frame {n = n} n<k blaming
        | I.operand-phase-blames operandGas operandBlame operandGas≤n
        with Observed.forward-blame operand-related
          (≤-trans (s≤s operandGas≤n) n<k) operandBlame
    forward-blame-frame {n = n} n<k blaming
        | I.operand-phase-blames operandGas operandBlame operandGas≤n
        | operandGasP , operandBlameP
        with P.operand-blame-expand
          {Σ = scopeStore T} {operandGas = operandGasP}
          fP {M = N} operandBlameP
    forward-blame-frame {n = n} n<k blaming
        | I.operand-phase-blames operandGas operandBlame operandGas≤n
        | operandGasP , operandBlameP
        | wholeGasP , wholeBlameP = wholeGasP , wholeBlameP
    forward-blame-frame {n = n} n<k blaming
        | I.call-phase-blames operandGas operandResultI operandReturn
            callGas callBlame phases≤n
        with Observed.forward-return operand-related
          {n = operandGas} {outI = operandResultI}
          operandGas<k operandReturn
      where
      phases<k = ≤-trans (s≤s phases≤n) n<k
      operandGas<k = first-of-two< phases<k
    forward-blame-frame {n = n} n<k blaming
        | I.call-phase-blames operandGas operandResultI operandReturn
            callGas callBlame phases≤n
        | inj₂ (operandGasP , operandBlameP)
        with P.operand-blame-expand
          {Σ = scopeStore T} {operandGas = operandGasP}
          fP {M = N} operandBlameP
    forward-blame-frame {n = n} n<k blaming
        | I.call-phase-blames operandGas operandResultI operandReturn
            callGas callBlame phases≤n
        | inj₂ (operandGasP , operandBlameP)
        | wholeGasP , wholeBlameP = wholeGasP , wholeBlameP
    forward-blame-frame {n = n} n<k blaming
        | I.call-phase-blames operandGas operandResultI operandReturn
            callGas callBlame phases≤n
        | inj₁ (operandGasP , operandResultP , operandReturnP ,
            Wop , operandFuture , operandValueRelated)
        with Observed.forward-blame call-related
          callGas<k callBlame-at-scope
      where
      phases<k = ≤-trans (s≤s phases≤n) n<k
      callGas<k : callGas < k ∸ operandGas
      callGas<k = drop-left-<
        {a = operandGas} {b = callGas} {k = k} phases<k
      callBlame-at-scope = blame-store-reindex {gas = callGas}
        (advance-store S (E.changes operandResultI)) callBlame

      call-related : Observed B Wop (k ∸ operandGas)
        (I.plug (I.transports (E.changes operandResultI) fI)
          (E.term operandResultI))
        (P.plug (P.transports (E.changes operandResultP) fP)
          (E.term operandResultP))
      call-related = plug-values
        (E.changes operandResultI) (E.changes operandResultP)
        {j = k ∸ operandGas} operandFuture (m∸n≤m k operandGas)
        operandValueRelated
    forward-blame-frame {n = n} n<k blaming
        | I.call-phase-blames operandGas operandResultI operandReturn
            callGas callBlame phases≤n
        | inj₁ (operandGasP , operandResultP , operandReturnP ,
            Wop , operandFuture , operandValueRelated)
        | callGasP , callBlameP
        with P.call-blame-expand
          {Σ = scopeStore T}
          {operandGas = operandGasP} {callGas = callGasP}
          fP {M = N} {operandResult = operandResultP}
          operandReturnP
          (blame-store-reindex {gas = callGasP}
            (sym (advance-store T (E.changes operandResultP)))
            callBlameP)
    forward-blame-frame {n = n} n<k blaming
        | I.call-phase-blames operandGas operandResultI operandReturn
            callGas callBlame phases≤n
        | inj₁ (operandGasP , operandResultP , operandReturnP ,
            Wop , operandFuture , operandValueRelated)
        | callGasP , callBlameP
        | wholeGasP , wholeBlameP = wholeGasP , wholeBlameP
