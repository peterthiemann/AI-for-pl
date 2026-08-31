module proof.LR-narrow.IntegratedModel where

-- File Charter:
--   * Experimental A+B interface: observations retain independent physical
--     histories AND an explicitly extended, persistent nominal world.
--   * Constructs natural and arrow meanings, proves index/future closure,
--     and introduces observations from actual evaluator returns or blame.
--   * Universal experiments use a stated natural-argument test family; this
--     is not a full interpretation of arbitrary polymorphic instantiation.
--   * No live LR, CTI, or operational rule is changed.

open import Data.List using ([])
open import Data.Nat using (ℕ; suc; _≤_; _<_; _∸_)
open import Data.Nat.Properties using (≤-trans; ∸-monoˡ-≤; m∸n≤m)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong) renaming (subst to subst≡; subst₂ to subst₂≡)

open import Types
open import TyStore
open import TermCtx using (Z)
open import CastTerms
open import Primitives using (κℕ)
open import Interpreter
import Eval as E
open import LR-narrow.Computation using (BlamesFrom)
open import LR-narrow.LogicalRelation using (SameBaseValue; same-natural)
open import proof.LR-narrow.Application
  using (eval-from-return; eval-from-blame; value-return-exact)
open import proof.LR-narrow.ScopedIdentity
  using (identity-return; lift-identity)
open import proof.LR-narrow.TargetEvaluation
  using (return-result-unique; eval-terminal-unique)
open import proof.LR-narrow.PhysicalScope
import proof.LR-narrow.IntegratedWorld as IW

module Model {ΔI0 ΔP0} (ΣI0 : TyStore ΔI0) (ΣP0 : TyStore ΔP0) where

  module Worlds = IW.Worlds ΣI0 ΣP0
  open Worlds

  record SemanticType : Set₁ where
    field
      impreciseTy : Ty ΔI0
      preciseTy : Ty ΔP0
      related : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP}
        → World S T → ℕ → Term ΔI → Term ΔP → Set
      imprecise-value : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP} {W : World S T} {k U V}
        → related W k U V → Value U
      precise-value : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP} {W : World S T} {k U V}
        → related W k U V → Value V
      imprecise-typed : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP} {W : World S T} {k U V}
        → related W k U V
        → ⟨ ΔI , scopeStore S , [] ⟩ ⊢ U ⦂ scopeTy S impreciseTy
      precise-typed : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP} {W : World S T} {k U V}
        → related W k U V
        → ⟨ ΔP , scopeStore T , [] ⟩ ⊢ V ⦂ scopeTy T preciseTy
      downward : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP} {W : World S T} {j k U V}
        → j ≤ k → related W k U V → related W j U V
      future-closed : ∀ {ΔI ΔP ΔI′ ΔP′}
          {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
          {S′ : PhysicalScope ΣI0 ΔI′} {T′ : PhysicalScope ΣP0 ΔP′}
          {W : World S T} {W′ : World S′ T′} {k U V}
        → (p : ScopeFuture S S′) → (q : ScopeFuture T T′)
        → Future p q W W′ → related W k U V
        → related W′ k (liftTerm p U) (liftTerm q V)

  open SemanticType public

  record Observed {ΔI ΔP} (A : SemanticType)
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      (W : World S T) (k : ℕ) (M : Term ΔI) (N : Term ΔP) : Set where
    field
      forward-return : ∀ {n} {outI : E.EvalResult M}
        → n < k → interpretFrom (scopeStore S) n M ≡ returned outI
        → (∃[ m ] ∃[ outP ]
            (interpretFrom (scopeStore T) m N ≡ returned outP)
            × ∃[ W′ ]
              Future (advance-future S (E.changes outI))
                (advance-future T (E.changes outP)) W W′
              × related A W′ (k ∸ n) (E.term outI) (E.term outP))
          ⊎ (∃[ m ] BlamesFrom (scopeStore T) m N)
      backward-return : ∀ {n} {outP : E.EvalResult N}
        → n < k → interpretFrom (scopeStore T) n N ≡ returned outP
        → ∃[ m ] ∃[ outI ]
            (interpretFrom (scopeStore S) m M ≡ returned outI)
            × ∃[ W′ ]
              Future (advance-future S (E.changes outI))
                (advance-future T (E.changes outP)) W W′
              × related A W′ (k ∸ n) (E.term outI) (E.term outP)
      forward-blame : ∀ {n}
        → n < k → BlamesFrom (scopeStore S) n M
        → ∃[ m ] BlamesFrom (scopeStore T) m N

  observed-downward : ∀ {ΔI ΔP} {A : SemanticType}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {W : World S T} {j k M N}
    → j ≤ k → Observed A W k M N → Observed A W j M N
  observed-downward {A = A} {S} {T} {W} {j} {k} {M} {N} j≤k c = record
    { forward-return = λ { {n} {outI} n<j ret → forward n {outI}
        (Observed.forward-return c (≤-trans n<j j≤k) ret) }
    ; backward-return = λ { {n} {outP} n<j ret → backward n {outP}
        (Observed.backward-return c (≤-trans n<j j≤k) ret) }
    ; forward-blame = λ n<j → Observed.forward-blame c (≤-trans n<j j≤k)
    }
    where
    forward : ∀ n {outI : E.EvalResult M}
      → ((∃[ m ] ∃[ outP ]
          (interpretFrom (scopeStore T) m N ≡ returned outP)
          × ∃[ W′ ] Future (advance-future S (E.changes outI))
              (advance-future T (E.changes outP)) W W′
            × related A W′ (k ∸ n) (E.term outI) (E.term outP))
        ⊎ (∃[ m ] BlamesFrom (scopeStore T) m N))
      → ((∃[ m ] ∃[ outP ]
          (interpretFrom (scopeStore T) m N ≡ returned outP)
          × ∃[ W′ ] Future (advance-future S (E.changes outI))
              (advance-future T (E.changes outP)) W W′
            × related A W′ (j ∸ n) (E.term outI) (E.term outP))
        ⊎ (∃[ m ] BlamesFrom (scopeStore T) m N))
    forward n (inj₁ (m , out , ret , W′ , ext , r)) =
      inj₁ (m , out , ret , W′ , ext , downward A (∸-monoˡ-≤ n j≤k) r)
    forward n (inj₂ b) = inj₂ b

    backward : ∀ n {outP : E.EvalResult N}
      → (∃[ m ] ∃[ outI ]
          (interpretFrom (scopeStore S) m M ≡ returned outI)
          × ∃[ W′ ] Future (advance-future S (E.changes outI))
              (advance-future T (E.changes outP)) W W′
            × related A W′ (k ∸ n) (E.term outI) (E.term outP))
      → (∃[ m ] ∃[ outI ]
          (interpretFrom (scopeStore S) m M ≡ returned outI)
          × ∃[ W′ ] Future (advance-future S (E.changes outI))
              (advance-future T (E.changes outP)) W W′
            × related A W′ (j ∸ n) (E.term outI) (E.term outP))
    backward n (m , out , ret , W′ , ext , r) =
      m , out , ret , W′ , ext , downward A (∸-monoˡ-≤ n j≤k) r

  natural : SemanticType
  natural = record
    { impreciseTy = ‵ `ℕ
    ; preciseTy = ‵ `ℕ
    ; related = λ W k → SameBaseValue `ℕ
    ; imprecise-value = λ { (same-natural n) → $ (κℕ n) }
    ; precise-value = λ { (same-natural n) → $ (κℕ n) }
    ; imprecise-typed = λ { {S = S} (same-natural n) →
        subst≡ (λ A → ⟨ _ , scopeStore S , [] ⟩ ⊢ $ (κℕ n) ⦂ A)
          (sym (scope-natural S)) (⊢$ (κℕ n)) }
    ; precise-typed = λ { {T = T} (same-natural n) →
        subst≡ (λ A → ⟨ _ , scopeStore T , [] ⟩ ⊢ $ (κℕ n) ⦂ A)
          (sym (scope-natural T)) (⊢$ (κℕ n)) }
    ; downward = λ j≤k r → r
    ; future-closed = λ { p q ext (same-natural n) →
        subst₂≡ (SameBaseValue `ℕ)
          (sym (lift-constant p (κℕ n))) (sym (lift-constant q (κℕ n)))
          (same-natural n) }
    }

  record ArrowValues {ΔI ΔP} (A B : SemanticType)
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      (W : World S T) (k : ℕ) (F : Term ΔI) (G : Term ΔP) : Set where
    constructor arrow-values
    field
      valueI : Value F
      valueP : Value G
      typedI : ⟨ ΔI , scopeStore S , [] ⟩
        ⊢ F ⦂ scopeTy S (impreciseTy A ⇒ impreciseTy B)
      typedP : ⟨ ΔP , scopeStore T , [] ⟩
        ⊢ G ⦂ scopeTy T (preciseTy A ⇒ preciseTy B)
      call : ∀ {ΔI′ ΔP′}
          {S′ : PhysicalScope ΣI0 ΔI′} {T′ : PhysicalScope ΣP0 ΔP′}
          {W′ : World S′ T′} {j U V}
        → (p : ScopeFuture S S′) → (q : ScopeFuture T T′)
        → Future p q W W′ → j < k → related A W′ j U V
        → Observed B W′ j (liftTerm p F · U) (liftTerm q G · V)

  arrow : SemanticType → SemanticType → SemanticType
  arrow A B = record
    { impreciseTy = impreciseTy A ⇒ impreciseTy B
    ; preciseTy = preciseTy A ⇒ preciseTy B
    ; related = ArrowValues A B
    ; imprecise-value = ArrowValues.valueI
    ; precise-value = ArrowValues.valueP
    ; imprecise-typed = ArrowValues.typedI
    ; precise-typed = ArrowValues.typedP
    ; downward = λ j≤k r → arrow-values
        (ArrowValues.valueI r) (ArrowValues.valueP r)
        (ArrowValues.typedI r) (ArrowValues.typedP r)
        (λ p q ext n<j args → ArrowValues.call r p q ext
          (≤-trans n<j j≤k) args)
    ; future-closed = λ { {U = F} {V = G} p q ext r → arrow-values
        (lift-value p (ArrowValues.valueI r))
        (lift-value q (ArrowValues.valueP r))
        (lift-root-typed p (ArrowValues.typedI r))
        (lift-root-typed q (ArrowValues.typedP r))
        (λ { {U = U} {V = V} p′ q′ ext′ n<k args →
          subst₂≡ (Observed B _ _)
            (cong (_· U) (lift-term-comp p p′ F))
            (cong (_· V) (lift-term-comp q q′ G))
            (ArrowValues.call r (scope-trans p p′) (scope-trans q q′)
              (future-trans ext ext′) n<k args) }) }
    }

  observed-from-returns : ∀ {ΔI ΔP} {A : SemanticType}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {W : World S T} {k M N gasI gasP}
      {outI : E.EvalResult M} {outP : E.EvalResult N}
      {W′ : World (advance S (E.changes outI))
                  (advance T (E.changes outP))}
    → interpretFrom (scopeStore S) gasI M ≡ returned outI
    → interpretFrom (scopeStore T) gasP N ≡ returned outP
    → Future (advance-future S (E.changes outI))
        (advance-future T (E.changes outP)) W W′
    → related A W′ k (E.term outI) (E.term outP)
    → Observed A W k M N
  observed-from-returns {A = A} {S} {T} {W} {k} {M} {N} {gasI} {gasP}
      {outI} {outP} {W′} retI retP ext r = record
    { forward-return = forward
    ; backward-return = backward
    ; forward-blame = no-blame
    }
    where
    forward : ∀ {n} {out : E.EvalResult M}
      → n < k → interpretFrom (scopeStore S) n M ≡ returned out
      → (∃[ m ] ∃[ out′ ]
          (interpretFrom (scopeStore T) m N ≡ returned out′)
          × ∃[ W″ ] Future (advance-future S (E.changes out))
              (advance-future T (E.changes out′)) W W″
            × related A W″ (k ∸ n) (E.term out) (E.term out′))
        ⊎ (∃[ m ] BlamesFrom (scopeStore T) m N)
    forward {n} n<k ret with return-result-unique {Σ = scopeStore S}
      {leftGas = n} {rightGas = gasI} ret retI
    forward {n} n<k ret | refl =
      inj₁ (gasP , outP , retP , W′ , ext , downward A (m∸n≤m k n) r)

    backward : ∀ {n} {out : E.EvalResult N}
      → n < k → interpretFrom (scopeStore T) n N ≡ returned out
      → ∃[ m ] ∃[ out′ ]
          (interpretFrom (scopeStore S) m M ≡ returned out′)
          × ∃[ W″ ] Future (advance-future S (E.changes out′))
              (advance-future T (E.changes out)) W W″
            × related A W″ (k ∸ n) (E.term out′) (E.term out)
    backward {n} n<k ret with return-result-unique {Σ = scopeStore T}
      {leftGas = n} {rightGas = gasP} ret retP
    backward {n} n<k ret | refl =
      gasI , outI , retI , W′ , ext , downward A (m∸n≤m k n) r

    no-blame : ∀ {n} → n < k → BlamesFrom (scopeStore S) n M
      → ∃[ m ] BlamesFrom (scopeStore T) m N
    no-blame {n} n<k (Δ′ , χ , tr , bl)
        with eval-terminal-unique {Σ = scopeStore S}
          {leftGas = gasI} {rightGas = n}
          (eval-from-return {Σ = scopeStore S} {gas = gasI} retI)
          (eval-from-blame {Σ = scopeStore S} {gas = n} bl)
    no-blame n<k (Δ′ , χ , tr , bl) | ()

  observed-from-right-blame : ∀ {ΔI ΔP} {A : SemanticType}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {W : World S T} {k M N gas}
    → BlamesFrom (scopeStore T) gas N → Observed A W k M N
  observed-from-right-blame {A = A} {S} {T} {W} {k} {M} {N} {gas}
      blameN@(Δ′ , χ , tr , bl) = record
    { forward-return = λ n<k ret → inj₂ (gas , blameN)
    ; backward-return = no-return
    ; forward-blame = λ n<k b → gas , blameN
    }
    where
    no-return : ∀ {n} {out : E.EvalResult N}
      → n < k → interpretFrom (scopeStore T) n N ≡ returned out
      → ∃[ m ] ∃[ out′ ]
          (interpretFrom (scopeStore S) m M ≡ returned out′)
          × ∃[ W′ ] Future (advance-future S (E.changes out′))
              (advance-future T (E.changes out)) W W′
            × related A W′ (k ∸ n) (E.term out′) (E.term out)
    no-return {n} n<k ret with eval-terminal-unique {Σ = scopeStore T}
      {leftGas = n} {rightGas = gas}
      (eval-from-return {Σ = scopeStore T} {gas = n} ret)
      (eval-from-blame {Σ = scopeStore T} {gas = gas} bl)
    no-return n<k ret | ()

  values-observed : ∀ {ΔI ΔP} (A : SemanticType)
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {W : World S T} {k U V}
    → related A W k U V → Observed A W k U V
  values-observed A {S} {T} r = observed-from-returns
    {gasI = 0} {gasP = 0}
    (value-return-exact {Σ = scopeStore S} 0 (imprecise-value A r))
    (value-return-exact {Σ = scopeStore T} 0 (precise-value A r))
    future-refl r

  identity-related : ∀ {ΔI ΔP} (A : SemanticType)
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      (W : World S T) k
    → related (arrow A A) W k (ƛ (` 0)) (ƛ (` 0))
  identity-related A {S} {T} W k =
    arrow-values (ƛ (` 0)) (ƛ (` 0))
      (subst≡ (λ C → ⟨ _ , scopeStore S , [] ⟩ ⊢ ƛ (` 0) ⦂ C)
        (sym (scope-arrow S (impreciseTy A) (impreciseTy A)))
        (⊢ƛ (⊢` Z)))
      (subst≡ (λ C → ⟨ _ , scopeStore T , [] ⟩ ⊢ ƛ (` 0) ⦂ C)
        (sym (scope-arrow T (preciseTy A) (preciseTy A)))
        (⊢ƛ (⊢` Z))) call
    where
    call : ∀ {ΔI′ ΔP′}
        {S′ : PhysicalScope ΣI0 ΔI′} {T′ : PhysicalScope ΣP0 ΔP′}
        {W′ : World S′ T′} {j U V}
      → (p : ScopeFuture S S′) → (q : ScopeFuture T T′)
      → Future p q W W′ → j < k → related A W′ j U V
      → Observed A W′ j
          (liftTerm p (ƛ (` 0)) · U) (liftTerm q (ƛ (` 0)) · V)
    call {S′ = S′} {T′} p q ext j<k args
        rewrite lift-identity p | lift-identity q
        with identity-return (scopeStore S′) (imprecise-value A args)
           | identity-return (scopeStore T′) (precise-value A args)
    call {S′ = S′} {T′} p q ext j<k args | vU , retU | vV , retV =
      observed-from-returns {S = S′} {T = T′} {gasI = 1} {gasP = 1}
        retU retV future-refl args

  -- This is deliberately a one-argument test family, not an interpretation
  -- of arbitrary universal instantiation. The endpoint equations expose the
  -- fragment restriction; no compatibility theorem is assumed by the family.

  record NaturalFamily (CI : Ty (suc ΔI0))
      (CP : Ty (suc ΔP0)) : Set₁ where
    field
      result : SemanticType
      resultI : ∀ {ΔI} (S : PhysicalScope ΣI0 ΔI)
        → scopeTy S (impreciseTy result) ≡ scopeBody S CI [ ‵ `ℕ ]ᵗ
      resultP : ∀ {ΔP} (T : PhysicalScope ΣP0 ΔP)
        → scopeTy T (preciseTy result) ≡ scopeBody T CP [ ‵ `ℕ ]ᵗ

  record NaturalUniversalValues {ΔI ΔP} {CI CP}
      (F : NaturalFamily CI CP)
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      (W : World S T) (k : ℕ) (U : Term ΔI) (V : Term ΔP) : Set where
    constructor natural-universal-values
    field
      valueI : Value U
      valueP : Value V
      typedI : ⟨ ΔI , scopeStore S , [] ⟩ ⊢ U ⦂ scopeTy S (`∀ CI)
      typedP : ⟨ ΔP , scopeStore T , [] ⟩ ⊢ V ⦂ scopeTy T (`∀ CP)
      instantiate : ∀ {ΔI′ ΔP′}
          {S′ : PhysicalScope ΣI0 ΔI′} {T′ : PhysicalScope ΣP0 ΔP′}
          {W′ : World S′ T′} {j}
        → (p : ScopeFuture S S′) → (q : ScopeFuture T T′)
        → Future p q W W′ → j < k
        → Observed (NaturalFamily.result F) W′ j
            (liftTerm p U ⦂∀ scopeBody S′ CI [ ‵ `ℕ ])
            (liftTerm q V ⦂∀ scopeBody T′ CP [ ‵ `ℕ ])

  naturalUniversal : ∀ {CI CP} → NaturalFamily CI CP → SemanticType
  naturalUniversal {CI} {CP} F = record
    { impreciseTy = `∀ CI
    ; preciseTy = `∀ CP
    ; related = NaturalUniversalValues F
    ; imprecise-value = NaturalUniversalValues.valueI
    ; precise-value = NaturalUniversalValues.valueP
    ; imprecise-typed = NaturalUniversalValues.typedI
    ; precise-typed = NaturalUniversalValues.typedP
    ; downward = λ j≤k r → natural-universal-values
        (NaturalUniversalValues.valueI r) (NaturalUniversalValues.valueP r)
        (NaturalUniversalValues.typedI r) (NaturalUniversalValues.typedP r)
        (λ p q ext n<j → NaturalUniversalValues.instantiate r p q ext
          (≤-trans n<j j≤k))
    ; future-closed = λ { {U = U} {V = V} p q ext r →
        natural-universal-values
          (lift-value p (NaturalUniversalValues.valueI r))
          (lift-value q (NaturalUniversalValues.valueP r))
          (lift-root-typed p (NaturalUniversalValues.typedI r))
          (lift-root-typed q (NaturalUniversalValues.typedP r))
          (λ { {S′ = S′} {T′ = T′} p′ q′ ext′ n<k →
            subst₂≡ (Observed (NaturalFamily.result F) _ _)
              (cong (λ L → L ⦂∀ scopeBody S′ CI [ ‵ `ℕ ])
                (lift-term-comp p p′ U))
              (cong (λ L → L ⦂∀ scopeBody T′ CP [ ‵ `ℕ ])
                (lift-term-comp q q′ V))
              (NaturalUniversalValues.instantiate r (scope-trans p p′)
                (scope-trans q q′) (future-trans ext ext′) n<k) }) }
    }
