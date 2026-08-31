module proof.LR-narrow.IntegratedLocal where

-- File Charter:
--   * Scope-anchored semantic meanings over the ORIGINAL integrated worlds.
--   * Endpoints are local types; explicit future paths retain their names.
--   * Observations retain all three directions and independent actual runs.
--   * Semantic records are infrastructure, not admissible payload codes:
--     the separate code interpretation controls which meanings may be used.
--   * No live LR, CTI, or operational rule is changed.

open import Data.List using ([])
open import Data.Nat using (ℕ; _≤_; _<_; _∸_)
open import Data.Nat.Properties using (≤-trans; ∸-monoˡ-≤; m∸n≤m)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong) renaming (subst to subst≡; subst₂ to subst₂≡)

open import Types
open import TyStore
open import TermCtx using (Z)
open import CastTerms
open import Primitives using (κℕ; κ𝔹)
open import Interpreter
import Eval as E
open import LR-narrow.Computation using (BlamesFrom)
open import LR-narrow.LogicalRelation
  using (SameBaseValue; same-natural; same-boolean)
open import proof.LR-narrow.Application
  using (eval-from-return; eval-from-blame; value-return-exact)
open import proof.LR-narrow.TargetEvaluation
  using (return-result-unique; eval-terminal-unique)
open import proof.LR-narrow.ScopedIdentity using (identity-return; lift-identity)
open import proof.LR-narrow.PhysicalScope
import proof.LR-narrow.IntegratedWorld as IW

module Local {ΔI0 ΔP0} (ΣI0 : TyStore ΔI0) (ΣP0 : TyStore ΔP0) where

  module Worlds = IW.Worlds ΣI0 ΣP0
  open Worlds

  record Meaning {ΔA ΔB} (S₀ : PhysicalScope ΣI0 ΔA)
      (T₀ : PhysicalScope ΣP0 ΔB) (AI : Ty ΔA) (AP : Ty ΔB) : Set₁ where
    field
      related : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP}
        → ScopeFuture S₀ S → ScopeFuture T₀ T
        → World S T → ℕ → Term ΔI → Term ΔP → Set
      imprecise-value : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP} {p : ScopeFuture S₀ S}
          {q : ScopeFuture T₀ T} {W : World S T} {k U V}
        → related p q W k U V → Value U
      precise-value : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP} {p : ScopeFuture S₀ S}
          {q : ScopeFuture T₀ T} {W : World S T} {k U V}
        → related p q W k U V → Value V
      imprecise-typed : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP} {p : ScopeFuture S₀ S}
          {q : ScopeFuture T₀ T} {W : World S T} {k U V}
        → related p q W k U V
        → ⟨ ΔI , scopeStore S , [] ⟩ ⊢ U ⦂ liftTy p AI
      precise-typed : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP} {p : ScopeFuture S₀ S}
          {q : ScopeFuture T₀ T} {W : World S T} {k U V}
        → related p q W k U V
        → ⟨ ΔP , scopeStore T , [] ⟩ ⊢ V ⦂ liftTy q AP
      downward : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP} {p : ScopeFuture S₀ S}
          {q : ScopeFuture T₀ T} {W : World S T} {j k U V}
        → j ≤ k → related p q W k U V → related p q W j U V
      future-closed : ∀ {ΔI ΔP ΔI′ ΔP′}
          {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
          {S′ : PhysicalScope ΣI0 ΔI′} {T′ : PhysicalScope ΣP0 ΔP′}
          {p : ScopeFuture S₀ S} {q : ScopeFuture T₀ T}
          {W : World S T} {W′ : World S′ T′} {k U V}
        → (r : ScopeFuture S S′) → (s : ScopeFuture T T′)
        → Future r s W W′ → related p q W k U V
        → related (scope-trans p r) (scope-trans q s) W′ k
            (liftTerm r U) (liftTerm s V)

  open Meaning public

  record Observed {ΔA ΔB} {S₀ : PhysicalScope ΣI0 ΔA}
      {T₀ : PhysicalScope ΣP0 ΔB} {AI AP} (A : Meaning S₀ T₀ AI AP)
      {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      (p : ScopeFuture S₀ S) (q : ScopeFuture T₀ T)
      (W : World S T) (k : ℕ) (M : Term ΔI) (N : Term ΔP) : Set where
    field
      forward-return : ∀ {n} {outI : E.EvalResult M}
        → n < k → interpretFrom (scopeStore S) n M ≡ returned outI
        → (∃[ m ] ∃[ outP ]
            (interpretFrom (scopeStore T) m N ≡ returned outP)
            × ∃[ W′ ]
              Future (advance-future S (E.changes outI))
                (advance-future T (E.changes outP)) W W′
              × related A
                  (scope-trans p (advance-future S (E.changes outI)))
                  (scope-trans q (advance-future T (E.changes outP)))
                  W′ (k ∸ n) (E.term outI) (E.term outP))
          ⊎ (∃[ m ] BlamesFrom (scopeStore T) m N)
      backward-return : ∀ {n} {outP : E.EvalResult N}
        → n < k → interpretFrom (scopeStore T) n N ≡ returned outP
        → ∃[ m ] ∃[ outI ]
            (interpretFrom (scopeStore S) m M ≡ returned outI)
            × ∃[ W′ ]
              Future (advance-future S (E.changes outI))
                (advance-future T (E.changes outP)) W W′
              × related A
                  (scope-trans p (advance-future S (E.changes outI)))
                  (scope-trans q (advance-future T (E.changes outP)))
                  W′ (k ∸ n) (E.term outI) (E.term outP)
      forward-blame : ∀ {n}
        → n < k → BlamesFrom (scopeStore S) n M
        → ∃[ m ] BlamesFrom (scopeStore T) m N

  observed-downward : ∀ {ΔA ΔB} {S₀ : PhysicalScope ΣI0 ΔA}
      {T₀ : PhysicalScope ΣP0 ΔB} {AI AP} {A : Meaning S₀ T₀ AI AP}
      {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {p : ScopeFuture S₀ S} {q : ScopeFuture T₀ T}
      {W : World S T} {j k M N}
    → j ≤ k → Observed A p q W k M N → Observed A p q W j M N
  observed-downward {A = A} j≤k obs = record
    { forward-return = λ { {n} n<j ret →
        case Observed.forward-return obs (≤-trans n<j j≤k) ret of λ
          { (inj₁ (m , out , ret , W′ , ext , rel)) →
              inj₁ (m , out , ret , W′ , ext ,
                downward A (∸-monoˡ-≤ n j≤k) rel)
          ; (inj₂ bl) → inj₂ bl } }
    ; backward-return = λ { {n} n<j ret →
        case Observed.backward-return obs (≤-trans n<j j≤k) ret of λ
          { (m , out , ret , W′ , ext , rel) →
              m , out , ret , W′ , ext ,
                downward A (∸-monoˡ-≤ n j≤k) rel } }
    ; forward-blame = λ n<j →
        Observed.forward-blame obs (≤-trans n<j j≤k)
    }

  base : ∀ {ΔA ΔB} {S₀ : PhysicalScope ΣI0 ΔA}
      {T₀ : PhysicalScope ΣP0 ΔB} (ι : Base)
    → Meaning S₀ T₀ (‵ ι) (‵ ι)
  base ι = record
    { related = λ p q W k → SameBaseValue ι
    ; imprecise-value = λ
        { (same-natural n) → $ (κℕ n) ; (same-boolean b) → $ (κ𝔹 b) }
    ; precise-value = λ
        { (same-natural n) → $ (κℕ n) ; (same-boolean b) → $ (κ𝔹 b) }
    ; imprecise-typed = λ
        { {p = p} (same-natural n) →
            subst≡ (λ C → ⟨ _ , _ , [] ⟩ ⊢ $ (κℕ n) ⦂ C)
              (sym (lift-ty-base p `ℕ)) (⊢$ (κℕ n))
        ; {p = p} (same-boolean b) →
            subst≡ (λ C → ⟨ _ , _ , [] ⟩ ⊢ $ (κ𝔹 b) ⦂ C)
              (sym (lift-ty-base p `𝔹)) (⊢$ (κ𝔹 b)) }
    ; precise-typed = λ
        { {q = q} (same-natural n) →
            subst≡ (λ C → ⟨ _ , _ , [] ⟩ ⊢ $ (κℕ n) ⦂ C)
              (sym (lift-ty-base q `ℕ)) (⊢$ (κℕ n))
        ; {q = q} (same-boolean b) →
            subst≡ (λ C → ⟨ _ , _ , [] ⟩ ⊢ $ (κ𝔹 b) ⦂ C)
              (sym (lift-ty-base q `𝔹)) (⊢$ (κ𝔹 b)) }
    ; downward = λ j≤k rel → rel
    ; future-closed = λ
        { r s ext (same-natural n) → subst₂≡ (SameBaseValue `ℕ)
            (sym (lift-constant r (κℕ n)))
            (sym (lift-constant s (κℕ n))) (same-natural n)
        ; r s ext (same-boolean b) → subst₂≡ (SameBaseValue `𝔹)
            (sym (lift-constant r (κ𝔹 b)))
            (sym (lift-constant s (κ𝔹 b))) (same-boolean b) }
    }

  observed-from-returns : ∀ {ΔA ΔB} {S₀ : PhysicalScope ΣI0 ΔA}
      {T₀ : PhysicalScope ΣP0 ΔB} {AI AP} {A : Meaning S₀ T₀ AI AP}
      {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {p : ScopeFuture S₀ S} {q : ScopeFuture T₀ T}
      {W : World S T} {k M N gasI gasP}
      {outI : E.EvalResult M} {outP : E.EvalResult N}
      {W′ : World (advance S (E.changes outI))
                  (advance T (E.changes outP))}
    → interpretFrom (scopeStore S) gasI M ≡ returned outI
    → interpretFrom (scopeStore T) gasP N ≡ returned outP
    → Future (advance-future S (E.changes outI))
        (advance-future T (E.changes outP)) W W′
    → related A (scope-trans p (advance-future S (E.changes outI)))
        (scope-trans q (advance-future T (E.changes outP)))
        W′ k (E.term outI) (E.term outP)
    → Observed A p q W k M N
  observed-from-returns {A = A} {S = S} {T} {p} {q} {W} {k} {M} {N}
      {gasI} {gasP} {outI} {outP} {W′} retI retP ext rel = record
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
            × related A (scope-trans p (advance-future S (E.changes out)))
                (scope-trans q (advance-future T (E.changes out′)))
                W″ (k ∸ n) (E.term out) (E.term out′))
        ⊎ (∃[ m ] BlamesFrom (scopeStore T) m N)
    forward {n} n<k ret with return-result-unique {Σ = scopeStore S}
      {leftGas = n} {rightGas = gasI} ret retI
    forward {n} n<k ret | refl =
      inj₁ (gasP , outP , retP , W′ , ext , downward A (m∸n≤m k n) rel)

    backward : ∀ {n} {out : E.EvalResult N}
      → n < k → interpretFrom (scopeStore T) n N ≡ returned out
      → ∃[ m ] ∃[ out′ ]
          (interpretFrom (scopeStore S) m M ≡ returned out′)
          × ∃[ W″ ] Future (advance-future S (E.changes out′))
              (advance-future T (E.changes out)) W W″
            × related A (scope-trans p (advance-future S (E.changes out′)))
                (scope-trans q (advance-future T (E.changes out)))
                W″ (k ∸ n) (E.term out′) (E.term out)
    backward {n} n<k ret with return-result-unique {Σ = scopeStore T}
      {leftGas = n} {rightGas = gasP} ret retP
    backward {n} n<k ret | refl =
      gasI , outI , retI , W′ , ext , downward A (m∸n≤m k n) rel

    no-blame : ∀ {n} → n < k → BlamesFrom (scopeStore S) n M
      → ∃[ m ] BlamesFrom (scopeStore T) m N
    no-blame {n} n<k (Δ′ , χ , tr , bl)
        with eval-terminal-unique {Σ = scopeStore S}
          {leftGas = gasI} {rightGas = n}
          (eval-from-return {Σ = scopeStore S} {gas = gasI} retI)
          (eval-from-blame {Σ = scopeStore S} {gas = n} bl)
    no-blame n<k (Δ′ , χ , tr , bl) | ()

  observed-from-right-blame : ∀ {ΔA ΔB}
      {S₀ : PhysicalScope ΣI0 ΔA} {T₀ : PhysicalScope ΣP0 ΔB}
      {AI AP} {A : Meaning S₀ T₀ AI AP} {ΔI ΔP}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {p : ScopeFuture S₀ S} {q : ScopeFuture T₀ T}
      {W : World S T} {k M N gas}
    → BlamesFrom (scopeStore T) gas N → Observed A p q W k M N
  observed-from-right-blame {A = A} {S = S} {T} {p} {q} {W} {k} {M} {N}
      {gas} blameN@(Δ′ , χ , tr , bl) = record
    { forward-return = λ n<k ret → inj₂ (gas , blameN)
    ; backward-return = no-return
    ; forward-blame = λ n<k b → gas , blameN
    }
    where
    no-return : ∀ {n} {out : E.EvalResult N}
      → n < k → interpretFrom (scopeStore T) n N ≡ returned out
      → ∃[ m ] ∃[ out′ ]
          (interpretFrom (scopeStore S) m M ≡ returned out′)
          × ∃[ W″ ] Future (advance-future S (E.changes out′))
              (advance-future T (E.changes out)) W W″
            × related A (scope-trans p (advance-future S (E.changes out′)))
                (scope-trans q (advance-future T (E.changes out)))
                W″ (k ∸ n) (E.term out′) (E.term out)
    no-return {n} n<k ret with eval-terminal-unique {Σ = scopeStore T}
      {leftGas = n} {rightGas = gas}
      (eval-from-return {Σ = scopeStore T} {gas = n} ret)
      (eval-from-blame {Σ = scopeStore T} {gas = gas} bl)
    no-return n<k ret | ()

  values-observed : ∀ {ΔA ΔB} {S₀ : PhysicalScope ΣI0 ΔA}
      {T₀ : PhysicalScope ΣP0 ΔB} {AI AP} (A : Meaning S₀ T₀ AI AP)
      {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {p : ScopeFuture S₀ S} {q : ScopeFuture T₀ T}
      {W : World S T} {k U V}
    → related A p q W k U V → Observed A p q W k U V
  values-observed A {S = S} {T} {p} {q} rel = observed-from-returns
    {gasI = 0} {gasP = 0}
    (value-return-exact {Σ = scopeStore S} 0 (imprecise-value A rel))
    (value-return-exact {Σ = scopeStore T} 0 (precise-value A rel))
    future-refl
    (subst₂≡ (λ r s → related A r s _ _ _ _)
      (sym (scope-trans-right-id p)) (sym (scope-trans-right-id q)) rel)
