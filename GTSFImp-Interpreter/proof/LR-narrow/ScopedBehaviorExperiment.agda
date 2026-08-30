module proof.LR-narrow.ScopedBehaviorExperiment where

-- File Charter:
--   * Inhabits the scope-aware arrow and nominal-seal relations with the
--     earlier non-identity closures, including the escaped private seal.
--   * Proves behavior after arbitrary independent future allocations, not
--     only in the two initial result stores or at a chosen step index.
--   * Relates the allocating maker computations at every observation index.
--   * Accepts the original literal-wrapper counterexample at every index.

open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym) renaming (subst to subst≡; subst₂ to subst₂≡)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import Primitives using (κℕ)
open import Reduction
import Eval as E
open import Interpreter
open import proof.TypeInTermSubst using (toRename-wk-eq)
open import proof.LR-narrow.Application using
  (prepend-return; value-return-exact)
open import proof.LR-narrow.RevealSteps using (unseal-step-question)
open import proof.LR-narrow.FramePhases using (Frame)
open import proof.LR-narrow.RevealFrames using (revealFrame; reveal-frm)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.FunctionSealCompatibility using
  (related-seals; related-function-reveals-return)
open import LR-narrow.LogicalRelation using (same-natural)
open import LR-narrow.World using (core; impreciseStore; preciseStore)
import proof.LR-narrow.FunctionSealClosureExperiment as C
import proof.LR-narrow.FunctionSealObservationExperiment as O
import proof.LR-narrow.ScopeExperiment as First

-- These templates expose just the two runtime names that move under futures.

captured : ∀ {Δ} → TyVar Δ → ℕ → Term Δ
captured X n = ƛ (($ (κℕ n) ↓ seal X (‵ `ℕ)) ↑ unseal X (‵ `ℕ))

private-domain : ∀ {Δ} → TyVar Δ → TyVar Δ → ℕ → Term Δ
private-domain X Z n = captured X n ↑ (seal Z (‵ `ℕ) ↦↑ id↑ (‵ `ℕ))

captured-typed : ∀ {Δ} {Σ : TyStore Δ} {X A} n
  → Σ ∋ X ⦂ ‵ `ℕ → ⟨ Δ , Σ , [] ⟩ ⊢ captured X n ⦂ (A ⇒ ‵ `ℕ)
captured-typed n entry = ⊢ƛ (⊢reveal (⊢↑-unseal entry)
  (⊢conceal (⊢↓-seal entry) (⊢$ (κℕ n))))

private-domain-typed : ∀ {Δ} {Σ : TyStore Δ} {X Z} n
  → Σ ∋ X ⦂ ‵ `ℕ → Σ ∋ Z ⦂ ‵ `ℕ
  → ⟨ Δ , Σ , [] ⟩ ⊢ private-domain X Z n ⦂ (‵ `ℕ ⇒ ‵ `ℕ)
private-domain-typed n entryX entryZ =
  ⊢reveal (⊢↑-⇒ (⊢↓-seal entryZ) ⊢↑-id) (captured-typed n entryX)

captured-return : ∀ {Δ} (Σ : TyStore Δ) X n m
  → ∃ λ (trace : captured X n · $ (κℕ m)
      —↠[ keep ∷ keep ∷ [] ] $ (κℕ n)) →
    interpretFrom Σ 2 (captured X n · $ (κℕ m))
      ≡ returned (E.result Δ (keep ∷ keep ∷ []) ($ (κℕ n)) trace ($ (κℕ n)))
captured-return Σ X n m with unseal-step-question {Σ = Σ} X (‵ `ℕ) ($ (κℕ n))
captured-return Σ X n m | $ .(κℕ n) , step-eq =
  _ , prepend-return {Σ = Σ} {gas = 1} refl
    (prepend-return {Σ = Σ} {gas = 0} step-eq
      (value-return-exact {Σ = Σ} 0 ($ (κℕ n))))

private-domain-return : ∀ {Δ} (Σ : TyStore Δ) X Z n m
  → ∃ λ (trace : private-domain X Z n · $ (κℕ m)
      —↠[ keep ∷ keep ∷ keep ∷ keep ∷ [] ] $ (κℕ n)) →
    interpretFrom Σ 4 (private-domain X Z n · $ (κℕ m))
      ≡ returned (E.result Δ (keep ∷ keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ n)) trace ($ (κℕ n)))
private-domain-return Σ X Z n m
    with unseal-step-question {Σ = Σ} X (‵ `ℕ) ($ (κℕ n))
private-domain-return Σ X Z n m | $ .(κℕ n) , step-eq =
  _ , prepend-return {Σ = Σ} {gas = 3} refl
    (prepend-return {Σ = Σ} {gas = 2} refl
      (prepend-return {Σ = Σ} {gas = 1}
        (Frame.plug-step? revealFrame (reveal-frm (id↑ (‵ `ℕ)))
          {Σ = Σ} step-eq)
        (prepend-return {Σ = Σ} {gas = 0} refl
          (value-return-exact {Σ = Σ} 0 ($ (κℕ n))))))

captured-future : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    (p : ScopeFuture S T) X n
  → liftTerm p (captured X n) ≡ captured (liftVar p X) n
captured-future stay X n = refl
captured-future (grow p) X n rewrite toRename-wk-eq X =
  captured-future p (Fin.suc X) n

private-domain-future : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    (p : ScopeFuture S T) X Z n
  → liftTerm p (private-domain X Z n)
      ≡ private-domain (liftVar p X) (liftVar p Z) n
private-domain-future stay X Z n = refl
private-domain-future (grow p) X Z n
    rewrite toRename-wk-eq X | toRename-wk-eq Z =
  private-domain-future p (Fin.suc X) (Fin.suc Z) n

module B = Model C.initial C.initial

-- Every argument pair admitted by the natural domain consists of the same
-- natural, but n is independent of that argument. The returned function is
-- therefore not being certified by an identity-body shortcut.

closures-related : ∀ n k → B.related (B.arrow B.natural B.natural)
  root (allocate root (‵ `ℕ)) k (C.fresh-bare n) (C.fresh-private n)
closures-related n k = B.arrow-values
  (C.fresh-bare-value n) (C.fresh-private-value n)
  (C.fresh-bare-⊢ n) (C.fresh-private-⊢ n) call
  where
  call : ∀ {Δᴵ Δᴾ} {S : PhysicalScope C.initial Δᴵ}
      {T : PhysicalScope C.initial Δᴾ} {j U V}
    → (p : ScopeFuture root S) → (q : ScopeFuture (allocate root (‵ `ℕ)) T)
    → j Data.Nat.< k → B.related B.natural S T j U V
    → B.ObservedComputations B.natural S T j
        (liftTerm p (C.fresh-bare n) · U) (liftTerm q (C.fresh-private n) · V)
  call {S = S} {T} p q j<k (same-natural m)
      rewrite captured-future p (Fin.suc Fin.zero) n
        | private-domain-future q (Fin.suc (Fin.suc Fin.zero)) Fin.zero n
      with captured-return (scopeStore S) (liftVar p (Fin.suc Fin.zero)) n m
         | private-domain-return (scopeStore T)
             (liftVar q (Fin.suc (Fin.suc Fin.zero))) (liftVar q Fin.zero) n m
  call {S = S} {T} p q j<k (same-natural m)
      | traceᴵ , retᴵ | traceᴾ , retᴾ =
    B.observed-from-returns {S = S} {T = T} {gasᴵ = 2} {gasᴾ = 4}
      retᴵ retᴾ (same-natural n)

closures-future-related : ∀ {Δᴵ Δᴾ} {S : PhysicalScope C.initial Δᴵ}
    {T : PhysicalScope C.initial Δᴾ}
  → (p : ScopeFuture root S) → (q : ScopeFuture (allocate root (‵ `ℕ)) T)
  → ∀ n k → B.related (B.arrow B.natural B.natural) S T k
      (liftTerm p (C.fresh-bare n)) (liftTerm q (C.fresh-private n))
closures-future-related p q n k =
  B.future-closed (B.arrow B.natural B.natural) p q (closures-related n k)

body-results-related : ∀ n k
  → B.related (B.nominal (B.arrow B.natural B.natural)
      Fin.zero Fin.zero (Z∋ refl) (Z∋ refl))
      root (allocate root (‵ `ℕ)) k
      (C.fresh-bare n ↓ seal Fin.zero (‵ `ℕ ⇒ ‵ `ℕ))
      (C.fresh-private n ↓ seal (Fin.suc Fin.zero) (‵ `ℕ ⇒ ‵ `ℕ))
body-results-related n k = related-seals
  (C.fresh-bare-value n) (C.fresh-private-value n) (closures-related n k)

-- The payload relation supplied to the general function-seal theorem is
-- now the model's arrow relation, with its proved Kripke/index invariants.

decoded-body-results : ∀ n k → ∃[ U ] ∃[ V ]
    (C.public-bare · $ (κℕ n) —↠[ keep ∷ keep ∷ keep ∷ [] ] U)
    × (C.public-private · $ (κℕ n)
        —↠[ keep ∷ keep ∷ bind (‵ `ℕ) ∷ keep ∷ [] ] V)
    × B.related (B.arrow B.natural B.natural)
        root (allocate root (‵ `ℕ)) k U V
decoded-body-results n k = related-function-reveals-return
  (Fin.suc Fin.zero) (‵ `ℕ) Fin.zero (‵ `ℕ ⇒ ‵ `ℕ)
  (Fin.suc Fin.zero) (‵ `ℕ) Fin.zero (‵ `ℕ ⇒ ‵ `ℕ)
  C.make-bare-value ($ (κℕ n)) C.make-private-value ($ (κℕ n))
  (C.make-bare-↠ n) (C.make-private-↠ n)
  (B.related (B.arrow B.natural B.natural) root (allocate root (‵ `ℕ)) k)
  (body-results-related n k)

bare-closure-return : ∀ n
  → interpretFrom C.initial 3 (C.public-bare · $ (κℕ n))
      ≡ returned (E.result 2 (keep ∷ keep ∷ keep ∷ []) (C.fresh-bare n)
        (C.public-bare-↠ n) (C.fresh-bare-value n))
bare-closure-return n = refl

makers-observed : ∀ n k
  → B.ObservedComputations (B.arrow B.natural B.natural) root root k
      (C.public-bare · $ (κℕ n)) (C.public-private · $ (κℕ n))
makers-observed n k = B.observed-from-returns
  {S = root} {T = root} {gasᴵ = 3} {gasᴾ = 4}
  (bare-closure-return n) (O.private-closure-return n 0) (closures-related n k)

-- The original raw-store counterexample is now related without lowering
-- either result scope. This is a computation test, not a universal-type
-- compatibility theorem: the semantic result type is just natural.

module L = Model (impreciseStore (core First.initial))
                 (preciseStore (core First.initial))

literal-wrapper-observed : ∀ k
  → L.ObservedComputations L.natural root root k First.bare First.wrapped
literal-wrapper-observed k = L.observed-from-returns
  {S = root} {T = root} {gasᴵ = 2} {gasᴾ = 5}
  (First.bare-eval 0) (First.wrapped-eval 0) (same-natural 7)
