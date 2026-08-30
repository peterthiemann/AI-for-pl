module proof.LR-narrow.ScopedRightSealClosureExperiment where

-- File Charter:
--   * Seals only the precise member of an escaping, non-identity closure pair.
--   * Retains the private precise name and adds a fresh right-only function
--     slot; the imprecise closure and its physical root are unchanged.
--   * Checks seal/unseal observations at every independent physical future,
--     plus typed data-ending calls with exact interpreter equations.

open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import Primitives using (κℕ)
open import Reduction
import Eval as E
open import Interpreter
open import proof.TypeInTermSubst using (typing-shiftᵗ-bind)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopeRebase
open import proof.LR-narrow.ScopedRightNominal
open import LR-narrow.LogicalRelation using (same-natural)
import proof.LR-narrow.FunctionSealClosureExperiment as C
import proof.LR-narrow.ScopedBehaviorExperiment as Prior
import proof.LR-narrow.ScopedConversionCompatibility as CC
import proof.LR-narrow.ScopedRightSealCompatibility as RS

precise-root : TyStore 4
precise-root = store-bind C.physical (‵ `ℕ ⇒ ‵ `ℕ)

module Old = Model C.initial C.initial
module R = Rebase {Σᴵ₀ = C.initial} {Σᴾ₀ = C.initial}
  root (allocate (allocate root (‵ `ℕ)) (‵ `ℕ ⇒ ‵ `ℕ))
module New = Model C.initial precise-root
module Right = Nominals C.initial precise-root
module Values = CC.Compatibility C.initial precise-root
module K = RS.Compatibility C.initial precise-root

-- Only the precise closure is shifted for the new function slot. Its
-- earlier private natural slot remains in the closure's domain conversion.

escaped-related : ∀ n k
  → New.related (R.rebase (Old.arrow Old.natural Old.natural)) root root k
      (C.fresh-bare n) (⇑ᵗᵐ (C.fresh-private n))
escaped-related n k = Prior.closures-future-related stay (grow stay) n k

right-sealed-related : ∀ n k
  → New.related (Right.right-nominal
      (R.rebase (Old.arrow Old.natural Old.natural)) Fin.zero (Z∋ refl))
      root root k (C.fresh-bare n)
      (⇑ᵗᵐ (C.fresh-private n) ↓ seal Fin.zero (‵ `ℕ ⇒ ‵ `ℕ))
right-sealed-related n k =
  related-right-seal ((ƛ _) ↑ fun) (escaped-related n k)

-- This is an arrow observation, not just agreement on the concrete call
-- below: the payload relation quantifies over all related future arguments.

right-roundtrip-observed : ∀ {Δᴵ Δᴾ}
    {S : PhysicalScope C.initial Δᴵ} {T : PhysicalScope precise-root Δᴾ}
    (p : ScopeFuture root S) (q : ScopeFuture root T) n k
  → New.ObservedComputations (R.rebase (Old.arrow Old.natural Old.natural))
      S T k (liftTerm p (C.fresh-bare n))
      ((liftTerm q (⇑ᵗᵐ (C.fresh-private n))
          ↓ seal (scopeVar T Fin.zero) (scopeTy T (‵ `ℕ ⇒ ‵ `ℕ)))
        ↑ unseal (scopeVar T Fin.zero) (scopeTy T (‵ `ℕ ⇒ ‵ `ℕ)))
right-roundtrip-observed p q n k =
  K.observed-right-unseal (R.rebase (Old.arrow Old.natural Old.natural))
    Fin.zero (Z∋ refl)
    (K.observed-right-seal (R.rebase (Old.arrow Old.natural Old.natural))
      Fin.zero (Z∋ refl)
      (Values.values-observed (R.rebase (Old.arrow Old.natural Old.natural))
        (New.future-closed (R.rebase (Old.arrow Old.natural Old.natural))
          p q (escaped-related n k))))

right-closure-roundtrip : ℕ → Term 4
right-closure-roundtrip n =
  (⇑ᵗᵐ (C.fresh-private n) ↓ seal Fin.zero (‵ `ℕ ⇒ ‵ `ℕ))
    ↑ unseal Fin.zero (‵ `ℕ ⇒ ‵ `ℕ)

right-closure-roundtrip-⊢ : ∀ n → ⟨ 4 , precise-root , [] ⟩
  ⊢ right-closure-roundtrip n ⦂ (‵ `ℕ ⇒ ‵ `ℕ)
right-closure-roundtrip-⊢ n =
  ⊢reveal (⊢↑-unseal (Z∋ refl)) (⊢conceal (⊢↓-seal (Z∋ refl))
    (typing-shiftᵗ-bind (C.fresh-private-⊢ n)))

right-closure-call : ℕ → ℕ → Term 4
right-closure-call n m = right-closure-roundtrip n · $ (κℕ m)

right-closure-call-⊢ : ∀ n m
  → ⟨ 4 , precise-root , [] ⟩ ⊢ right-closure-call n m ⦂ ‵ `ℕ
right-closure-call-⊢ n m = ⊢· (right-closure-roundtrip-⊢ n) (⊢$ (κℕ m))

right-closure-call-↠ : ∀ n m → right-closure-call n m
  —↠[ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ] $ (κℕ n)
right-closure-call-↠ n m =
    right-closure-call n m
  —→[ keep ]⟨ ξ-·₁ (pure-step (conceal-reveal ((ƛ _) ↑ fun))) refl ⟩
    ⇑ᵗᵐ (C.fresh-private n) · $ (κℕ m)
  —→[ keep ]⟨ pure-step (β-reveal-⇒ (ƛ _) ($ (κℕ m))) ⟩
    (Prior.captured (Fin.suc (Fin.suc (Fin.suc Fin.zero))) n
      · ($ (κℕ m) ↓ seal (Fin.suc Fin.zero) (‵ `ℕ))) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ ξ-reveal (pure-step (β ($ (κℕ m) ↓ seal))) refl ⟩
    (($ (κℕ n) ↓ seal (Fin.suc (Fin.suc (Fin.suc Fin.zero))) (‵ `ℕ))
      ↑ unseal (Fin.suc (Fin.suc (Fin.suc Fin.zero))) (‵ `ℕ)) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ ξ-reveal (pure-step (conceal-reveal ($ (κℕ n)))) refl ⟩
    $ (κℕ n) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ pure-step (id-reveal ($ (κℕ n))) ⟩
    $ (κℕ n) ∎[]

right-closure-call-eval : ∀ n m
  → interpretFrom precise-root 5 (right-closure-call n m)
      ≡ returned (E.result 4 (keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [])
          ($ (κℕ n)) (right-closure-call-↠ n m) ($ (κℕ n)))
right-closure-call-eval n m = refl

right-closure-call-observed : ∀ n m k
  → New.ObservedComputations (R.rebase Old.natural) root root k
      (C.fresh-bare n · $ (κℕ m)) (right-closure-call n m)
right-closure-call-observed n m k
    with Prior.captured-return C.initial (Fin.suc Fin.zero) n m
right-closure-call-observed n m k | trace , ret =
  R.observed-to Old.natural
    (Old.observed-from-returns {gasᴵ = 2} {gasᴾ = 5}
      ret (right-closure-call-eval n m) (same-natural n))
