module proof.LR-narrow.VisibleEnvironmentExperiment where

-- File Charter:
--   * Extends a visible environment after an unmatched private allocation.
--   * Reuses non-identity escaping closures: their private seal stays hidden
--     from the visible-name map and usable after the fresh paired bind.
--   * Checks fresh nominal membership and arrow behavior at every index,
--     plus typed, executable calls after actual universal allocations.

open import Data.List using ([])
open import Data.Nat using (ℕ)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import Primitives using (κℕ)
open import Reduction
import Eval as E
open import Interpreter
import Consistency as Emb
open import proof.TypeInTermSubst using
  (typing-shiftᵗ-lift; renameᵗᵐ-preserves-Value)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopeRebase
open import proof.LR-narrow.VisibleEnvironment
open import proof.LR-narrow.FunctionSealCompatibility using (related-seals)
open import LR-narrow.LogicalRelation using (same-natural)
import proof.LR-narrow.FunctionSealClosureExperiment as C
import proof.LR-narrow.ScopedBehaviorExperiment as Prior

module Old = Model C.initial C.initial

-- Initially X represents naturals and Y represents functions on naturals.

initialEnvironment : VisibleEnvironment C.initial C.initial 2
initialEnvironment = record
  { impreciseNames = Emb.id↪ᵗ
  ; preciseNames = Emb.id↪ᵗ
  ; representation = λ
      { Fin.zero → Old.arrow Old.natural Old.natural
      ; (Fin.suc Fin.zero) → Old.natural }
  ; impreciseEntry = λ
      { Fin.zero → Z∋ refl
      ; (Fin.suc Fin.zero) → S-bind∋ (Z∋ refl) refl }
  ; preciseEntry = λ
      { Fin.zero → Z∋ refl
      ; (Fin.suc Fin.zero) → S-bind∋ (Z∋ refl) refl }
  }

module Private = Rebase {Σᴵ₀ = C.initial} {Σᴾ₀ = C.initial}
  root (allocate root (‵ `ℕ))

privateEnvironment : VisibleEnvironment C.initial C.physical 2
privateEnvironment =
  rerootEnvironment root (allocate root (‵ `ℕ)) initialEnvironment

module Fresh = Extend privateEnvironment
  (Private.rebase (Old.arrow Old.natural Old.natural))
module New = Fresh.R.New

-- The precise physical order is W, Z, Y, X; the visible order is W, Y, X.
-- The new pair W represents functions. Z remains private, not an alias.

private-stays-hidden : ∀ X
  → Emb.toRenameᵗ (preciseNames Fresh.extended) X ≢ Fin.suc Fin.zero
private-stays-hidden Fin.zero ()
private-stays-hidden (Fin.suc Fin.zero) ()
private-stays-hidden (Fin.suc (Fin.suc Fin.zero)) ()

old-natural-name :
  Emb.toRenameᵗ (preciseNames Fresh.extended) (Fin.suc (Fin.suc Fin.zero))
    ≡ Fin.suc (Fin.suc (Fin.suc Fin.zero))
old-natural-name = refl

escaped-closures-related : ∀ n k
  → New.related (Fresh.R.rebase
      (Private.rebase (Old.arrow Old.natural Old.natural))) root root k
      (⇑ᵗᵐ (C.fresh-bare n)) (⇑ᵗᵐ (C.fresh-private n))
escaped-closures-related n k =
  Prior.closures-future-related (grow stay) (grow stay) n k

-- The new visible name denotes the actual pair of freshly allocated slots.
-- Its payload is the old escaping closure, not a root-scoped replacement.

fresh-name-related : ∀ n k
  → New.related (meaning Fresh.extended Fin.zero) root root k
      (⇑ᵗᵐ (C.fresh-bare n) ↓ seal Fin.zero (‵ `ℕ ⇒ ‵ `ℕ))
      (⇑ᵗᵐ (C.fresh-private n) ↓ seal Fin.zero (‵ `ℕ ⇒ ‵ `ℕ))
fresh-name-related n k = related-seals (ƛ _) ((ƛ _) ↑ fun)
  (escaped-closures-related n k)

escaped-arrow-related : ∀ n k
  → New.related
      (New.arrow (Fresh.R.rebase (Private.rebase Old.natural))
                 (Fresh.R.rebase (Private.rebase Old.natural))) root root k
      (⇑ᵗᵐ (C.fresh-bare n)) (⇑ᵗᵐ (C.fresh-private n))
escaped-arrow-related n k =
  Fresh.R.arrow-to (Private.rebase Old.natural)
    (Private.rebase Old.natural)
    (Private.arrow-to Old.natural Old.natural (escaped-closures-related n k))

-- Actual allocations use a value-restricted universal whose body retains
-- the escaped closure. The instantiation type allocates the fresh W pair.

instantiate-again : ∀ {Δ} → Term Δ → Term Δ
instantiate-again F =
  (Λ (⇑ᵗᵐ F)) ⦂∀ (‵ `ℕ ⇒ ‵ `ℕ) [ ‵ `ℕ ⇒ ‵ `ℕ ]

instantiate-again-⊢ : ∀ {Δ} {Σ : TyStore Δ} {F}
  → Value F → ⟨ Δ , Σ , [] ⟩ ⊢ F ⦂ (‵ `ℕ ⇒ ‵ `ℕ)
  → ⟨ Δ , Σ , [] ⟩ ⊢ instantiate-again F ⦂ (‵ `ℕ ⇒ ‵ `ℕ)
instantiate-again-⊢ vF typed = ⊢• (⊢Λ
  (renameᵗᵐ-preserves-Value Emb.wk↪ᵗ vF) (typing-shiftᵗ-lift typed))

bare-call : ℕ → ℕ → Term 2
bare-call n m = instantiate-again (C.fresh-bare n) · $ (κℕ m)

private-call : ℕ → ℕ → Term 3
private-call n m = instantiate-again (C.fresh-private n) · $ (κℕ m)

bare-call-⊢ : ∀ n m → ⟨ 2 , C.initial , [] ⟩ ⊢ bare-call n m ⦂ ‵ `ℕ
bare-call-⊢ n m = ⊢·
  (instantiate-again-⊢ (C.fresh-bare-value n) (C.fresh-bare-⊢ n)) (⊢$ (κℕ m))

private-call-⊢ : ∀ n m → ⟨ 3 , C.physical , [] ⟩ ⊢ private-call n m ⦂ ‵ `ℕ
private-call-⊢ n m = ⊢·
  (instantiate-again-⊢ (C.fresh-private-value n) (C.fresh-private-⊢ n))
  (⊢$ (κℕ m))

bare-call-↠ : ∀ n m → bare-call n m
  —↠[ bind (‵ `ℕ ⇒ ‵ `ℕ) ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ]
  $ (κℕ n)
bare-call-↠ n m =
    bare-call n m
  —→[ bind (‵ `ℕ ⇒ ‵ `ℕ) ]⟨ ξ-·₁ (β-Λ (ƛ _)) refl ⟩
    (⇑ᵗᵐ (C.fresh-bare n) ↑ (id↓ (‵ `ℕ) ↦↑ id↑ (‵ `ℕ))) · $ (κℕ m)
  —→[ keep ]⟨ pure-step (β-reveal-⇒ (ƛ _) ($ (κℕ m))) ⟩
    (⇑ᵗᵐ (C.fresh-bare n) · ($ (κℕ m) ↓ id↓ (‵ `ℕ))) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ ξ-reveal
      (ξ-·₂ (ƛ _) (pure-step (id-conceal ($ (κℕ m)))) refl) refl ⟩
    (⇑ᵗᵐ (C.fresh-bare n) · $ (κℕ m)) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ ξ-reveal (pure-step (β ($ (κℕ m)))) refl ⟩
    (($ (κℕ n) ↓ seal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ))
      ↑ unseal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ)) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ ξ-reveal (pure-step (conceal-reveal ($ (κℕ n)))) refl ⟩
    $ (κℕ n) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ pure-step (id-reveal ($ (κℕ n))) ⟩
    $ (κℕ n) ∎[]

private-call-↠ : ∀ n m → private-call n m
  —↠[ bind (‵ `ℕ ⇒ ‵ `ℕ) ∷ keep ∷ keep ∷ keep ∷ keep
      ∷ keep ∷ keep ∷ keep ∷ [] ] $ (κℕ n)
private-call-↠ n m =
    private-call n m
  —→[ bind (‵ `ℕ ⇒ ‵ `ℕ) ]⟨ ξ-·₁ (β-Λ ((ƛ _) ↑ fun)) refl ⟩
    (⇑ᵗᵐ (C.fresh-private n) ↑ (id↓ (‵ `ℕ) ↦↑ id↑ (‵ `ℕ))) · $ (κℕ m)
  —→[ keep ]⟨ pure-step (β-reveal-⇒ ((ƛ _) ↑ fun) ($ (κℕ m))) ⟩
    (⇑ᵗᵐ (C.fresh-private n) · ($ (κℕ m) ↓ id↓ (‵ `ℕ))) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ ξ-reveal
      (ξ-·₂ ((ƛ _) ↑ fun) (pure-step (id-conceal ($ (κℕ m)))) refl) refl ⟩
    (⇑ᵗᵐ (C.fresh-private n) · $ (κℕ m)) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ ξ-reveal (pure-step (β-reveal-⇒ (ƛ _) ($ (κℕ m)))) refl ⟩
    ((Prior.captured (Fin.suc (Fin.suc (Fin.suc Fin.zero))) n
      · ($ (κℕ m) ↓ seal (Fin.suc Fin.zero) (‵ `ℕ))) ↑ id↑ (‵ `ℕ))
      ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ ξ-reveal
      (ξ-reveal (pure-step (β ($ (κℕ m) ↓ seal))) refl) refl ⟩
    ((($ (κℕ n) ↓ seal (Fin.suc (Fin.suc (Fin.suc Fin.zero))) (‵ `ℕ))
      ↑ unseal (Fin.suc (Fin.suc (Fin.suc Fin.zero))) (‵ `ℕ))
      ↑ id↑ (‵ `ℕ)) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ ξ-reveal
      (ξ-reveal (pure-step (conceal-reveal ($ (κℕ n)))) refl) refl ⟩
    ($ (κℕ n) ↑ id↑ (‵ `ℕ)) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ ξ-reveal (pure-step (id-reveal ($ (κℕ n)))) refl ⟩
    $ (κℕ n) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ pure-step (id-reveal ($ (κℕ n))) ⟩
    $ (κℕ n) ∎[]

bare-call-return : ∀ n m
  → interpretFrom C.initial 6 (bare-call n m)
      ≡ returned (E.result 3
        (bind (‵ `ℕ ⇒ ‵ `ℕ) ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ n)) (bare-call-↠ n m) ($ (κℕ n)))
bare-call-return n m = refl

private-call-return : ∀ n m
  → interpretFrom C.physical 8 (private-call n m)
      ≡ returned (E.result 4
        (bind (‵ `ℕ ⇒ ‵ `ℕ) ∷ keep ∷ keep ∷ keep ∷ keep
          ∷ keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ n)) (private-call-↠ n m) ($ (κℕ n)))
private-call-return n m = refl

-- Rebase transfers computation observations as well as value membership.
-- In particular these new allocations reach exactly Fresh.extended's roots.

calls-observed : ∀ n m k
  → Private.New.ObservedComputations (Private.rebase Old.natural)
      root root k (bare-call n m) (private-call n m)
calls-observed n m k =
  Private.observed-to Old.natural
    (Old.observed-from-returns {gasᴵ = 6} {gasᴾ = 8}
      (bare-call-return n m) (private-call-return n m) (same-natural n))
