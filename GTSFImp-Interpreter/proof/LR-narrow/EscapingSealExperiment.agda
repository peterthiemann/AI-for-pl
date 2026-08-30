module proof.LR-narrow.EscapingSealExperiment where

-- File Charter:
--   * Tests the absent universal wrapper on polymorphic identity.
--   * Checks its returned function, escaping private seal, and data use.
--   * Refutes lowering that function through a lookup-preserving embedding
--     of the chosen paired scope. No live LR or reduction rule is changed.

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (_×_; _,_; ∃-syntax)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans)

open import Types
open import TyStore
open import TermCtx using (Z)
open import Primitives using (κℕ)
open import CastTerms
open import Conversion
open import Reduction
import Consistency as C
open import Consistency using (_↪ᵗ_; toRenameᵗ; wk↪ᵗ)
import Eval as E
open import Interpreter
open import LR-narrow.World
open import proof.TypeInTermSubst using (StoreRename)
import proof.LR-narrow.ScopeExperiment as First

bare-id : Term 1
bare-id = (Λ (ƛ (` 0)))
  ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ＇ Fin.zero ]

wrapped-id : Term 1
wrapped-id = ((Λ (ƛ (` 0)))
  ↑ 〖 Fin.zero , ‵ `ℕ ↑ `∀ (＇ Fin.zero ⇒ ＇ Fin.zero) 〗)
  ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ＇ Fin.zero ]

bare-id-⊢ : ⟨ 1 , preciseStore (core First.initial) , [] ⟩
  ⊢ bare-id ⦂ (＇ Fin.zero ⇒ ＇ Fin.zero)
bare-id-⊢ = ⊢• (⊢Λ (ƛ (` 0)) (⊢ƛ (⊢` Z)))

wrapped-id-⊢ : ⟨ 1 , preciseStore (core First.initial) , [] ⟩
  ⊢ wrapped-id ⦂ (＇ Fin.zero ⇒ ＇ Fin.zero)
wrapped-id-⊢ = ⊢• (⊢reveal (⊢↑-∀ (⊢↑-⇒ ⊢↓-id ⊢↑-id))
  (⊢Λ (ƛ (` 0)) (⊢ƛ (⊢` Z))))

bare-function : Term 2
bare-function = (ƛ (` 0))
  ↑ (seal Fin.zero (＇ (Fin.suc Fin.zero))
      ↦↑ unseal Fin.zero (＇ (Fin.suc Fin.zero)))

wrapped-function : Term 3
wrapped-function = ((ƛ (` 0))
  ↑ (seal Fin.zero (＇ (Fin.suc Fin.zero))
      ↦↑ unseal Fin.zero (＇ (Fin.suc Fin.zero))))
  ↑ (id↓ (＇ (Fin.suc Fin.zero)) ↦↑ id↑ (＇ (Fin.suc Fin.zero)))
  ↑ (seal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero)))
      ↦↑ unseal (Fin.suc Fin.zero) (＇ (Fin.suc (Fin.suc Fin.zero))))

bare-id-↠ : bare-id —↠[ bind (＇ Fin.zero) ∷ [] ] bare-function
bare-id-↠ =
    (Λ (ƛ (` 0))) ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ＇ Fin.zero ]
  —→[ bind (＇ Fin.zero) ]⟨ β-Λ (ƛ (` 0)) ⟩
    bare-function ∎[]

wrapped-id-↠ : wrapped-id
  —↠[ bind (＇ Fin.zero) ∷ bind (＇ Fin.zero) ∷ [] ] wrapped-function
wrapped-id-↠ =
    ((Λ (ƛ (` 0))) ↑ `∀↑ (id↓ (＇ Fin.zero) ↦↑ id↑ (＇ Fin.zero)))
      ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ＇ Fin.zero ]
  —→[ bind (＇ Fin.zero) ]⟨ β-reveal-∀ (Λ (ƛ (` 0))) ⟩
    (((Λ (ƛ (` 0))) ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ＇ Fin.zero ])
      ↑ (id↓ (＇ Fin.zero) ↦↑ id↑ (＇ Fin.zero)))
      ↑ (seal Fin.zero (＇ (Fin.suc Fin.zero))
          ↦↑ unseal Fin.zero (＇ (Fin.suc Fin.zero)))
  —→[ bind (＇ Fin.zero) ]⟨
      ξ-reveal (ξ-reveal (β-Λ (ƛ (` 0))) refl) refl ⟩
    wrapped-function ∎[]

bare-id-result : E.EvalResult bare-id
bare-id-result = E.result 2 (bind (＇ Fin.zero) ∷ [])
  bare-function bare-id-↠ ((ƛ (` 0)) ↑ fun)

wrapped-id-result : E.EvalResult wrapped-id
wrapped-id-result = E.result 3
  (bind (＇ Fin.zero) ∷ bind (＇ Fin.zero) ∷ [])
  wrapped-function wrapped-id-↠ ((((ƛ (` 0)) ↑ fun) ↑ fun) ↑ fun)

bare-id-eval : ∀ gas
  → interpretFrom (impreciseStore (core First.initial)) (suc gas) bare-id
      ≡ returned bare-id-result
bare-id-eval zero = refl
bare-id-eval (suc gas) = refl

wrapped-id-eval : ∀ gas
  → interpretFrom (preciseStore (core First.initial)) (suc (suc gas))
      wrapped-id ≡ returned wrapped-id-result
wrapped-id-eval zero = refl
wrapped-id-eval (suc gas) = refl

bare-function-⊢ : ⟨ 2 , preciseStore (core First.paired) , [] ⟩
  ⊢ bare-function ⦂ (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero))
bare-function-⊢ = ⊢reveal
  (⊢↑-⇒ (⊢↓-seal (Z∋ refl)) (⊢↑-unseal (Z∋ refl))) (⊢ƛ (⊢` Z))

wrapped-function-⊢ :
  ⟨ 3 , store-bind (preciseStore (core First.paired)) (＇ Fin.zero) , [] ⟩
  ⊢ wrapped-function
    ⦂ (＇ (Fin.suc (Fin.suc Fin.zero)) ⇒ ＇ (Fin.suc (Fin.suc Fin.zero)))
wrapped-function-⊢ = ⊢reveal
  (⊢↑-⇒ (⊢↓-seal (S-bind∋ (Z∋ refl) refl))
    (⊢↑-unseal (S-bind∋ (Z∋ refl) refl)))
  (⊢reveal (⊢↑-⇒ ⊢↓-id ⊢↑-id)
    (⊢reveal (⊢↑-⇒ (⊢↓-seal (Z∋ refl)) (⊢↑-unseal (Z∋ refl)))
      (⊢ƛ (⊢` Z))))

-- Both closures can be used safely. The old X seal on the argument and
-- the matching unseal on the result make the endpoint a natural, not a
-- function. These interpreter witnesses retain the private runtime store.

bare-use : Term 2
bare-use = (bare-function · ($ (κℕ 7)
  ↓ seal (Fin.suc Fin.zero) (‵ `ℕ)))
  ↑ unseal (Fin.suc Fin.zero) (‵ `ℕ)

wrapped-use : Term 3
wrapped-use = (wrapped-function · ($ (κℕ 7)
  ↓ seal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ)))
  ↑ unseal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ)

bare-use-⊢ : ⟨ 2 , preciseStore (core First.paired) , [] ⟩
  ⊢ bare-use ⦂ ‵ `ℕ
bare-use-⊢ = ⊢reveal (⊢↑-unseal (S-bind∋ (Z∋ refl) refl))
  (⊢· bare-function-⊢
    (⊢conceal (⊢↓-seal (S-bind∋ (Z∋ refl) refl)) (⊢$ (κℕ 7))))

wrapped-use-⊢ :
  ⟨ 3 , store-bind (preciseStore (core First.paired)) (＇ Fin.zero) , [] ⟩
  ⊢ wrapped-use ⦂ ‵ `ℕ
wrapped-use-⊢ = ⊢reveal
  (⊢↑-unseal (S-bind∋ (S-bind∋ (Z∋ refl) refl) refl))
  (⊢· wrapped-function-⊢
    (⊢conceal (⊢↓-seal (S-bind∋ (S-bind∋ (Z∋ refl) refl) refl))
      (⊢$ (κℕ 7))))

bare-use-eval : ∃[ outcome ]
  (interpretFrom (preciseStore (core First.paired)) 20 bare-use
    ≡ returned outcome) × (E.term outcome ≡ $ (κℕ 7))
bare-use-eval = _ , refl , refl

wrapped-use-eval : ∃[ outcome ]
  (interpretFrom
    (store-bind (preciseStore (core First.paired)) (＇ Fin.zero))
    20 wrapped-use ≡ returned outcome) × (E.term outcome ≡ $ (κℕ 7))
wrapped-use-eval = _ , refl , refl

private
  -- A syntax probe for a seal in the domain of the n-th reveal wrapper.
  -- It is equivariant under every embedding, so a zero answer cannot be
  -- produced by weakening. Other syntax is deliberately not inspected.
  domain-seal : ∀ {Δ A B} → Conv↑ Δ A B → Maybe (TyVar Δ)
  domain-seal (unseal X R) = nothing
  domain-seal (seal X R ↦↑ d) = just X
  domain-seal ((c ↦↓ d) ↦↑ e) = nothing
  domain-seal (`∀↓ c ↦↑ d) = nothing
  domain-seal (id↓ A ↦↑ d) = nothing
  domain-seal (`∀↑ c) = nothing
  domain-seal (id↑ A) = nothing

  seal-at : ∀ {Δ} → ℕ → Term Δ → Maybe (TyVar Δ)
  seal-at n (` x) = nothing
  seal-at n (ƛ M) = nothing
  seal-at n (L · M) = nothing
  seal-at n (Λ M) = nothing
  seal-at n (M ⦂∀ B [ A ]) = nothing
  seal-at n ($ κ) = nothing
  seal-at n (L ⊕[ op ] M) = nothing
  seal-at n (M ⟨ c ⟩) = nothing
  seal-at zero (M ↑ c) = domain-seal c
  seal-at (suc n) (M ↑ c) = seal-at n M
  seal-at n (M ↓ c) = nothing
  seal-at n blame = nothing

  domain-seal-rename : ∀ {Δ Δ′ A B} (ρ : Δ ↪ᵗ Δ′) (c : Conv↑ Δ A B)
    → domain-seal (rename↑ (toRenameᵗ ρ) c)
        ≡ map (toRenameᵗ ρ) (domain-seal c)
  domain-seal-rename ρ (unseal X R) = refl
  domain-seal-rename ρ (seal X R ↦↑ d) = refl
  domain-seal-rename ρ ((c ↦↓ d) ↦↑ e) = refl
  domain-seal-rename ρ (`∀↓ c ↦↑ d) = refl
  domain-seal-rename ρ (id↓ A ↦↑ d) = refl
  domain-seal-rename ρ (`∀↑ c) = refl
  domain-seal-rename ρ (id↑ A) = refl

  seal-at-rename : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′) n (M : Term Δ)
    → seal-at n (renameᵗᵐ ρ M) ≡ map (toRenameᵗ ρ) (seal-at n M)
  seal-at-rename ρ n (` x) = refl
  seal-at-rename ρ n (ƛ M) = refl
  seal-at-rename ρ n (L · M) = refl
  seal-at-rename ρ n (Λ M) = refl
  seal-at-rename ρ n (M ⦂∀ B [ A ]) = refl
  seal-at-rename ρ n ($ κ) = refl
  seal-at-rename ρ n (L ⊕[ op ] M) = refl
  seal-at-rename ρ n (M ⟨ c ⟩) = refl
  seal-at-rename ρ zero (M ↑ c) = domain-seal-rename ρ c
  seal-at-rename ρ (suc n) (M ↑ c) = seal-at-rename ρ n M
  seal-at-rename ρ n (M ↓ c) = refl
  seal-at-rename ρ n blame = refl

  skip-not-zero : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′) (X : Maybe (TyVar Δ))
    → just Fin.zero ≡ map (toRenameᵗ (C.skip ρ)) X → ⊥
  skip-not-zero ρ nothing ()
  skip-not-zero ρ (just X) ()

-- The returned type mentions only old X, but the function itself contains
-- the private seal Z at zero. Type-level non-occurrence is insufficient.

wrapped-function-not-lowered : (V : Term 2)
  → wrapped-function ≡ ⇑ᵗᵐ V → ⊥
wrapped-function-not-lowered V eq = skip-not-zero C.id↪ᵗ (seal-at 2 V)
  (trans (cong (seal-at 2) eq) (seal-at-rename wk↪ᵗ 2 V))

private
  no-name-in-empty : 1 ↪ᵗ 0 → ⊥
  no-name-in-empty ()

  middle-not-natural :
    store-bind (preciseStore (core First.paired)) (＇ Fin.zero)
      ∋ Fin.suc Fin.zero ⦂ ‵ `ℕ → ⊥
  middle-not-natural (S-bind∋ (Z∋ refl) ())

  newest-not-oldest :
    store-bind (preciseStore (core First.paired)) (＇ Fin.zero)
      ∋ Fin.zero ⦂ ＇ (Fin.suc (Fin.suc Fin.zero)) → ⊥
  newest-not-oldest (Z∋ ())

-- Choosing another embedding of the same paired world cannot help:
-- keeping Z instead would give the wrong representation for X or Y.
-- This quantifies over every embedding, not just the weakening witness.

wrapped-function-not-in-paired-scope : (ρ : 2 ↪ᵗ 3)
  → StoreRename (toRenameᵗ ρ) (preciseStore (core First.paired))
      (store-bind (preciseStore (core First.paired)) (＇ Fin.zero))
  → (V : Term 2)
  → wrapped-function ≡ renameᵗᵐ ρ V → ⊥
wrapped-function-not-in-paired-scope (C.keep (C.keep ρ)) h V eq =
  middle-not-natural (h (S-bind∋ (Z∋ refl) refl))
wrapped-function-not-in-paired-scope (C.keep (C.skip (C.keep ρ))) h V eq =
  newest-not-oldest (h (Z∋ refl))
wrapped-function-not-in-paired-scope (C.keep (C.skip (C.skip ρ))) h V eq =
  no-name-in-empty ρ
wrapped-function-not-in-paired-scope (C.skip ρ) h V eq =
  skip-not-zero ρ (seal-at 2 V)
    (trans (cong (seal-at 2) eq) (seal-at-rename (C.skip ρ) 2 V))
