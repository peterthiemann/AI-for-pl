module proof.LR-narrow.ScopedReturnsExperiment where

-- File Charter:
--   * Proof-local return observations with a smaller visible precise scope.
--   * Reuses lookup-preserving store renaming and injective embeddings;
--     returned syntax and all caller terms must respect the same embedding.
--   * Checks the literal counterexample and an allocating continuation.
--   * Does not change the live LR or assert general evaluation equivariance.

open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; ∃-syntax)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans; sym)

open import Types
open import TyStore
open import TermCtx using (Z)
open import Primitives using (κℕ; addℕ; δ-add)
open import CastTerms
open import Conversion
open import Reduction
import Consistency as C
open import Consistency using (_↪ᵗ_; toRenameᵗ; wk↪ᵗ)
import Eval as E
open import Interpreter
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.Computation using (IndexedValueRelation)
open import LR-narrow.LogicalRelation
open import proof.TypeInTermSubst using
  (StoreRename; StoreRename-wk-bind; toRename-keep-eq)
open import proof.LR-narrow.Constant using
  (constant-values-related; constant-values-related-future)
import proof.LR-narrow.ScopeExperiment as First

-- A private runtime allocation is hidden only if the returned syntax is
-- literally in the image of the embedding. The caller-action field keeps
-- every old name accessible; the store field preserves representations,
-- not just cardinalities or returned ground values. The target is unchanged.

data ScopedReturns {Δᴾ Δᴵ Δᶜ}
    {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
    (W : World Δᴾ Δᴵ Δᶜ) (R : IndexedValueRelation W) (k : ℕ) :
    E.EvalResult Mᴵ → E.EvalResult Mᴾ → Set where
  scoped-returns : ∀ {resultᴵ : E.EvalResult Mᴵ}
      {resultᴾ : E.EvalResult Mᴾ} {Δᵛ Δᶜ′}
    → (W′ : World Δᵛ (E.Δ′ resultᴵ) Δᶜ′)
    → (future : Future W W′)
    → (ρ : Δᵛ ↪ᵗ E.Δ′ resultᴾ)
    → impreciseStore (core W′) ≡
        E.changes resultᴵ ▶ˢ impreciseStore (core W)
    → StoreRename (toRenameᵗ ρ) (preciseStore (core W′))
        (E.changes resultᴾ ▶ˢ preciseStore (core W))
    → (∀ M → E.changes resultᴵ ▶ᵀ M ≡ liftImpreciseTerm future M)
    → (∀ M → E.changes resultᴾ ▶ᵀ M ≡
        renameᵗᵐ ρ (liftPreciseTerm future M))
    → (V : Term Δᵛ)
    → E.term resultᴾ ≡ renameᵗᵐ ρ V
    → R W′ future k (E.term resultᴵ) V
    → ScopedReturns W R k resultᴵ resultᴾ

literal-returns : ∀ k
  → ScopedReturns First.initial (FutureValueRelation (I.ι⊑ι {ι = `ℕ})) k
      First.bare-result First.wrapped-result
literal-returns k = scoped-returns First.paired
  (future-paired future-refl I.X⊑X)
  wk↪ᵗ refl StoreRename-wk-bind (λ M → refl) (λ M → refl)
  ($ (κℕ 7)) refl
  (constant-values-related-future
    (future-paired future-refl I.X⊑X)
    k (κℕ 7))

-- A subsequent visible allocation goes ABOVE the hidden name. Keeping
-- the new slot in the embedding (rather than weakening again) preserves
-- lookup for both the new name and every older visible name.

store-rename-bind : ∀ {Δ Δ′} {ρ : Δ ↪ᵗ Δ′} {Σ Σ′}
  → StoreRename (toRenameᵗ ρ) Σ Σ′
  → (A : Ty Δ)
  → StoreRename (toRenameᵗ (C.keep ρ)) (store-bind Σ A)
      (store-bind Σ′ (renameᵗ (toRenameᵗ ρ) A))
store-rename-bind {ρ = ρ} h A (Z∋ eq) = Z∋
  (trans (cong (renameᵗ (toRenameᵗ (C.keep ρ))) eq)
    (trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq ρ))
      (renameᵗ-shift (toRenameᵗ ρ) A)))
store-rename-bind {ρ = ρ} h A (S-bind∋ {A = B} entry eq) =
  S-bind∋ (h entry)
    (trans (cong (renameᵗ (toRenameᵗ (C.keep ρ))) eq)
      (trans (renameᵗ-cong (⇑ᵗ B) (toRename-keep-eq ρ))
        (renameᵗ-shift (toRenameᵗ ρ) B)))

store-rename-hide : ∀ {Δ Δ′} {ρ : Δ ↪ᵗ Δ′} {Σ Σ′}
  → StoreRename (toRenameᵗ ρ) Σ Σ′
  → (A : Ty Δ′)
  → StoreRename (toRenameᵗ (C.skip ρ)) Σ (store-bind Σ′ A)
store-rename-hide {ρ = ρ} h A {A = B} entry =
  S-bind∋ (h entry) (sym (renameᵗ-comp (toRenameᵗ ρ) Fin.suc B))

-- An executable continuation: allocate at a visible name, then add one
-- to the previously returned natural. It exercises type application,
-- function reveal/conceal, beta reduction, and primitive evaluation.

continue : ∀ {Δ} → TyVar Δ → ℕ → Term Δ
continue X n = ((Λ (ƛ (` 0 ⊕[ addℕ ] $ (κℕ n))))
  ⦂∀ (‵ `ℕ ⇒ ‵ `ℕ) [ ＇ X ]) · $ (κℕ 1)

continue-⊢ : ∀ {Δ} {Σ : TyStore Δ} X n
  → ⟨ Δ , Σ , [] ⟩ ⊢ continue X n ⦂ ‵ `ℕ
continue-⊢ X n = ⊢·
  (⊢• (⊢Λ (ƛ (` 0 ⊕[ addℕ ] $ (κℕ n)))
    (⊢ƛ (⊢⊕ addℕ (⊢` Z) (⊢$ (κℕ n))))))
  (⊢$ (κℕ 1))

continue-↠ : ∀ {Δ} (X : TyVar Δ) n
  → continue X n
      —↠[ bind (＇ X) ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ]
      $ (κℕ (suc n))
continue-↠ X n =
    ((Λ (ƛ (` 0 ⊕[ addℕ ] $ (κℕ n))))
      ⦂∀ (‵ `ℕ ⇒ ‵ `ℕ) [ ＇ X ]) · $ (κℕ 1)
  —→[ bind (＇ X) ]⟨
      ξ-·₁ (β-Λ (ƛ (` 0 ⊕[ addℕ ] $ (κℕ n)))) refl ⟩
    ((ƛ (` 0 ⊕[ addℕ ] $ (κℕ n)))
      ↑ (id↓ (‵ `ℕ) ↦↑ id↑ (‵ `ℕ))) · $ (κℕ 1)
  —→[ keep ]⟨ pure-step
      (β-reveal-⇒ (ƛ (` 0 ⊕[ addℕ ] $ (κℕ n))) ($ (κℕ 1))) ⟩
    ((ƛ (` 0 ⊕[ addℕ ] $ (κℕ n)))
      · ($ (κℕ 1) ↓ id↓ (‵ `ℕ))) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ ξ-reveal
      (ξ-·₂ (ƛ (` 0 ⊕[ addℕ ] $ (κℕ n)))
        (pure-step (id-conceal ($ (κℕ 1)))) refl) refl ⟩
    ((ƛ (` 0 ⊕[ addℕ ] $ (κℕ n))) · $ (κℕ 1)) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ ξ-reveal (pure-step (β ($ (κℕ 1)))) refl ⟩
    ($ (κℕ 1) ⊕[ addℕ ] $ (κℕ n)) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ ξ-reveal (pure-step (δ-⊕ δ-add)) refl ⟩
    $ (κℕ (suc n)) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ pure-step (id-reveal ($ (κℕ (suc n)))) ⟩
    $ (κℕ (suc n)) ∎[]

continue-result : ∀ {Δ} (X : TyVar Δ) n → E.EvalResult (continue X n)
continue-result {Δ} X n = E.result (suc Δ)
  (bind (＇ X) ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [])
  ($ (κℕ (suc n))) (continue-↠ X n) ($ (κℕ (suc n)))

continue-eval : ∀ {Δ} (Σ : TyStore Δ) X n gas
  → interpretFrom Σ (suc (suc (suc (suc (suc (suc gas))))))
      (continue X n) ≡ returned (continue-result X n)
continue-eval Σ X n zero = refl
continue-eval Σ X n (suc gas) = refl

continue-rename : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′) X n
  → renameᵗᵐ ρ (continue X n) ≡ continue (toRenameᵗ ρ X) n
continue-rename ρ X n = refl

-- This is a proved, fuel-independent test for the continuation family,
-- not an assumed compatibility field and not a theorem for all programs.

continue-scope : ∀ {Δ Δ′} {ρ : Δ ↪ᵗ Δ′}
    {Σ : TyStore Δ} {Σ′ : TyStore Δ′}
  → StoreRename (toRenameᵗ ρ) Σ Σ′
  → (X : TyVar Δ) → (n gas : ℕ)
  → (interpretFrom Σ (suc (suc (suc (suc (suc (suc gas))))))
        (continue X n) ≡ returned (continue-result X n))
    × (interpretFrom Σ′ (suc (suc (suc (suc (suc (suc gas))))))
        (continue (toRenameᵗ ρ X) n)
        ≡ returned (continue-result (toRenameᵗ ρ X) n))
    × StoreRename (toRenameᵗ (C.keep ρ))
        (E.changes (continue-result X n) ▶ˢ Σ)
        (E.changes (continue-result (toRenameᵗ ρ X) n) ▶ˢ Σ′)
    × (E.term (continue-result (toRenameᵗ ρ X) n)
        ≡ renameᵗᵐ (C.keep ρ) (E.term (continue-result X n)))
continue-scope {Σ = Σ} {Σ′} h X n gas =
  continue-eval Σ X n gas , continue-eval Σ′ _ n gas ,
  store-rename-bind h (＇ X) , refl

continued-world : World 3 3 3
continued-world = pairedBindWorld First.paired
  (＇ Fin.zero) (＇ Fin.zero) I.X⊑X

literal-continued-store : StoreRename (toRenameᵗ (C.keep wk↪ᵗ))
  (preciseStore (core continued-world))
  (E.changes (continue-result (Fin.suc Fin.zero) 7)
    ▶ˢ (E.changes First.wrapped-result
      ▶ˢ preciseStore (core First.initial)))
literal-continued-store = store-rename-bind StoreRename-wk-bind (＇ Fin.zero)

literal-continued-values : ∀ k
  → ValueImprecision continued-world I.ι⊑ι k
      (E.term (continue-result {Δ = 2} Fin.zero 7)) ($ (κℕ 8))
literal-continued-values k = constant-values-related k (κℕ 8)
