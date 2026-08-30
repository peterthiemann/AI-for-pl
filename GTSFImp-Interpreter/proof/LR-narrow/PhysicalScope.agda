module proof.LR-narrow.PhysicalScope where

-- File Charter:
--   * Physical stores extending a fixed visible root by fresh allocations.
--   * Futures retain every old physical name, including private names, and
--     provide coherent actions on types, terms, values, and store lookups.
--   * Interpreter histories determine their result scopes independently.
--   * This fixed-root prototype does not extend the visible type environment.

open import Data.List using ([])
open import Data.Nat using (suc)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans) renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import Primitives using (Const)
open import Reduction
open import Consistency using (wk↪ᵗ)
open import proof.TypeInTermSubst using
  (typing-shiftᵗ-bind; renameᵗᵐ-preserves-Value; toRename-wk-eq;
   renameᵗ-wk-eq)

data PhysicalScope {Δ₀} (Σ₀ : TyStore Δ₀) : TyCtx → Set where
  root : PhysicalScope Σ₀ Δ₀
  allocate : ∀ {Δ} → PhysicalScope Σ₀ Δ → Ty Δ
    → PhysicalScope Σ₀ (suc Δ)

scopeStore : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀} → PhysicalScope Σ₀ Δ → TyStore Δ
scopeStore {Σ₀ = Σ₀} root = Σ₀
scopeStore (allocate S A) = store-bind (scopeStore S) A

scopeTy : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
  → PhysicalScope Σ₀ Δ → Ty Δ₀ → Ty Δ
scopeTy root A = A
scopeTy (allocate S B) A = ⇑ᵗ (scopeTy S A)

scopeVar : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
  → PhysicalScope Σ₀ Δ → TyVar Δ₀ → TyVar Δ
scopeVar root X = X
scopeVar (allocate S B) X = Fin.suc (scopeVar S X)

scope-entry : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀} (S : PhysicalScope Σ₀ Δ) {X A}
  → Σ₀ ∋ X ⦂ A → scopeStore S ∋ scopeVar S X ⦂ scopeTy S A
scope-entry root entry = entry
scope-entry (allocate S B) entry = S-bind∋ (scope-entry S entry) refl

scope-variable : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀} (S : PhysicalScope Σ₀ Δ) X
  → scopeTy S (＇ X) ≡ ＇ scopeVar S X
scope-variable root X = refl
scope-variable (allocate S B) X = cong ⇑ᵗ (scope-variable S X)

scope-natural : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀} (S : PhysicalScope Σ₀ Δ)
  → scopeTy S (‵ `ℕ) ≡ ‵ `ℕ
scope-natural root = refl
scope-natural (allocate S B) = cong ⇑ᵗ (scope-natural S)

scope-arrow : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀} (S : PhysicalScope Σ₀ Δ) A B
  → scopeTy S (A ⇒ B) ≡ (scopeTy S A ⇒ scopeTy S B)
scope-arrow root A B = refl
scope-arrow (allocate S C) A B = cong ⇑ᵗ (scope-arrow S A B)

data ScopeFuture {Δ₀} {Σ₀ : TyStore Δ₀} : ∀ {Δ Δ′}
    → PhysicalScope Σ₀ Δ → PhysicalScope Σ₀ Δ′ → Set where
  stay : ∀ {Δ} {S : PhysicalScope Σ₀ Δ} → ScopeFuture S S
  grow : ∀ {Δ Δ′} {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′} {A}
    → ScopeFuture (allocate S A) T → ScopeFuture S T

scope-trans : ∀ {Δ₀ Δ₁ Δ₂ Δ₃} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ₁} {T : PhysicalScope Σ₀ Δ₂}
    {U : PhysicalScope Σ₀ Δ₃}
  → ScopeFuture S T → ScopeFuture T U → ScopeFuture S U
scope-trans stay q = q
scope-trans (grow p) q = grow (scope-trans p q)

liftTerm : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
  → ScopeFuture S T → Term Δ → Term Δ′
liftTerm stay M = M
liftTerm (grow p) M = liftTerm p (⇑ᵗᵐ M)

liftTy : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
  → ScopeFuture S T → Ty Δ → Ty Δ′
liftTy stay A = A
liftTy (grow p) A = liftTy p (⇑ᵗ A)

liftVar : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
  → ScopeFuture S T → TyVar Δ → TyVar Δ′
liftVar stay X = X
liftVar (grow p) X = liftVar p (Fin.suc X)

lift-term-comp : ∀ {Δ₀ Δ₁ Δ₂ Δ₃} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ₁} {T : PhysicalScope Σ₀ Δ₂}
    {U : PhysicalScope Σ₀ Δ₃} (p : ScopeFuture S T) (q : ScopeFuture T U) M
  → liftTerm (scope-trans p q) M ≡ liftTerm q (liftTerm p M)
lift-term-comp stay q M = refl
lift-term-comp (grow p) q M = lift-term-comp p q (⇑ᵗᵐ M)

lift-root-type : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
  → (p : ScopeFuture S T) → ∀ A → liftTy p (scopeTy S A) ≡ scopeTy T A
lift-root-type stay A = refl
lift-root-type (grow p) A = lift-root-type p A

lift-value : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′} {V}
  → (p : ScopeFuture S T) → Value V → Value (liftTerm p V)
lift-value stay v = v
lift-value (grow p) v = lift-value p (renameᵗᵐ-preserves-Value wk↪ᵗ v)

lift-typed : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′} {M A}
  → (p : ScopeFuture S T) → ⟨ Δ , scopeStore S , [] ⟩ ⊢ M ⦂ A
  → ⟨ Δ′ , scopeStore T , [] ⟩ ⊢ liftTerm p M ⦂ liftTy p A
lift-typed stay typed = typed
lift-typed (grow p) typed = lift-typed p (typing-shiftᵗ-bind typed)

lift-root-typed : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′} {M A}
  → (p : ScopeFuture S T) → ⟨ Δ , scopeStore S , [] ⟩ ⊢ M ⦂ scopeTy S A
  → ⟨ Δ′ , scopeStore T , [] ⟩ ⊢ liftTerm p M ⦂ scopeTy T A
lift-root-typed {T = T} {M} {A} p typed =
  subst≡ (λ B → ⟨ _ , scopeStore T , [] ⟩ ⊢ liftTerm p M ⦂ B)
    (lift-root-type p A) (lift-typed p typed)

advance : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
  → PhysicalScope Σ₀ Δ → StoreChanges Δ Δ′ → PhysicalScope Σ₀ Δ′
advance S [] = S
advance S (keep ∷ χs) = advance S χs
advance S (bind A ∷ χs) = advance (allocate S A) χs

advance-future : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    (S : PhysicalScope Σ₀ Δ) (χs : StoreChanges Δ Δ′)
  → ScopeFuture S (advance S χs)
advance-future S [] = stay
advance-future S (keep ∷ χs) = advance-future S χs
advance-future S (bind A ∷ χs) = grow (advance-future (allocate S A) χs)

advance-store : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    (S : PhysicalScope Σ₀ Δ) (χs : StoreChanges Δ Δ′)
  → scopeStore (advance S χs) ≡ χs ▶ˢ scopeStore S
advance-store S [] = refl
advance-store S (keep ∷ χs) = advance-store S χs
advance-store S (bind A ∷ χs) = advance-store (allocate S A) χs

advance-term : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    (S : PhysicalScope Σ₀ Δ) (χs : StoreChanges Δ Δ′) M
  → liftTerm (advance-future S χs) M ≡ χs ▶ᵀ M
advance-term S [] M = refl
advance-term S (keep ∷ χs) M = advance-term S χs M
advance-term S (bind A ∷ χs) M = advance-term (allocate S A) χs (⇑ᵗᵐ M)

lift-constant : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    (p : ScopeFuture S T) (c : Const)
  → liftTerm p ($ c) ≡ $ c
lift-constant stay c = refl
lift-constant (grow p) c = lift-constant p c

lift-root-seal : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    (p : ScopeFuture S T) X R U
  → liftTerm p (U ↓ seal (scopeVar S X) (scopeTy S R))
      ≡ liftTerm p U ↓ seal (scopeVar T X) (scopeTy T R)
lift-root-seal stay X R U = refl
lift-root-seal {S = S} (grow p) X R U
    rewrite toRename-wk-eq (scopeVar S X) | renameᵗ-wk-eq (scopeTy S R) =
  lift-root-seal p X R (⇑ᵗᵐ U)
