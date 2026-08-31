module proof.LR-narrow.IntegratedProducerSteps where

-- File Charter:
--   * Operational kernels for the integrated dynamic-payload producer
--     λ x : X. x⟨X!⟩ under structural reveal adapters.
--   * Proves typing and exact evaluator equations for one direct Nat adapter
--     and two alias adapters X↦Nat, Y↦X.
--   * This file is independent of IntegratedModel and IntegratedData.

open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

open import Types
open import TyStore
open import TermCtx using (Z)
import Consistency as C
open C using (Env∼; _⊢_∼★)
open import CastTerms
open import Conversion
open import Reduction
open import Primitives using (κℕ)
open import Interpreter
import Eval as E
open import LR-narrow.LogicalRelation using (groundInjection)
open import proof.Consistency as PC using (rename∼★ᵐ)
open import proof.LR-narrow.Closure using (rename-ground-injection)
open import proof.LR-narrow.PhysicalScope

lift-application : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
  → (p : ScopeFuture S T) → ∀ L M
  → liftTerm p (L · M) ≡ liftTerm p L · liftTerm p M
lift-application stay L M = refl
lift-application (grow p) L M = lift-application p (⇑ᵗᵐ L) (⇑ᵗᵐ M)

inject-function : ∀ {Δ} (X : TyVar Δ) {μ : Env∼ Δ}
  → μ ⊢ ＇ X ∼★
  → Term Δ
inject-function X gate =
  ƛ (` 0 ⟨ groundInjection (＇ X) gate ⟩)

shift-inject-function : ∀ {Δ} {X : TyVar Δ} {μ : Env∼ Δ}
    {gate : μ ⊢ ＇ X ∼★}
  → ⇑ᵗᵐ (inject-function X gate)
      ≡ inject-function (C.toRenameᵗ C.wk↪ᵗ X)
          (rename∼★ᵐ C.wk↪ᵗ gate)
shift-inject-function {X = X} {gate = gate}
    rewrite rename-ground-injection (＇ X) gate = refl

inject-function-value : ∀ {Δ} {X : TyVar Δ} {μ : Env∼ Δ}
    {gate : μ ⊢ ＇ X ∼★}
  → Value (inject-function X gate)
inject-function-value = ƛ (` 0 ⟨ groundInjection (＇ _) _ ⟩)

inject-function-⊢ : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {μ : Env∼ Δ} {gate : μ ⊢ ＇ X ∼★}
  → ⟨ Δ , Σ , [] ⟩ ⊢ inject-function X gate ⦂ (＇ X ⇒ ★)
inject-function-⊢ = ⊢ƛ (⊢⟨⟩ (⊢` Z) (groundInjection (＇ _) _))

inject-function-inert : ∀ {Δ} {X : TyVar Δ} {μ : Env∼ Δ}
    {gate : μ ⊢ ＇ X ∼★}
  → Inert (groundInjection (＇ X) gate)
inject-function-inert {gate = gate} = inj ⦃ G∼★ = gate ⦄

one-adapter-function : ∀ {Δ} (X : TyVar Δ) {μ : Env∼ Δ}
  → μ ⊢ ＇ X ∼★
  → Term Δ
one-adapter-function X gate =
  inject-function X gate ↑ (seal X (‵ `ℕ) ↦↑ id↑ ★)

shift-one-adapter-function : ∀ {Δ} {X : TyVar Δ} {μ : Env∼ Δ}
    {gate : μ ⊢ ＇ X ∼★}
  → ⇑ᵗᵐ (one-adapter-function X gate)
      ≡ one-adapter-function (C.toRenameᵗ C.wk↪ᵗ X)
          (rename∼★ᵐ C.wk↪ᵗ gate)
shift-one-adapter-function {X = X} {gate = gate}
    rewrite shift-inject-function {X = X} {gate = gate} = refl

one-adapter-function-value : ∀ {Δ} {X : TyVar Δ} {μ : Env∼ Δ}
    {gate : μ ⊢ ＇ X ∼★}
  → Value (one-adapter-function X gate)
one-adapter-function-value = inject-function-value ↑ fun

one-adapter-function-⊢ : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {μ : Env∼ Δ} {gate : μ ⊢ ＇ X ∼★}
  → Σ ∋ X ⦂ ‵ `ℕ
  → ⟨ Δ , Σ , [] ⟩ ⊢ one-adapter-function X gate ⦂ (‵ `ℕ ⇒ ★)
one-adapter-function-⊢ entry =
  ⊢reveal (⊢↑-⇒ (⊢↓-seal entry) ⊢↑-id) inject-function-⊢

one-adapter : ∀ {Δ} (X : TyVar Δ) {μ : Env∼ Δ}
  → μ ⊢ ＇ X ∼★
  → ℕ
  → Term Δ
one-adapter X gate n = one-adapter-function X gate · $ (κℕ n)

shift-one-adapter : ∀ {Δ} {X : TyVar Δ} {μ : Env∼ Δ}
    {gate : μ ⊢ ＇ X ∼★} n
  → ⇑ᵗᵐ (one-adapter X gate n)
      ≡ one-adapter (C.toRenameᵗ C.wk↪ᵗ X)
          (rename∼★ᵐ C.wk↪ᵗ gate) n
shift-one-adapter {X = X} {gate = gate} n
    rewrite shift-one-adapter-function {X = X} {gate = gate} = refl

one-adapter-result : ∀ {Δ} (X : TyVar Δ) {μ : Env∼ Δ}
  → μ ⊢ ＇ X ∼★
  → ℕ
  → Term Δ
one-adapter-result X gate n =
  ($ (κℕ n) ↓ seal X (‵ `ℕ)) ⟨ groundInjection (＇ X) gate ⟩

shift-one-adapter-result : ∀ {Δ} {X : TyVar Δ} {μ : Env∼ Δ}
    {gate : μ ⊢ ＇ X ∼★} n
  → ⇑ᵗᵐ (one-adapter-result X gate n)
      ≡ one-adapter-result (C.toRenameᵗ C.wk↪ᵗ X)
          (rename∼★ᵐ C.wk↪ᵗ gate) n
shift-one-adapter-result {X = X} {gate = gate} n
    rewrite rename-ground-injection (＇ X) gate = refl

one-adapter-result-value : ∀ {Δ} {X : TyVar Δ} {μ : Env∼ Δ}
    {gate : μ ⊢ ＇ X ∼★} {n}
  → Value (one-adapter-result X gate n)
one-adapter-result-value =
  (($ (κℕ _) ↓ seal) 《 inject-function-inert 》)

one-adapter-⊢ : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {μ : Env∼ Δ} {gate : μ ⊢ ＇ X ∼★} n
  → Σ ∋ X ⦂ ‵ `ℕ
  → ⟨ Δ , Σ , [] ⟩ ⊢ one-adapter X gate n ⦂ ★
one-adapter-⊢ n entry =
  ⊢· (one-adapter-function-⊢ entry) (⊢$ (κℕ n))

one-adapter-result-⊢ : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {μ : Env∼ Δ} {gate : μ ⊢ ＇ X ∼★} n
  → Σ ∋ X ⦂ ‵ `ℕ
  → ⟨ Δ , Σ , [] ⟩ ⊢ one-adapter-result X gate n ⦂ ★
one-adapter-result-⊢ n entry =
  ⊢⟨⟩ (⊢conceal (⊢↓-seal entry) (⊢$ (κℕ n)))
    (groundInjection (＇ _) _)

one-adapter-↠ : ∀ {Δ} {X : TyVar Δ} {μ : Env∼ Δ}
    {gate : μ ⊢ ＇ X ∼★} n
  → one-adapter X gate n
      —↠[ keep ∷ keep ∷ keep ∷ [] ] one-adapter-result X gate n
one-adapter-↠ {X = X} {gate = gate} n =
    one-adapter X gate n
  —→[ keep ]⟨
      pure-step (β-reveal-⇒ inject-function-value ($ (κℕ n))) ⟩
    ((inject-function X gate · ($ (κℕ n) ↓ seal X (‵ `ℕ)))
      ↑ id↑ ★)
  —→[ keep ]⟨
      ξ-reveal
        (pure-step (β (($ (κℕ n)) ↓ seal)))
        refl ⟩
    (one-adapter-result X gate n ↑ id↑ ★)
  —→[ keep ]⟨ pure-step (id-reveal one-adapter-result-value) ⟩
    one-adapter-result X gate n ∎[]

one-adapter-return : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {μ : Env∼ Δ} {gate : μ ⊢ ＇ X ∼★} n
  → interpretFrom Σ 3 (one-adapter X gate n)
      ≡ returned (E.result Δ (keep ∷ keep ∷ keep ∷ [])
        (one-adapter-result X gate n) (one-adapter-↠ n)
        one-adapter-result-value)
one-adapter-return n = refl

one-adapter-lift-↠ : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    {X : TyVar Δ} {μ : Env∼ Δ} {gate : μ ⊢ ＇ X ∼★} n
  → (p : ScopeFuture S T)
  → liftTerm p (one-adapter X gate n)
      —↠[ keep ∷ keep ∷ keep ∷ [] ]
        liftTerm p (one-adapter-result X gate n)
one-adapter-lift-↠ n stay = one-adapter-↠ n
one-adapter-lift-↠ {X = X} {gate = gate} n (grow p)
    rewrite shift-one-adapter {X = X} {gate = gate} n
          | shift-one-adapter-result {X = X} {gate = gate} n =
  one-adapter-lift-↠ n p

one-adapter-result-lift-value : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    {X : TyVar Δ} {μ : Env∼ Δ} {gate : μ ⊢ ＇ X ∼★} n
  → (p : ScopeFuture S T)
  → Value (liftTerm p (one-adapter-result X gate n))
one-adapter-result-lift-value n stay = one-adapter-result-value
one-adapter-result-lift-value {X = X} {gate = gate} n (grow p)
    rewrite shift-one-adapter-result {X = X} {gate = gate} n =
  one-adapter-result-lift-value n p

one-adapter-lift-return : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    {X : TyVar Δ} {μ : Env∼ Δ} {gate : μ ⊢ ＇ X ∼★} n
  → (p : ScopeFuture S T)
  → interpretFrom (scopeStore T) 3 (liftTerm p (one-adapter X gate n))
      ≡ returned (E.result Δ′ (keep ∷ keep ∷ keep ∷ [])
        (liftTerm p (one-adapter-result X gate n))
        (one-adapter-lift-↠ n p)
        (one-adapter-result-lift-value n p))
one-adapter-lift-return {Δ = Δ} {S = S} {X = X} {gate = gate}
    n stay =
  one-adapter-return {Δ = Δ} {Σ = scopeStore S} {X = X}
    {gate = gate} n
one-adapter-lift-return {X = X} {gate = gate} n (grow p)
    rewrite shift-one-adapter {X = X} {gate = gate} n
          | shift-one-adapter-result {X = X} {gate = gate} n =
  one-adapter-lift-return n p

two-adapters-function : ∀ {Δ} (X Y : TyVar Δ) {μ : Env∼ Δ}
  → μ ⊢ ＇ Y ∼★
  → Term Δ
two-adapters-function X Y gate =
  ((inject-function Y gate ↑ (seal Y (＇ X) ↦↑ id↑ ★))
    ↑ (seal X (‵ `ℕ) ↦↑ id↑ ★))

shift-two-adapters-function : ∀ {Δ} {X Y : TyVar Δ} {μ : Env∼ Δ}
    {gate : μ ⊢ ＇ Y ∼★}
  → ⇑ᵗᵐ (two-adapters-function X Y gate)
      ≡ two-adapters-function (C.toRenameᵗ C.wk↪ᵗ X)
          (C.toRenameᵗ C.wk↪ᵗ Y) (rename∼★ᵐ C.wk↪ᵗ gate)
shift-two-adapters-function {X = X} {Y = Y} {gate = gate}
    rewrite shift-inject-function {X = Y} {gate = gate} = refl

two-adapters-function-value : ∀ {Δ} {X Y : TyVar Δ} {μ : Env∼ Δ}
    {gate : μ ⊢ ＇ Y ∼★}
  → Value (two-adapters-function X Y gate)
two-adapters-function-value = (inject-function-value ↑ fun) ↑ fun

two-adapters-function-⊢ : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
    {μ : Env∼ Δ} {gate : μ ⊢ ＇ Y ∼★}
  → Σ ∋ X ⦂ ‵ `ℕ
  → Σ ∋ Y ⦂ ＇ X
  → ⟨ Δ , Σ , [] ⟩ ⊢ two-adapters-function X Y gate ⦂ (‵ `ℕ ⇒ ★)
two-adapters-function-⊢ x-entry y-entry =
  ⊢reveal (⊢↑-⇒ (⊢↓-seal x-entry) ⊢↑-id)
    (⊢reveal (⊢↑-⇒ (⊢↓-seal y-entry) ⊢↑-id)
      inject-function-⊢)

two-adapters : ∀ {Δ} (X Y : TyVar Δ) {μ : Env∼ Δ}
  → μ ⊢ ＇ Y ∼★
  → ℕ
  → Term Δ
two-adapters X Y gate n = two-adapters-function X Y gate · $ (κℕ n)

shift-two-adapters : ∀ {Δ} {X Y : TyVar Δ} {μ : Env∼ Δ}
    {gate : μ ⊢ ＇ Y ∼★} n
  → ⇑ᵗᵐ (two-adapters X Y gate n)
      ≡ two-adapters (C.toRenameᵗ C.wk↪ᵗ X)
          (C.toRenameᵗ C.wk↪ᵗ Y) (rename∼★ᵐ C.wk↪ᵗ gate) n
shift-two-adapters {X = X} {Y = Y} {gate = gate} n
    rewrite shift-two-adapters-function {X = X} {Y = Y} {gate = gate} = refl

two-adapters-result : ∀ {Δ} (X Y : TyVar Δ) {μ : Env∼ Δ}
  → μ ⊢ ＇ Y ∼★
  → ℕ
  → Term Δ
two-adapters-result X Y gate n =
  (($ (κℕ n) ↓ seal X (‵ `ℕ)) ↓ seal Y (＇ X))
    ⟨ groundInjection (＇ Y) gate ⟩

shift-two-adapters-result : ∀ {Δ} {X Y : TyVar Δ} {μ : Env∼ Δ}
    {gate : μ ⊢ ＇ Y ∼★} n
  → ⇑ᵗᵐ (two-adapters-result X Y gate n)
      ≡ two-adapters-result (C.toRenameᵗ C.wk↪ᵗ X)
          (C.toRenameᵗ C.wk↪ᵗ Y) (rename∼★ᵐ C.wk↪ᵗ gate) n
shift-two-adapters-result {Y = Y} {gate = gate} n
    rewrite rename-ground-injection (＇ Y) gate = refl

two-adapters-result-value : ∀ {Δ} {X Y : TyVar Δ} {μ : Env∼ Δ}
    {gate : μ ⊢ ＇ Y ∼★} {n}
  → Value (two-adapters-result X Y gate n)
two-adapters-result-value =
  ((($ (κℕ _) ↓ seal) ↓ seal) 《 inject-function-inert 》)

two-adapters-⊢ : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
    {μ : Env∼ Δ} {gate : μ ⊢ ＇ Y ∼★} n
  → Σ ∋ X ⦂ ‵ `ℕ
  → Σ ∋ Y ⦂ ＇ X
  → ⟨ Δ , Σ , [] ⟩ ⊢ two-adapters X Y gate n ⦂ ★
two-adapters-⊢ n x-entry y-entry =
  ⊢· (two-adapters-function-⊢ x-entry y-entry) (⊢$ (κℕ n))

two-adapters-result-⊢ : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
    {μ : Env∼ Δ} {gate : μ ⊢ ＇ Y ∼★} n
  → Σ ∋ X ⦂ ‵ `ℕ
  → Σ ∋ Y ⦂ ＇ X
  → ⟨ Δ , Σ , [] ⟩ ⊢ two-adapters-result X Y gate n ⦂ ★
two-adapters-result-⊢ n x-entry y-entry =
  ⊢⟨⟩
    (⊢conceal (⊢↓-seal y-entry)
      (⊢conceal (⊢↓-seal x-entry) (⊢$ (κℕ n))))
    (groundInjection (＇ _) _)

two-adapters-↠ : ∀ {Δ} {X Y : TyVar Δ} {μ : Env∼ Δ}
    {gate : μ ⊢ ＇ Y ∼★} n
  → two-adapters X Y gate n
      —↠[ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ]
        two-adapters-result X Y gate n
two-adapters-↠ {X = X} {Y} {gate = gate} n =
    two-adapters X Y gate n
  —→[ keep ]⟨
      pure-step
        (β-reveal-⇒ (inject-function-value ↑ fun) ($ (κℕ n))) ⟩
    (((inject-function Y gate ↑ (seal Y (＇ X) ↦↑ id↑ ★))
        · ($ (κℕ n) ↓ seal X (‵ `ℕ)))
      ↑ id↑ ★)
  —→[ keep ]⟨
      ξ-reveal
        (pure-step
          (β-reveal-⇒ inject-function-value (($ (κℕ n)) ↓ seal)))
        refl ⟩
    (((inject-function Y gate
        · (($ (κℕ n) ↓ seal X (‵ `ℕ)) ↓ seal Y (＇ X)))
      ↑ id↑ ★) ↑ id↑ ★)
  —→[ keep ]⟨
      ξ-reveal
        (ξ-reveal
          (pure-step (β ((($ (κℕ n)) ↓ seal) ↓ seal)))
          refl)
        refl ⟩
    ((two-adapters-result X Y gate n ↑ id↑ ★) ↑ id↑ ★)
  —→[ keep ]⟨
      ξ-reveal (pure-step (id-reveal two-adapters-result-value)) refl ⟩
    (two-adapters-result X Y gate n ↑ id↑ ★)
  —→[ keep ]⟨ pure-step (id-reveal two-adapters-result-value) ⟩
    two-adapters-result X Y gate n ∎[]

two-adapters-return : ∀ {Δ} {Σ : TyStore Δ} {X Y : TyVar Δ}
    {μ : Env∼ Δ} {gate : μ ⊢ ＇ Y ∼★} n
  → interpretFrom Σ 5 (two-adapters X Y gate n)
      ≡ returned (E.result Δ
        (keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [])
        (two-adapters-result X Y gate n) (two-adapters-↠ n)
        two-adapters-result-value)
two-adapters-return n = refl

two-adapters-lift-↠ : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    {X Y : TyVar Δ} {μ : Env∼ Δ} {gate : μ ⊢ ＇ Y ∼★} n
  → (p : ScopeFuture S T)
  → liftTerm p (two-adapters X Y gate n)
      —↠[ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ]
        liftTerm p (two-adapters-result X Y gate n)
two-adapters-lift-↠ n stay = two-adapters-↠ n
two-adapters-lift-↠ {X = X} {Y = Y} {gate = gate} n (grow p)
    rewrite shift-two-adapters {X = X} {Y = Y} {gate = gate} n
          | shift-two-adapters-result {X = X} {Y = Y} {gate = gate} n =
  two-adapters-lift-↠ n p

two-adapters-result-lift-value : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    {X Y : TyVar Δ} {μ : Env∼ Δ} {gate : μ ⊢ ＇ Y ∼★} n
  → (p : ScopeFuture S T)
  → Value (liftTerm p (two-adapters-result X Y gate n))
two-adapters-result-lift-value n stay = two-adapters-result-value
two-adapters-result-lift-value {X = X} {Y = Y} {gate = gate} n (grow p)
    rewrite shift-two-adapters-result {X = X} {Y = Y} {gate = gate} n =
  two-adapters-result-lift-value n p

two-adapters-lift-return : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    {X Y : TyVar Δ} {μ : Env∼ Δ} {gate : μ ⊢ ＇ Y ∼★} n
  → (p : ScopeFuture S T)
  → interpretFrom (scopeStore T) 5 (liftTerm p (two-adapters X Y gate n))
      ≡ returned (E.result Δ′
        (keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [])
        (liftTerm p (two-adapters-result X Y gate n))
        (two-adapters-lift-↠ n p)
        (two-adapters-result-lift-value n p))
two-adapters-lift-return {Δ = Δ} {S = S} {X = X} {Y = Y}
    {gate = gate} n stay =
  two-adapters-return {Δ = Δ} {Σ = scopeStore S} {X = X}
    {Y = Y} {gate = gate} n
two-adapters-lift-return {X = X} {Y = Y} {gate = gate} n (grow p)
    rewrite shift-two-adapters {X = X} {Y = Y} {gate = gate} n
          | shift-two-adapters-result {X = X} {Y = Y} {gate = gate} n =
  two-adapters-lift-return n p
