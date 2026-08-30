module proof.LR-narrow.ScopedUniversalExperiment where

-- File Charter:
--   * Inhabits the paired universal clause with the occurring-binder
--     polymorphic identity for any supplied small family of semantic types.
--   * Uses fresh nominal meanings, function-seal compatibility, and rebasing
--     to relate returned adapters without dropping their allocated names.
--   * Tests paired and right-only constant universals, including wrappers
--     that add an extra precise allocation, for arbitrary type arguments.

open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym)

open import Types
open import TyStore
open import TermCtx using (Z)
open import CastTerms
open import Conversion
open import Primitives using (κℕ)
open import Reduction
import Eval as E
open import Interpreter
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopeRebase
open import proof.LR-narrow.ScopedUniversal
open import proof.LR-narrow.ScopedIdentity
open import proof.LR-narrow.ScopedFunctionSeal using (module Compatibility)
open import proof.LR-narrow.Application using (value-return-exact)
open import LR-narrow.LogicalRelation using (same-natural)

polymorphic-identity : ∀ {Δ} → Term Δ
polymorphic-identity = Λ (ƛ (` 0))

polymorphic-identity-⊢ : ∀ {Δ} {Σ : TyStore Δ}
  → ⟨ Δ , Σ , [] ⟩ ⊢ polymorphic-identity ⦂ `∀ (＇ Fin.zero ⇒ ＇ Fin.zero)
polymorphic-identity-⊢ = ⊢Λ (ƛ (` 0)) (⊢ƛ (⊢` Z))

polymorphic-identity-return : ∀ {Δ} (Σ : TyStore Δ) (R : Ty Δ)
  → interpretFrom Σ 1
      (polymorphic-identity ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ R ])
      ≡ returned (E.result (suc Δ) (bind R ∷ [])
        ((ƛ (` 0)) ↑ (seal Fin.zero (⇑ᵗ R) ↦↑ unseal Fin.zero (⇑ᵗ R)))
        ((polymorphic-identity ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ R ])
          —→[ bind R ]⟨ β-Λ (ƛ (` 0)) ⟩
          ((ƛ (` 0)) ↑ (seal Fin.zero (⇑ᵗ R) ↦↑ unseal Fin.zero (⇑ᵗ R)))
          ∎[]) ((ƛ (` 0)) ↑ fun))
polymorphic-identity-return Σ R = refl

lift-polymorphic-identity : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′} (p : ScopeFuture S T)
  → liftTerm p polymorphic-identity ≡ polymorphic-identity
lift-polymorphic-identity stay = refl
lift-polymorphic-identity (grow p) = lift-polymorphic-identity p

module IdentityInstantiation {Δᴵ Δᴾ} {Σᴵ : TyStore Δᴵ} {Σᴾ : TyStore Δᴾ}
    (A : Model.ScopedType Σᴵ Σᴾ) where

  module B = Model Σᴵ Σᴾ
  module R = Rebase {Σᴵ₀ = Σᴵ} {Σᴾ₀ = Σᴾ}
    (allocate root (B.impreciseTy A)) (allocate root (B.preciseTy A))
  module K = Compatibility (store-bind Σᴵ (B.impreciseTy A))
                           (store-bind Σᴾ (B.preciseTy A))

  adapters-related : ∀ k → B.related (B.arrow A A)
    (allocate root (B.impreciseTy A)) (allocate root (B.preciseTy A)) k
    ((ƛ (` 0)) ↑ (seal Fin.zero (⇑ᵗ (B.impreciseTy A))
      ↦↑ unseal Fin.zero (⇑ᵗ (B.impreciseTy A))))
    ((ƛ (` 0)) ↑ (seal Fin.zero (⇑ᵗ (B.preciseTy A))
      ↦↑ unseal Fin.zero (⇑ᵗ (B.preciseTy A))))
  adapters-related k = R.arrow-from A A
    (K.function-seals-related (R.rebase A) (R.rebase A)
      Fin.zero Fin.zero Fin.zero Fin.zero
      (Z∋ refl) (Z∋ refl) (Z∋ refl) (Z∋ refl)
      (identity-related
        (R.New.nominal (R.rebase A) Fin.zero Fin.zero (Z∋ refl) (Z∋ refl)) k))

  observed : ∀ k → B.ObservedComputations (B.arrow A A) root root k
    (polymorphic-identity ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ B.impreciseTy A ])
    (polymorphic-identity ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ B.preciseTy A ])
  observed k = B.observed-from-returns {gasᴵ = 1} {gasᴾ = 1}
    (polymorphic-identity-return Σᴵ (B.impreciseTy A))
    (polymorphic-identity-return Σᴾ (B.preciseTy A)) (adapters-related k)

-- This is a theorem schema over arbitrary small families, not a claim that
-- the collection of ALL ScopedType records forms a small argument code.

module IdentityFamily {Δᴵ₀ Δᴾ₀} (Σᴵ₀ : TyStore Δᴵ₀) (Σᴾ₀ : TyStore Δᴾ₀)
    (Code : ∀ {Δᴵ Δᴾ}
      → PhysicalScope Σᴵ₀ Δᴵ → PhysicalScope Σᴾ₀ Δᴾ → Set)
    (denote : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
        {T : PhysicalScope Σᴾ₀ Δᴾ}
      → Code S T → Model.ScopedType (scopeStore S) (scopeStore T)) where

  module B = Model Σᴵ₀ Σᴾ₀
  module U = Universals Σᴵ₀ Σᴾ₀

  family : U.PairedFamily (＇ Fin.zero ⇒ ＇ Fin.zero)
                          (＇ Fin.zero ⇒ ＇ Fin.zero)
  family = record
    { Argument = Code
    ; argumentᴵ = λ a → Model.impreciseTy (denote a)
    ; argumentᴾ = λ a → Model.preciseTy (denote a)
    ; result = λ { {S = S} {T} a →
        Model.arrow (scopeStore S) (scopeStore T) (denote a) (denote a) }
    ; resultᴵ = λ { {S = S} a → result-type S (Model.impreciseTy (denote a)) }
    ; resultᴾ = λ { {T = T} a → result-type T (Model.preciseTy (denote a)) }
    }
    where
    result-type : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
        (S : PhysicalScope Σ₀ Δ) (A : Ty Δ)
      → (A ⇒ A) ≡ scopeBody S (＇ Fin.zero ⇒ ＇ Fin.zero) [ A ]ᵗ
    result-type S A rewrite scope-body-arrow S (＇ Fin.zero) (＇ Fin.zero)
      | scope-body-bound S = refl

  related : ∀ k → B.related (U.universal family) root root k
    polymorphic-identity polymorphic-identity
  related k = U.universal-values (Λ (ƛ (` 0))) (Λ (ƛ (` 0)))
    polymorphic-identity-⊢ polymorphic-identity-⊢ call
    where
    call : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
        {T : PhysicalScope Σᴾ₀ Δᴾ} {j}
      → (p : ScopeFuture root S) → (q : ScopeFuture root T)
      → j < k → (a : Code S T)
      → Model.ObservedComputations (scopeStore S) (scopeStore T)
          (U.PairedFamily.result family {S = S} {T = T} a) root root j
          (liftTerm p polymorphic-identity
            ⦂∀ scopeBody S (＇ Fin.zero ⇒ ＇ Fin.zero)
              [ Model.impreciseTy (denote a) ])
          (liftTerm q polymorphic-identity
            ⦂∀ scopeBody T (＇ Fin.zero ⇒ ＇ Fin.zero)
              [ Model.preciseTy (denote a) ])
    call {S = S} {T} {j} p q j<k a
        rewrite lift-polymorphic-identity p | lift-polymorphic-identity q
          | scope-body-arrow S (＇ Fin.zero) (＇ Fin.zero) | scope-body-bound S
          | scope-body-arrow T (＇ Fin.zero) (＇ Fin.zero) | scope-body-bound T =
      IdentityInstantiation.observed (denote a) j

constant-polymorphic : ∀ {Δ} → ℕ → Term Δ
constant-polymorphic n = Λ ($ (κℕ n))

wrapped-constant : ∀ {Δ} → ℕ → Term Δ
wrapped-constant n = constant-polymorphic n ↑ `∀↑ id↑ (‵ `ℕ)

constant-polymorphic-⊢ : ∀ {Δ} {Σ : TyStore Δ} n
  → ⟨ Δ , Σ , [] ⟩ ⊢ constant-polymorphic n ⦂ `∀ (‵ `ℕ)
constant-polymorphic-⊢ n = ⊢Λ ($ (κℕ n)) (⊢$ (κℕ n))

wrapped-constant-⊢ : ∀ {Δ} {Σ : TyStore Δ} n
  → ⟨ Δ , Σ , [] ⟩ ⊢ wrapped-constant n ⦂ `∀ (‵ `ℕ)
wrapped-constant-⊢ n = ⊢reveal (⊢↑-∀ ⊢↑-id) (constant-polymorphic-⊢ n)

constant-return : ∀ {Δ} (Σ : TyStore Δ) R n
  → interpretFrom Σ 2 (constant-polymorphic n ⦂∀ (‵ `ℕ) [ R ])
      ≡ returned (E.result (suc Δ) (bind R ∷ keep ∷ []) ($ (κℕ n))
        ((constant-polymorphic n ⦂∀ (‵ `ℕ) [ R ])
          —→[ bind R ]⟨ β-Λ ($ (κℕ n)) ⟩
          ($ (κℕ n) ↑ id↑ (‵ `ℕ))
          —→[ keep ]⟨ pure-step (id-reveal ($ (κℕ n))) ⟩
          $ (κℕ n) ∎[]) ($ (κℕ n)))
constant-return Σ R n = refl

wrapped-constant-return : ∀ {Δ} (Σ : TyStore Δ) R n
  → interpretFrom Σ 5 (wrapped-constant n ⦂∀ (‵ `ℕ) [ R ])
      ≡ returned (E.result (suc (suc Δ))
        (bind R ∷ bind (＇ Fin.zero) ∷ keep ∷ keep ∷ keep ∷ []) ($ (κℕ n))
        ((wrapped-constant n ⦂∀ (‵ `ℕ) [ R ])
          —→[ bind R ]⟨ β-reveal-∀ (Λ ($ (κℕ n))) ⟩
          ((constant-polymorphic n ⦂∀ (‵ `ℕ) [ ＇ Fin.zero ])
            ↑ id↑ (‵ `ℕ)) ↑ id↑ (‵ `ℕ)
          —→[ bind (＇ Fin.zero) ]⟨
            ξ-reveal (ξ-reveal (β-Λ ($ (κℕ n))) refl) refl ⟩
          (($ (κℕ n) ↑ id↑ (‵ `ℕ)) ↑ id↑ (‵ `ℕ)) ↑ id↑ (‵ `ℕ)
          —→[ keep ]⟨ ξ-reveal
            (ξ-reveal (pure-step (id-reveal ($ (κℕ n)))) refl) refl ⟩
          ($ (κℕ n) ↑ id↑ (‵ `ℕ)) ↑ id↑ (‵ `ℕ)
          —→[ keep ]⟨ ξ-reveal (pure-step (id-reveal ($ (κℕ n)))) refl ⟩
          $ (κℕ n) ↑ id↑ (‵ `ℕ)
          —→[ keep ]⟨ pure-step (id-reveal ($ (κℕ n))) ⟩
          $ (κℕ n) ∎[]) ($ (κℕ n)))
wrapped-constant-return Σ R n = refl

lift-constant-polymorphic : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    (p : ScopeFuture S T) n
  → liftTerm p (constant-polymorphic n) ≡ constant-polymorphic n
lift-constant-polymorphic stay n = refl
lift-constant-polymorphic (grow p) n = lift-constant-polymorphic p n

lift-wrapped-constant : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    (p : ScopeFuture S T) n
  → liftTerm p (wrapped-constant n) ≡ wrapped-constant n
lift-wrapped-constant stay n = refl
lift-wrapped-constant (grow p) n = lift-wrapped-constant p n

module ConstantFamilies {Δᴵ₀ Δᴾ₀} (Σᴵ₀ : TyStore Δᴵ₀)
    (Σᴾ₀ : TyStore Δᴾ₀) where

  module B = Model Σᴵ₀ Σᴾ₀
  module U = Universals Σᴵ₀ Σᴾ₀

  result-type : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀} (S : PhysicalScope Σ₀ Δ) R
    → ‵ `ℕ ≡ scopeBody S (‵ `ℕ) [ R ]ᵗ
  result-type S R rewrite scope-body-natural S = refl

  paired : U.PairedFamily (‵ `ℕ) (‵ `ℕ)
  paired = record
    { Argument = λ { {Δᴵ} {Δᴾ} S T → Ty Δᴵ × Ty Δᴾ }
    ; argumentᴵ = proj₁
    ; argumentᴾ = proj₂
    ; result = λ { {S = S} {T} a → Model.natural (scopeStore S) (scopeStore T) }
    ; resultᴵ = λ { {S = S} a → result-type S (proj₁ a) }
    ; resultᴾ = λ { {T = T} a → result-type T (proj₂ a) }
    }

  right : U.RightFamily (‵ `ℕ) (‵ `ℕ)
  right = record
    { Argument = λ { {Δᴾ = Δᴾ} S T → Ty Δᴾ }
    ; argumentᴾ = λ R → R
    ; result = λ { {S = S} {T} R → Model.natural (scopeStore S) (scopeStore T) }
    ; resultᴵ = λ { {S = S} R → sym (scope-natural S) }
    ; resultᴾ = λ { {T = T} R → result-type T R }
    }

  paired-related : ∀ n k → B.related (U.universal paired) root root k
    (constant-polymorphic n) (wrapped-constant n)
  paired-related n k = U.universal-values
    (Λ ($ (κℕ n))) ((Λ ($ (κℕ n))) ↑ all)
    (constant-polymorphic-⊢ n) (wrapped-constant-⊢ n) call
    where
    call : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
        {T : PhysicalScope Σᴾ₀ Δᴾ} {j}
      → (p : ScopeFuture root S) → (q : ScopeFuture root T)
      → j < k → (a : Ty Δᴵ × Ty Δᴾ)
      → Model.ObservedComputations (scopeStore S) (scopeStore T)
          (Model.natural (scopeStore S) (scopeStore T)) root root j
          (liftTerm p (constant-polymorphic n)
            ⦂∀ scopeBody S (‵ `ℕ) [ proj₁ a ])
          (liftTerm q (wrapped-constant n) ⦂∀ scopeBody T (‵ `ℕ) [ proj₂ a ])
    call {S = S} {T} p q j<k (Rᴵ , Rᴾ)
        rewrite lift-constant-polymorphic p n | lift-wrapped-constant q n
          | scope-body-natural S | scope-body-natural T =
      Model.observed-from-returns (scopeStore S) (scopeStore T)
        {gasᴵ = 2} {gasᴾ = 5} (constant-return (scopeStore S) Rᴵ n)
        (wrapped-constant-return (scopeStore T) Rᴾ n) (same-natural n)

  right-related : ∀ n k → B.related (U.rightUniversal right) root root k
    ($ (κℕ n)) (wrapped-constant n)
  right-related n k = U.right-universal-values
    ($ (κℕ n)) ((Λ ($ (κℕ n))) ↑ all) (⊢$ (κℕ n)) (wrapped-constant-⊢ n) call
    where
    call : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
        {T : PhysicalScope Σᴾ₀ Δᴾ} {j}
      → (p : ScopeFuture root S) → (q : ScopeFuture root T)
      → j ≤ k → (R : Ty Δᴾ)
      → Model.ObservedComputations (scopeStore S) (scopeStore T)
          (Model.natural (scopeStore S) (scopeStore T)) root root j
          (liftTerm p ($ (κℕ n)))
          (liftTerm q (wrapped-constant n) ⦂∀ scopeBody T (‵ `ℕ) [ R ])
    call {S = S} {T} p q j≤k R
        rewrite lift-constant p (κℕ n) | lift-wrapped-constant q n
          | scope-body-natural T =
      Model.observed-from-returns (scopeStore S) (scopeStore T)
        {gasᴵ = 0} {gasᴾ = 5}
        (value-return-exact {Σ = scopeStore S} 0 ($ (κℕ n)))
        (wrapped-constant-return (scopeStore T) R n) (same-natural n)

-- A fully applied data check of the occurring-binder example.

identity-natural-call : ∀ {Δ} → ℕ → Term Δ
identity-natural-call n =
  (polymorphic-identity ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ‵ `ℕ ]) · $ (κℕ n)

identity-natural-call-⊢ : ∀ {Δ} {Σ : TyStore Δ} n
  → ⟨ Δ , Σ , [] ⟩ ⊢ identity-natural-call n ⦂ ‵ `ℕ
identity-natural-call-⊢ n = ⊢· (⊢• polymorphic-identity-⊢) (⊢$ (κℕ n))

identity-natural-call-return : ∀ {Δ} (Σ : TyStore Δ) n
  → interpretFrom Σ 4 (identity-natural-call n)
      ≡ returned (E.result (suc Δ) (bind (‵ `ℕ) ∷ keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ n))
        (identity-natural-call n
          —→[ bind (‵ `ℕ) ]⟨ ξ-·₁ (β-Λ (ƛ (` 0))) refl ⟩
          ((ƛ (` 0)) ↑ (seal Fin.zero (‵ `ℕ) ↦↑ unseal Fin.zero (‵ `ℕ)))
            · $ (κℕ n)
          —→[ keep ]⟨ pure-step (β-reveal-⇒ (ƛ (` 0)) ($ (κℕ n))) ⟩
          ((ƛ (` 0)) · ($ (κℕ n) ↓ seal Fin.zero (‵ `ℕ)))
            ↑ unseal Fin.zero (‵ `ℕ)
          —→[ keep ]⟨ ξ-reveal (pure-step (β ($ (κℕ n) ↓ seal))) refl ⟩
          ($ (κℕ n) ↓ seal Fin.zero (‵ `ℕ)) ↑ unseal Fin.zero (‵ `ℕ)
          —→[ keep ]⟨ pure-step (conceal-reveal ($ (κℕ n))) ⟩
          $ (κℕ n) ∎[]) ($ (κℕ n)))
identity-natural-call-return Σ n = refl

-- A nonempty, infinite argument family: naturals and iterated higher-order
-- endofunctions. Exercise elimination of the constructed universal clause.

module Empty = Model store-empty store-empty

argument-tower : ℕ → Empty.ScopedType
argument-tower zero = Empty.natural
argument-tower (suc n) = Empty.arrow (argument-tower n) (argument-tower n)

module Tower = IdentityFamily store-empty store-empty (λ S T → ℕ)
  (λ { {S = S} {T} a → Rebase.rebase S T (argument-tower a) })

tower-instantiations : ∀ a k → Empty.ObservedComputations
  (Tower.U.PairedFamily.result Tower.family {S = root} {T = root} a)
  root root k
  (polymorphic-identity ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero)
    [ Empty.impreciseTy (argument-tower a) ])
  (polymorphic-identity ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero)
    [ Empty.preciseTy (argument-tower a) ])
tower-instantiations a k = Tower.U.UniversalValues.instantiate
  (Tower.related (suc k)) stay stay ≤-refl a

module Constants = ConstantFamilies store-empty store-empty

right-at-same-index : ∀ R n k → Empty.ObservedComputations Empty.natural
  root root k ($ (κℕ n)) (wrapped-constant n ⦂∀ (‵ `ℕ) [ R ])
right-at-same-index R n k = Constants.U.RightUniversalValues.instantiate
  (Constants.right-related n k) stay stay ≤-refl R
