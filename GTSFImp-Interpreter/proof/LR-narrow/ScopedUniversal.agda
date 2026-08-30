module proof.LR-narrow.ScopedUniversal where

-- File Charter:
--   * Constructs paired and right-only universal semantic types from small
--     argument-indexed interpretations of their instantiated result types.
--   * Proves index and independent-future closure of both universal clauses.
--     Tests use actual type applications and retain every result allocation.
--   * Families contain semantic interpretations, not assumed compatibility
--     theorems. Deriving them from general type syntax remains separate.

open import Data.List using ([])
open import Data.Nat using (ℕ; suc; _<_; _≤_)
open import Data.Nat.Properties using (≤-trans)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong) renaming (subst₂ to subst₂≡)

open import Types
open import TyStore
open import CastTerms
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior

module Universals {Δᴵ₀ Δᴾ₀} (Σᴵ₀ : TyStore Δᴵ₀) (Σᴾ₀ : TyStore Δᴾ₀) where

  module B = Model Σᴵ₀ Σᴾ₀

  -- Argument codes and their evidence live in Set, e.g. syntactic type pairs
  -- with admissibility derivations. Quantifying over all ScopedType records
  -- instead would put the value relation in Set₁, outside this model.

  record PairedFamily (Cᴵ : Ty (suc Δᴵ₀)) (Cᴾ : Ty (suc Δᴾ₀)) : Set₁ where
    field
      Argument : ∀ {Δᴵ Δᴾ}
        → PhysicalScope Σᴵ₀ Δᴵ → PhysicalScope Σᴾ₀ Δᴾ → Set
      argumentᴵ : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
          {T : PhysicalScope Σᴾ₀ Δᴾ} → Argument S T → Ty Δᴵ
      argumentᴾ : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
          {T : PhysicalScope Σᴾ₀ Δᴾ} → Argument S T → Ty Δᴾ
      result : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
          {T : PhysicalScope Σᴾ₀ Δᴾ}
        → Argument S T → Model.ScopedType (scopeStore S) (scopeStore T)
      resultᴵ : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
          {T : PhysicalScope Σᴾ₀ Δᴾ} (a : Argument S T)
        → Model.impreciseTy (result a) ≡ scopeBody S Cᴵ [ argumentᴵ a ]ᵗ
      resultᴾ : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
          {T : PhysicalScope Σᴾ₀ Δᴾ} (a : Argument S T)
        → Model.preciseTy (result a) ≡ scopeBody T Cᴾ [ argumentᴾ a ]ᵗ

  record UniversalValues {Δᴵ Δᴾ} {Cᴵ Cᴾ} (F : PairedFamily Cᴵ Cᴾ)
      (S : PhysicalScope Σᴵ₀ Δᴵ) (T : PhysicalScope Σᴾ₀ Δᴾ)
      (k : ℕ) (U : Term Δᴵ) (V : Term Δᴾ) : Set where
    constructor universal-values
    open PairedFamily F
    field
      valueᴵ : Value U
      valueᴾ : Value V
      typedᴵ : ⟨ Δᴵ , scopeStore S , [] ⟩ ⊢ U ⦂ scopeTy S (`∀ Cᴵ)
      typedᴾ : ⟨ Δᴾ , scopeStore T , [] ⟩ ⊢ V ⦂ scopeTy T (`∀ Cᴾ)
      instantiate : ∀ {Δᴵ′ Δᴾ′} {S′ : PhysicalScope Σᴵ₀ Δᴵ′}
          {T′ : PhysicalScope Σᴾ₀ Δᴾ′} {j}
        → (p : ScopeFuture S S′) → (q : ScopeFuture T T′)
        → j < k → (a : Argument S′ T′)
        → Model.ObservedComputations (scopeStore S′) (scopeStore T′)
            (result a) root root j
            (liftTerm p U ⦂∀ scopeBody S′ Cᴵ [ argumentᴵ a ])
            (liftTerm q V ⦂∀ scopeBody T′ Cᴾ [ argumentᴾ a ])

  universal : ∀ {Cᴵ Cᴾ} → PairedFamily Cᴵ Cᴾ → B.ScopedType
  universal {Cᴵ} {Cᴾ} F = record
    { impreciseTy = `∀ Cᴵ
    ; preciseTy = `∀ Cᴾ
    ; related = UniversalValues F
    ; imprecise-value = UniversalValues.valueᴵ
    ; precise-value = UniversalValues.valueᴾ
    ; imprecise-typed = UniversalValues.typedᴵ
    ; precise-typed = UniversalValues.typedᴾ
    ; downward = λ j≤k r → universal-values
        (UniversalValues.valueᴵ r) (UniversalValues.valueᴾ r)
        (UniversalValues.typedᴵ r) (UniversalValues.typedᴾ r)
        (λ p q n<j a → UniversalValues.instantiate r p q (≤-trans n<j j≤k) a)
    ; future-closed = λ { {U = U} {V = V} p q r → universal-values
        (lift-value p (UniversalValues.valueᴵ r))
        (lift-value q (UniversalValues.valueᴾ r))
        (lift-root-typed p (UniversalValues.typedᴵ r))
        (lift-root-typed q (UniversalValues.typedᴾ r))
        (λ { {S′ = S′} {T′ = T′} p′ q′ n<k a →
          subst₂≡ (Model.ObservedComputations (scopeStore S′) (scopeStore T′)
              (PairedFamily.result F a) root root _)
            (cong (λ L → L ⦂∀ scopeBody S′ Cᴵ [ PairedFamily.argumentᴵ F a ])
              (lift-term-comp p p′ U))
            (cong (λ L → L ⦂∀ scopeBody T′ Cᴾ [ PairedFamily.argumentᴾ F a ])
              (lift-term-comp q q′ V))
            (UniversalValues.instantiate r (scope-trans p p′)
              (scope-trans q q′) n<k a) }) }
    }

  -- Right-only instantiation tests the unchanged imprecise value against
  -- a precise type application. Its admissible argument need not be ★.
  -- There is no imprecise step to pay for a contractive decrement: unlike
  -- the paired clause, this clause includes tests at the SAME index.

  record RightFamily (Cᴵ : Ty Δᴵ₀) (Cᴾ : Ty (suc Δᴾ₀)) : Set₁ where
    field
      Argument : ∀ {Δᴵ Δᴾ}
        → PhysicalScope Σᴵ₀ Δᴵ → PhysicalScope Σᴾ₀ Δᴾ → Set
      argumentᴾ : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
          {T : PhysicalScope Σᴾ₀ Δᴾ} → Argument S T → Ty Δᴾ
      result : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
          {T : PhysicalScope Σᴾ₀ Δᴾ}
        → Argument S T → Model.ScopedType (scopeStore S) (scopeStore T)
      resultᴵ : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
          {T : PhysicalScope Σᴾ₀ Δᴾ} (a : Argument S T)
        → Model.impreciseTy (result a) ≡ scopeTy S Cᴵ
      resultᴾ : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
          {T : PhysicalScope Σᴾ₀ Δᴾ} (a : Argument S T)
        → Model.preciseTy (result a) ≡ scopeBody T Cᴾ [ argumentᴾ a ]ᵗ

  record RightUniversalValues {Δᴵ Δᴾ} {Cᴵ Cᴾ} (F : RightFamily Cᴵ Cᴾ)
      (S : PhysicalScope Σᴵ₀ Δᴵ) (T : PhysicalScope Σᴾ₀ Δᴾ)
      (k : ℕ) (U : Term Δᴵ) (V : Term Δᴾ) : Set where
    constructor right-universal-values
    open RightFamily F
    field
      valueᴵ : Value U
      valueᴾ : Value V
      typedᴵ : ⟨ Δᴵ , scopeStore S , [] ⟩ ⊢ U ⦂ scopeTy S Cᴵ
      typedᴾ : ⟨ Δᴾ , scopeStore T , [] ⟩ ⊢ V ⦂ scopeTy T (`∀ Cᴾ)
      instantiate : ∀ {Δᴵ′ Δᴾ′} {S′ : PhysicalScope Σᴵ₀ Δᴵ′}
          {T′ : PhysicalScope Σᴾ₀ Δᴾ′} {j}
        → (p : ScopeFuture S S′) → (q : ScopeFuture T T′)
        → j ≤ k → (a : Argument S′ T′)
        → Model.ObservedComputations (scopeStore S′) (scopeStore T′)
            (result a) root root j (liftTerm p U)
            (liftTerm q V ⦂∀ scopeBody T′ Cᴾ [ argumentᴾ a ])

  rightUniversal : ∀ {Cᴵ Cᴾ} → RightFamily Cᴵ Cᴾ → B.ScopedType
  rightUniversal {Cᴵ} {Cᴾ} F = record
    { impreciseTy = Cᴵ
    ; preciseTy = `∀ Cᴾ
    ; related = RightUniversalValues F
    ; imprecise-value = RightUniversalValues.valueᴵ
    ; precise-value = RightUniversalValues.valueᴾ
    ; imprecise-typed = RightUniversalValues.typedᴵ
    ; precise-typed = RightUniversalValues.typedᴾ
    ; downward = λ j≤k r → right-universal-values
        (RightUniversalValues.valueᴵ r) (RightUniversalValues.valueᴾ r)
        (RightUniversalValues.typedᴵ r) (RightUniversalValues.typedᴾ r)
        (λ p q n≤j a →
          RightUniversalValues.instantiate r p q (≤-trans n≤j j≤k) a)
    ; future-closed = λ { {U = U} {V = V} p q r → right-universal-values
        (lift-value p (RightUniversalValues.valueᴵ r))
        (lift-value q (RightUniversalValues.valueᴾ r))
        (lift-root-typed p (RightUniversalValues.typedᴵ r))
        (lift-root-typed q (RightUniversalValues.typedᴾ r))
        (λ { {S′ = S′} {T′ = T′} p′ q′ n≤k a →
          subst₂≡ (Model.ObservedComputations (scopeStore S′) (scopeStore T′)
              (RightFamily.result F a) root root _)
            (lift-term-comp p p′ U)
            (cong (λ L → L ⦂∀ scopeBody T′ Cᴾ [ RightFamily.argumentᴾ F a ])
              (lift-term-comp q q′ V))
            (RightUniversalValues.instantiate r (scope-trans p p′)
              (scope-trans q q′) n≤k a) }) }
    }
