module proof.LR-narrow.ScopedTypeEquivalence where

-- File Charter:
--   * Equivalence witnesses between scoped semantic types without record
--     equality or function extensionality.
--   * Transports observed computations through pointwise relation conversion.
--   * Records the rebase/natural and rebase/arrow equivalences used by scoped
--     body interpretation.

open import Data.List using ([])
open import Data.Nat using (ℕ; _∸_; _<_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
import Eval as E
open import Interpreter
open import LR-narrow.Computation using (BlamesFrom)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopeRebase as ScopeRebase
open import proof.LR-narrow.ScopedBehavior

module Equivalence {Δᴵ Δᴾ} (Σᴵ : TyStore Δᴵ) (Σᴾ : TyStore Δᴾ) where

  open Model Σᴵ Σᴾ

  record Equivalent (A B : ScopedType) : Set₁ where
    field
      imprecise-type : impreciseTy A ≡ impreciseTy B
      precise-type : preciseTy A ≡ preciseTy B
      to : ∀ {Δᴵ′ Δᴾ′}
          {S : PhysicalScope Σᴵ Δᴵ′} {T : PhysicalScope Σᴾ Δᴾ′}
          {k U V}
        → related A S T k U V → related B S T k U V
      from : ∀ {Δᴵ′ Δᴾ′}
          {S : PhysicalScope Σᴵ Δᴵ′} {T : PhysicalScope Σᴾ Δᴾ′}
          {k U V}
        → related B S T k U V → related A S T k U V

  open Equivalent public

  eq-refl : ∀ {A} → Equivalent A A
  eq-refl = record
    { imprecise-type = refl
    ; precise-type = refl
    ; to = λ r → r
    ; from = λ r → r
    }

  eq-sym : ∀ {A B} → Equivalent A B → Equivalent B A
  eq-sym eq = record
    { imprecise-type = sym (imprecise-type eq)
    ; precise-type = sym (precise-type eq)
    ; to = from eq
    ; from = to eq
    }

  eq-trans : ∀ {A B C} → Equivalent A B → Equivalent B C → Equivalent A C
  eq-trans left right = record
    { imprecise-type = trans (imprecise-type left) (imprecise-type right)
    ; precise-type = trans (precise-type left) (precise-type right)
    ; to = λ r → to right (to left r)
    ; from = λ r → from left (from right r)
    }

  observed-to : ∀ {Δᴵ′ Δᴾ′} {A B : ScopedType}
      {S : PhysicalScope Σᴵ Δᴵ′} {T : PhysicalScope Σᴾ Δᴾ′} {k M N}
    → Equivalent A B
    → ObservedComputations A S T k M N
    → ObservedComputations B S T k M N
  observed-to {B = B} {S} {T} {k} {M} {N} eq c = record
    { forward-return = forward
    ; backward-return = backward
    ; forward-blame = ObservedComputations.forward-blame c
    }
    where
    forward : ∀ {n} {outᴵ : E.EvalResult M}
      → n < k → interpretFrom (scopeStore S) n M ≡ returned outᴵ
      → (∃[ m ] ∃[ outᴾ ]
          (interpretFrom (scopeStore T) m N ≡ returned outᴾ)
          × related B (advance S (E.changes outᴵ))
              (advance T (E.changes outᴾ)) (k ∸ n)
              (E.term outᴵ) (E.term outᴾ))
        ⊎ (∃[ m ] BlamesFrom (scopeStore T) m N)
    forward n<k ret with ObservedComputations.forward-return c n<k ret
    forward n<k ret | inj₁ (m , outᴾ , retᴾ , r) =
      inj₁ (m , outᴾ , retᴾ , to eq r)
    forward n<k ret | inj₂ blameᴾ = inj₂ blameᴾ

    backward : ∀ {n} {outᴾ : E.EvalResult N}
      → n < k → interpretFrom (scopeStore T) n N ≡ returned outᴾ
      → ∃[ m ] ∃[ outᴵ ]
          (interpretFrom (scopeStore S) m M ≡ returned outᴵ)
          × related B (advance S (E.changes outᴵ))
              (advance T (E.changes outᴾ)) (k ∸ n)
              (E.term outᴵ) (E.term outᴾ)
    backward n<k ret with ObservedComputations.backward-return c n<k ret
    backward n<k ret | m , outᴵ , retᴵ , r =
      m , outᴵ , retᴵ , to eq r

  arrow-cong : ∀ {A A′ B B′}
    → Equivalent A A′ → Equivalent B B′
    → Equivalent (arrow A B) (arrow A′ B′)
  arrow-cong {A} {A′} {B} {B′} eqA eqB = record
    { imprecise-type =
        cong₂ _⇒_ (imprecise-type eqA) (imprecise-type eqB)
    ; precise-type =
        cong₂ _⇒_ (precise-type eqA) (precise-type eqB)
    ; to = to-arrow
    ; from = from-arrow
    }
    where
    to-arrow : ∀ {Δᴵ′ Δᴾ′}
        {S : PhysicalScope Σᴵ Δᴵ′} {T : PhysicalScope Σᴾ Δᴾ′}
        {k U V}
      → related (arrow A B) S T k U V
      → related (arrow A′ B′) S T k U V
    to-arrow {S = S} {T = T} r = arrow-values
      (ArrowValues.functionᴵ-value r)
      (ArrowValues.functionᴾ-value r)
      (subst≡ (λ A → ⟨ _ , _ , [] ⟩ ⊢ _ ⦂ A)
        (cong (scopeTy S) (cong₂ _⇒_
          (imprecise-type eqA) (imprecise-type eqB)))
        (ArrowValues.functionᴵ-typed r))
      (subst≡ (λ A → ⟨ _ , _ , [] ⟩ ⊢ _ ⦂ A)
        (cong (scopeTy T) (cong₂ _⇒_
          (precise-type eqA) (precise-type eqB)))
        (ArrowValues.functionᴾ-typed r))
      (λ p q j<k args →
        observed-to eqB (ArrowValues.call r p q j<k (from eqA args)))

    from-arrow : ∀ {Δᴵ′ Δᴾ′}
        {S : PhysicalScope Σᴵ Δᴵ′} {T : PhysicalScope Σᴾ Δᴾ′}
        {k U V}
      → related (arrow A′ B′) S T k U V
      → related (arrow A B) S T k U V
    from-arrow {S = S} {T = T} r = arrow-values
      (ArrowValues.functionᴵ-value r)
      (ArrowValues.functionᴾ-value r)
      (subst≡ (λ A → ⟨ _ , _ , [] ⟩ ⊢ _ ⦂ A)
        (sym (cong (scopeTy S) (cong₂ _⇒_
          (imprecise-type eqA) (imprecise-type eqB))))
        (ArrowValues.functionᴵ-typed r))
      (subst≡ (λ A → ⟨ _ , _ , [] ⟩ ⊢ _ ⦂ A)
        (sym (cong (scopeTy T) (cong₂ _⇒_
          (precise-type eqA) (precise-type eqB))))
        (ArrowValues.functionᴾ-typed r))
      (λ p q j<k args →
        observed-to (eq-sym eqB)
          (ArrowValues.call r p q j<k (to eqA args)))

module RebaseEquivalence {Δᴵ₀ Δᴾ₀ Δᴵ Δᴾ}
    {Σᴵ₀ : TyStore Δᴵ₀} {Σᴾ₀ : TyStore Δᴾ₀}
    (S : PhysicalScope Σᴵ₀ Δᴵ) (T : PhysicalScope Σᴾ₀ Δᴾ) where

  module R = ScopeRebase.Rebase S T
  module Old = Model Σᴵ₀ Σᴾ₀
  module New = Model (scopeStore S) (scopeStore T)
  module Eq = Equivalence (scopeStore S) (scopeStore T)

  natural : Eq.Equivalent (R.rebase Old.natural) New.natural
  natural = record
    { imprecise-type = scope-natural S
    ; precise-type = scope-natural T
    ; to = λ r → r
    ; from = λ r → r
    }

  arrow : (A B : Old.ScopedType)
    → Eq.Equivalent (R.rebase (Old.arrow A B))
        (New.arrow (R.rebase A) (R.rebase B))
  arrow A B = record
    { imprecise-type = scope-arrow S (Old.impreciseTy A) (Old.impreciseTy B)
    ; precise-type = scope-arrow T (Old.preciseTy A) (Old.preciseTy B)
    ; to = R.arrow-to A B
    ; from = R.arrow-from A B
    }
