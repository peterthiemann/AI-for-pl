module proof.LR-narrow.ScopedStepExpansion where

-- File Charter:
--   * Expands scoped observations across one right-only target step.
--   * Handles both keep and allocating store changes by advancing the target
--     physical scope before reusing the continuation observation.
--   * Preserves the source computation, the outer step index, and the exact
--     target evaluator histories produced by the prepended step.

open import Data.List using (_∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc; _∸_; _<_)
open import Data.Nat.Properties using (n≤1+n; ∸-monoʳ-≤)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym)
  renaming (subst₂ to subst₂≡)

open import Types
open import TyStore
open import CastTerms
open import Reduction
import Eval as E
open import Interpreter
open import LR-narrow.Computation using (BlamesFrom)
open import proof.LR-narrow.Application using (prepend-result)
open import proof.LR-narrow.BindStepExpansion using
  (step-return-invert; step-return; step-return-expand;
   step-blame-expand)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior

step-scope : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
  → StoreChange Δ Δ′ → PhysicalScope Σ₀ Δ → PhysicalScope Σ₀ Δ′
step-scope keep T = T
step-scope (bind A) T = allocate T A

step-scope-advance : ∀ {Δ₀ Δ Δ′ Δ″} {Σ₀ : TyStore Δ₀}
    (T : PhysicalScope Σ₀ Δ) (χ : StoreChange Δ Δ′)
    (χs : StoreChanges Δ′ Δ″)
  → advance T (χ ∷ χs) ≡ advance (step-scope χ T) χs
step-scope-advance T keep χs = refl
step-scope-advance T (bind A) χs = refl

step-scope-store : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    (T : PhysicalScope Σ₀ Δ) (χ : StoreChange Δ Δ′)
  → scopeStore (step-scope χ T) ≡ applyStore χ (scopeStore T)
step-scope-store T keep = refl
step-scope-store T (bind A) = refl

observed-right-step : ∀ {Δᴵ₀ Δᴾ₀} {Σᴵ₀ : TyStore Δᴵ₀}
    {Σᴾ₀ : TyStore Δᴾ₀} {Δᴵ Δᴾ Δᴾ′}
    {B : Model.ScopedType Σᴵ₀ Σᴾ₀}
    {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ}
    {k : ℕ} {M : Term Δᴵ} {N : Term Δᴾ} {N′ : Term Δᴾ′}
    {χ : StoreChange Δᴾ Δᴾ′}
  → N ≢ blame
  → E.value? N ≡ nothing
  → (step : N —→[ χ ] N′)
  → E.step? (scopeStore T) N ≡ just (E.step-result χ N′ step)
  → Model.ObservedComputations Σᴵ₀ Σᴾ₀ B S (step-scope χ T) k M N′
  → Model.ObservedComputations Σᴵ₀ Σᴾ₀ B S T k M N
observed-right-step {B = B} {S} {T} {k} {M} {N} {N′} {χ}
    N≢blame value-eq step step-eq c = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = blames
  }
  where
  open Model _ _

  forward : ∀ {n} {outᴵ : E.EvalResult M}
    → n < k → interpretFrom (scopeStore S) n M ≡ returned outᴵ
    → (∃[ m ] ∃[ outᴾ ]
        (interpretFrom (scopeStore T) m N ≡ returned outᴾ)
        × related B (advance S (E.changes outᴵ))
            (advance T (E.changes outᴾ)) (k ∸ n)
            (E.term outᴵ) (E.term outᴾ))
      ⊎ (∃[ m ] BlamesFrom (scopeStore T) m N)
  forward {n} n<k ret with ObservedComputations.forward-return c n<k ret
  forward {n} {outᴵ} n<k ret | inj₁ (m , outᴾ , retᴾ , r) =
    inj₁ (suc m , prepend-result step outᴾ ,
      step-return-expand {Σ = scopeStore T} {gas = m}
        N≢blame value-eq step step-eq retᴾ ,
      subst₂≡ (λ S′ T′ → related B S′ T′ (k ∸ n)
          (E.term outᴵ) (E.term (prepend-result step outᴾ)))
        refl (sym (step-scope-advance T χ (E.changes outᴾ))) r)
  forward n<k ret | inj₂ (m , blameᴾ) =
    inj₂ (suc m , step-blame-expand {Σ = scopeStore T} {gas = m}
      N≢blame value-eq step step-eq blameᴾ)

  backward : ∀ {n} {outᴾ : E.EvalResult N}
    → n < k → interpretFrom (scopeStore T) n N ≡ returned outᴾ
    → ∃[ m ] ∃[ outᴵ ]
        (interpretFrom (scopeStore S) m M ≡ returned outᴵ)
        × related B (advance S (E.changes outᴵ))
            (advance T (E.changes outᴾ)) (k ∸ n)
            (E.term outᴵ) (E.term outᴾ)
  backward {n} n<k ret with step-return-invert {Σ = scopeStore T} {n = n}
    N≢blame value-eq step step-eq ret
  backward {n = suc gas} n<k ret
      | step-return outᴾ retᴾ refl
      with ObservedComputations.backward-return c
        (Data.Nat.Properties.≤-trans (Data.Nat.s≤s (n≤1+n gas)) n<k)
        retᴾ
  backward {n = suc gas} n<k ret
      | step-return outᴾ retᴾ refl | m , outᴵ , retᴵ , r =
    m , outᴵ , retᴵ ,
    subst₂≡ (λ S′ T′ → related B S′ T′ (k ∸ suc gas)
        (E.term outᴵ) (E.term (prepend-result step outᴾ)))
      refl (sym (step-scope-advance T χ (E.changes outᴾ)))
      (downward B (∸-monoʳ-≤ k (n≤1+n gas)) r)

  blames : ∀ {n}
    → n < k → BlamesFrom (scopeStore S) n M
    → ∃[ m ] BlamesFrom (scopeStore T) m N
  blames {n} n<k blameᴵ
      with ObservedComputations.forward-blame c n<k blameᴵ
  blames n<k blameᴵ | m , blameᴾ =
    suc m , step-blame-expand {Σ = scopeStore T} {gas = m}
      N≢blame value-eq step step-eq blameᴾ
