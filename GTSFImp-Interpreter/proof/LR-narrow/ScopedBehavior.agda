module proof.LR-narrow.ScopedBehavior where

-- File Charter:
--   * Proof-local semantic types over two independently growing physical
--     scopes, with fixed physical roots. Results need not lower to the roots.
--   * The computation observation has the DGG's three directions. Natural,
--     arrow, and nominal-seal types have proved index/future closure.
--   * The closure fields are semantic-type invariants, proved by each type
--     constructor, not assumed function-reveal compatibility obligations.
--   * ScopedUniversal supplies family-indexed universal constructors;
--     dynamic types remain absent. ScopeRebase and VisibleEnvironment
--     provide root changes and visible-name extension.

open import Data.List using ([])
open import Data.Nat using (ℕ; _≤_; _<_; _∸_)
open import Data.Nat.Properties using (≤-trans; ∸-monoˡ-≤; m∸n≤m)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong) renaming (subst to subst≡; subst₂ to subst₂≡)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import Primitives using (κℕ)
import Eval as E
open import Interpreter
open import LR-narrow.Computation using (BlamesFrom)
open import LR-narrow.LogicalRelation using (SameBaseValue; same-natural)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.FunctionSealCompatibility using
  (SealedValues; related-seals)
open import proof.LR-narrow.Application using
  (eval-from-return; eval-from-blame)
open import proof.LR-narrow.TargetEvaluation using
  (return-result-unique; eval-terminal-unique)

module Model {Δᴵ₀ Δᴾ₀} (Σᴵ₀ : TyStore Δᴵ₀) (Σᴾ₀ : TyStore Δᴾ₀) where

  record ScopedType : Set₁ where
    field
      impreciseTy : Ty Δᴵ₀
      preciseTy : Ty Δᴾ₀
      related : ∀ {Δᴵ Δᴾ}
        → PhysicalScope Σᴵ₀ Δᴵ → PhysicalScope Σᴾ₀ Δᴾ
        → ℕ → Term Δᴵ → Term Δᴾ → Set
      imprecise-value : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
          {T : PhysicalScope Σᴾ₀ Δᴾ} {k U V}
        → related S T k U V → Value U
      precise-value : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
          {T : PhysicalScope Σᴾ₀ Δᴾ} {k U V}
        → related S T k U V → Value V
      imprecise-typed : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
          {T : PhysicalScope Σᴾ₀ Δᴾ} {k U V}
        → related S T k U V
        → ⟨ Δᴵ , scopeStore S , [] ⟩ ⊢ U ⦂ scopeTy S impreciseTy
      precise-typed : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
          {T : PhysicalScope Σᴾ₀ Δᴾ} {k U V}
        → related S T k U V
        → ⟨ Δᴾ , scopeStore T , [] ⟩ ⊢ V ⦂ scopeTy T preciseTy
      downward : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
          {T : PhysicalScope Σᴾ₀ Δᴾ} {j k U V}
        → j ≤ k → related S T k U V → related S T j U V
      future-closed : ∀ {Δᴵ Δᴾ Δᴵ′ Δᴾ′}
          {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ}
          {S′ : PhysicalScope Σᴵ₀ Δᴵ′} {T′ : PhysicalScope Σᴾ₀ Δᴾ′}
          {k U V}
        → (p : ScopeFuture S S′) → (q : ScopeFuture T T′)
        → related S T k U V
        → related S′ T′ k (liftTerm p U) (liftTerm q V)

  open ScopedType public

  -- A return is interpreted in its actual physical result scopes. Their
  -- stores and caller actions are justified by advance-store/advance-term.
  -- No existential raw-store join and no syntax-lowering premise occur.

  record ObservedComputations {Δᴵ Δᴾ} (B : ScopedType)
      (S : PhysicalScope Σᴵ₀ Δᴵ) (T : PhysicalScope Σᴾ₀ Δᴾ)
      (k : ℕ) (M : Term Δᴵ) (N : Term Δᴾ) : Set where
    field
      forward-return : ∀ {n} {outᴵ : E.EvalResult M}
        → n < k → interpretFrom (scopeStore S) n M ≡ returned outᴵ
        → (∃[ m ] ∃[ outᴾ ]
            (interpretFrom (scopeStore T) m N ≡ returned outᴾ)
            × related B (advance S (E.changes outᴵ))
                (advance T (E.changes outᴾ)) (k ∸ n)
                (E.term outᴵ) (E.term outᴾ))
          ⊎ (∃[ m ] BlamesFrom (scopeStore T) m N)
      backward-return : ∀ {n} {outᴾ : E.EvalResult N}
        → n < k → interpretFrom (scopeStore T) n N ≡ returned outᴾ
        → ∃[ m ] ∃[ outᴵ ]
            (interpretFrom (scopeStore S) m M ≡ returned outᴵ)
            × related B (advance S (E.changes outᴵ))
                (advance T (E.changes outᴾ)) (k ∸ n)
                (E.term outᴵ) (E.term outᴾ)
      forward-blame : ∀ {n}
        → n < k → BlamesFrom (scopeStore S) n M
        → ∃[ m ] BlamesFrom (scopeStore T) m N

  observed-downward : ∀ {Δᴵ Δᴾ} {B : ScopedType}
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {j k M N}
    → j ≤ k → ObservedComputations B S T k M N
    → ObservedComputations B S T j M N
  observed-downward {B = B} {S} {T} {j} {M = M} {N} j≤k c = record
    { forward-return = forward
    ; backward-return = backward
    ; forward-blame = λ n<j →
        ObservedComputations.forward-blame c (≤-trans n<j j≤k)
    }
    where
    forward : ∀ {n} {outᴵ : E.EvalResult M}
      → n < j → interpretFrom (scopeStore S) n M ≡ returned outᴵ
      → (∃[ m ] ∃[ outᴾ ]
          (interpretFrom (scopeStore T) m N ≡ returned outᴾ)
          × related B (advance S (E.changes outᴵ))
              (advance T (E.changes outᴾ)) (j ∸ n)
              (E.term outᴵ) (E.term outᴾ))
        ⊎ (∃[ m ] BlamesFrom (scopeStore T) m N)
    forward {n} n<j ret
        with ObservedComputations.forward-return c (≤-trans n<j j≤k) ret
    forward {n} n<j ret | inj₁ (m , out , returnedN , r) =
      inj₁ (m , out , returnedN , downward B (∸-monoˡ-≤ n j≤k) r)
    forward n<j ret | inj₂ blames = inj₂ blames

    backward : ∀ {n} {outᴾ : E.EvalResult N}
      → n < j → interpretFrom (scopeStore T) n N ≡ returned outᴾ
      → ∃[ m ] ∃[ outᴵ ]
          (interpretFrom (scopeStore S) m M ≡ returned outᴵ)
          × related B (advance S (E.changes outᴵ))
              (advance T (E.changes outᴾ)) (j ∸ n)
              (E.term outᴵ) (E.term outᴾ)
    backward {n} n<j ret
        with ObservedComputations.backward-return c (≤-trans n<j j≤k) ret
    backward {n} n<j ret | m , out , returnedM , r =
      m , out , returnedM , downward B (∸-monoˡ-≤ n j≤k) r

  -- This is the Kripke closure of the operational observation, not an
  -- assumption that evaluation itself commutes with arbitrary allocations.
  ScopedComputations : ∀ {Δᴵ Δᴾ} (B : ScopedType)
    → PhysicalScope Σᴵ₀ Δᴵ → PhysicalScope Σᴾ₀ Δᴾ
    → ℕ → Term Δᴵ → Term Δᴾ → Set
  ScopedComputations B S T k M N = ∀ {Δᴵ′ Δᴾ′}
      {S′ : PhysicalScope Σᴵ₀ Δᴵ′} {T′ : PhysicalScope Σᴾ₀ Δᴾ′}
    → (p : ScopeFuture S S′) → (q : ScopeFuture T T′)
    → ObservedComputations B S′ T′ k (liftTerm p M) (liftTerm q N)

  computations-downward : ∀ {Δᴵ Δᴾ} {B : ScopedType}
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {j k M N}
    → j ≤ k → ScopedComputations B S T k M N
    → ScopedComputations B S T j M N
  computations-downward j≤k c p q = observed-downward j≤k (c p q)

  computations-future : ∀ {Δᴵ Δᴾ Δᴵ′ Δᴾ′} {B : ScopedType}
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ}
      {S′ : PhysicalScope Σᴵ₀ Δᴵ′} {T′ : PhysicalScope Σᴾ₀ Δᴾ′} {k M N}
    → (p : ScopeFuture S S′) → (q : ScopeFuture T T′)
    → ScopedComputations B S T k M N
    → ScopedComputations B S′ T′ k (liftTerm p M) (liftTerm q N)
  computations-future {B = B} {M = M} {N} p q c p′ q′ =
    subst₂≡ (ObservedComputations B _ _ _)
      (lift-term-comp p p′ M) (lift-term-comp q q′ N)
      (c (scope-trans p p′) (scope-trans q q′))

  natural : ScopedType
  natural = record
    { impreciseTy = ‵ `ℕ
    ; preciseTy = ‵ `ℕ
    ; related = λ S T k → SameBaseValue `ℕ
    ; imprecise-value = λ { (same-natural n) → $ (κℕ n) }
    ; precise-value = λ { (same-natural n) → $ (κℕ n) }
    ; imprecise-typed = λ { {S = S} (same-natural n) →
        subst≡ (λ A → ⟨ _ , scopeStore S , [] ⟩ ⊢ $ (κℕ n) ⦂ A)
          (sym (scope-natural S)) (⊢$ (κℕ n)) }
    ; precise-typed = λ { {T = T} (same-natural n) →
        subst≡ (λ A → ⟨ _ , scopeStore T , [] ⟩ ⊢ $ (κℕ n) ⦂ A)
          (sym (scope-natural T)) (⊢$ (κℕ n)) }
    ; downward = λ j≤k r → r
    ; future-closed = λ { p q (same-natural n) →
        subst₂≡ (SameBaseValue `ℕ)
          (sym (lift-constant p (κℕ n))) (sym (lift-constant q (κℕ n)))
          (same-natural n) }
    }

  record ArrowValues {Δᴵ Δᴾ} (A B : ScopedType)
      (S : PhysicalScope Σᴵ₀ Δᴵ) (T : PhysicalScope Σᴾ₀ Δᴾ)
      (k : ℕ) (F : Term Δᴵ) (G : Term Δᴾ) : Set where
    constructor arrow-values
    field
      functionᴵ-value : Value F
      functionᴾ-value : Value G
      functionᴵ-typed : ⟨ Δᴵ , scopeStore S , [] ⟩
        ⊢ F ⦂ scopeTy S (impreciseTy A ⇒ impreciseTy B)
      functionᴾ-typed : ⟨ Δᴾ , scopeStore T , [] ⟩
        ⊢ G ⦂ scopeTy T (preciseTy A ⇒ preciseTy B)
      call : ∀ {Δᴵ′ Δᴾ′} {S′ : PhysicalScope Σᴵ₀ Δᴵ′}
          {T′ : PhysicalScope Σᴾ₀ Δᴾ′} {j U V}
        → (p : ScopeFuture S S′) → (q : ScopeFuture T T′)
        → j < k → related A S′ T′ j U V
        → ObservedComputations B S′ T′ j (liftTerm p F · U) (liftTerm q G · V)

  arrow : ScopedType → ScopedType → ScopedType
  arrow A B = record
    { impreciseTy = impreciseTy A ⇒ impreciseTy B
    ; preciseTy = preciseTy A ⇒ preciseTy B
    ; related = ArrowValues A B
    ; imprecise-value = ArrowValues.functionᴵ-value
    ; precise-value = ArrowValues.functionᴾ-value
    ; imprecise-typed = ArrowValues.functionᴵ-typed
    ; precise-typed = ArrowValues.functionᴾ-typed
    ; downward = λ j≤k r → arrow-values
        (ArrowValues.functionᴵ-value r) (ArrowValues.functionᴾ-value r)
        (ArrowValues.functionᴵ-typed r) (ArrowValues.functionᴾ-typed r)
        (λ p q n<j args → ArrowValues.call r p q (≤-trans n<j j≤k) args)
    ; future-closed = λ { {U = F} {V = G} p q r → arrow-values
        (lift-value p (ArrowValues.functionᴵ-value r))
        (lift-value q (ArrowValues.functionᴾ-value r))
        (lift-root-typed p (ArrowValues.functionᴵ-typed r))
        (lift-root-typed q (ArrowValues.functionᴾ-typed r))
        (λ { {U = U} {V = V} p′ q′ n<k args →
          subst₂≡ (ObservedComputations B _ _ _)
            (cong (_· U) (lift-term-comp p p′ F))
            (cong (_· V) (lift-term-comp q q′ G))
            (ArrowValues.call r (scope-trans p p′) (scope-trans q q′)
              n<k args) }) }
    }

  nominal : (A : ScopedType) (X : TyVar Δᴵ₀) (Y : TyVar Δᴾ₀)
    → Σᴵ₀ ∋ X ⦂ impreciseTy A → Σᴾ₀ ∋ Y ⦂ preciseTy A → ScopedType
  nominal A X Y entryX entryY = record
    { impreciseTy = ＇ X
    ; preciseTy = ＇ Y
    ; related = λ S T k →
        SealedValues (scopeVar S X) (scopeTy S (impreciseTy A))
          (scopeVar T Y) (scopeTy T (preciseTy A)) (related A S T k)
    ; imprecise-value = λ { (related-seals vU vV r) → vU ↓ seal }
    ; precise-value = λ { (related-seals vU vV r) → vV ↓ seal }
    ; imprecise-typed = λ { {S = S} (related-seals {Uᴵ = U} vU vV r) →
        subst≡ (λ B → ⟨ _ , scopeStore S , [] ⟩
          ⊢ U ↓ seal (scopeVar S X) (scopeTy S (impreciseTy A)) ⦂ B)
          (sym (scope-variable S X))
          (⊢conceal (⊢↓-seal (scope-entry S entryX)) (imprecise-typed A r)) }
    ; precise-typed = λ { {T = T} (related-seals {Uᴾ = V} vU vV r) →
        subst≡ (λ B → ⟨ _ , scopeStore T , [] ⟩
          ⊢ V ↓ seal (scopeVar T Y) (scopeTy T (preciseTy A)) ⦂ B)
          (sym (scope-variable T Y))
          (⊢conceal (⊢↓-seal (scope-entry T entryY)) (precise-typed A r)) }
    ; downward = λ { j≤k (related-seals vU vV r) →
        related-seals vU vV (downward A j≤k r) }
    ; future-closed = λ { p q (related-seals {Uᴵ = U} {Uᴾ = V} vU vV r) →
        subst₂≡ (SealedValues _ _ _ _ (related A _ _ _))
          (sym (lift-root-seal p X (impreciseTy A) U))
          (sym (lift-root-seal q Y (preciseTy A) V))
          (related-seals (lift-value p vU) (lift-value q vV)
            (future-closed A p q r)) }
    }

  -- Known returns provide a useful introduction rule. Determinism with
  -- respect to fuel proves ALL bounded observations, including no left blame.
  observed-from-returns : ∀ {Δᴵ Δᴾ} {B : ScopedType}
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ}
      {k M N gasᴵ gasᴾ} {outᴵ : E.EvalResult M} {outᴾ : E.EvalResult N}
    → interpretFrom (scopeStore S) gasᴵ M ≡ returned outᴵ
    → interpretFrom (scopeStore T) gasᴾ N ≡ returned outᴾ
    → related B (advance S (E.changes outᴵ)) (advance T (E.changes outᴾ))
        k (E.term outᴵ) (E.term outᴾ)
    → ObservedComputations B S T k M N
  observed-from-returns {B = B} {S} {T} {k} {M} {N} {gasᴵ} {gasᴾ}
      {outᴵ} {outᴾ} returnᴵ returnᴾ r = record
    { forward-return = forward
    ; backward-return = backward
    ; forward-blame = no-blame
    }
    where
    forward : ∀ {n} {out : E.EvalResult M}
      → n < k → interpretFrom (scopeStore S) n M ≡ returned out
      → (∃[ m ] ∃[ out′ ]
          (interpretFrom (scopeStore T) m N ≡ returned out′)
          × related B (advance S (E.changes out)) (advance T (E.changes out′))
              (k ∸ n) (E.term out) (E.term out′))
        ⊎ (∃[ m ] BlamesFrom (scopeStore T) m N)
    forward {n} n<k ret with return-result-unique {Σ = scopeStore S}
      {leftGas = n} {rightGas = gasᴵ} ret returnᴵ
    forward {n} n<k ret | refl =
      inj₁ (gasᴾ , outᴾ , returnᴾ , downward B (m∸n≤m k n) r)

    backward : ∀ {n} {out : E.EvalResult N}
      → n < k → interpretFrom (scopeStore T) n N ≡ returned out
      → ∃[ m ] ∃[ out′ ]
          (interpretFrom (scopeStore S) m M ≡ returned out′)
          × related B (advance S (E.changes out′)) (advance T (E.changes out))
              (k ∸ n) (E.term out′) (E.term out)
    backward {n} n<k ret with return-result-unique {Σ = scopeStore T}
      {leftGas = n} {rightGas = gasᴾ} ret returnᴾ
    backward {n} n<k ret | refl =
      gasᴵ , outᴵ , returnᴵ , downward B (m∸n≤m k n) r

    no-blame : ∀ {n} → n < k → BlamesFrom (scopeStore S) n M
      → ∃[ m ] BlamesFrom (scopeStore T) m N
    no-blame {n} n<k (Δ′ , χs , trace , blamedM)
        with eval-terminal-unique {Σ = scopeStore S}
          {leftGas = gasᴵ} {rightGas = n}
          (eval-from-return {Σ = scopeStore S} {gas = gasᴵ} returnᴵ)
          (eval-from-blame {Σ = scopeStore S} {gas = n} blamedM)
    no-blame n<k (Δ′ , χs , trace , blamedM) | ()

  observed-from-right-blame : ∀ {Δᴵ Δᴾ} {B : ScopedType}
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {k M N gas}
    → BlamesFrom (scopeStore T) gas N → ObservedComputations B S T k M N
  observed-from-right-blame {B = B} {S} {T} {k} {M} {N} {gas}
      blameN@(Δ′ , χs , trace , blamedN) = record
    { forward-return = λ n<k ret → inj₂ (gas , blameN)
    ; backward-return = no-return
    ; forward-blame = λ n<k blameM → gas , blameN
    }
    where
    no-return : ∀ {n} {out : E.EvalResult N}
      → n < k → interpretFrom (scopeStore T) n N ≡ returned out
      → ∃[ m ] ∃[ out′ ] (interpretFrom (scopeStore S) m M ≡ returned out′)
          × related B (advance S (E.changes out′)) (advance T (E.changes out))
              (k ∸ n) (E.term out′) (E.term out)
    no-return {n} n<k ret
        with eval-terminal-unique {Σ = scopeStore T}
          {leftGas = n} {rightGas = gas}
          (eval-from-return {Σ = scopeStore T} {gas = n} ret)
          (eval-from-blame {Σ = scopeStore T} {gas = gas} blamedN)
    no-return n<k ret | ()
