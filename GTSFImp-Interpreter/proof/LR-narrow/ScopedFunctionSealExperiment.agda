module proof.LR-narrow.ScopedFunctionSealExperiment where

-- File Charter:
--   * Instantiates general arrow compatibility with constant and blaming
--     abstract functions at every index and every independent future.
--   * Checks data returns, permitted precise blame, and forward blame.
--   * The allocating higher-order instance remains in ScopedBehaviorExperiment.

open import Data.List using ([])
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import Primitives using (κℕ)
open import Reduction
import Eval as E
open import Interpreter
open import LR-narrow.Computation using (BlamesFrom)
open import LR-narrow.LogicalRelation using (same-natural)
open import proof.TypeInTermSubst using (toRename-wk-eq)
open import proof.LR-narrow.FunctionSealCompatibility using
  (reveal-function; related-seals)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedFunctionSeal

initial : TyStore 1
initial = store-bind store-empty (‵ `ℕ)

module B = Model initial initial
module K = Compatibility initial initial

constant-abstract : ∀ {Δ} → TyVar Δ → ℕ → Term Δ
constant-abstract X n = ƛ ($ (κℕ n) ↓ seal X (‵ `ℕ))

constant-abstract-typed : ∀ {Δ} {Σ : TyStore Δ} {X} n
  → Σ ∋ X ⦂ ‵ `ℕ
  → ⟨ Δ , Σ , [] ⟩ ⊢ constant-abstract X n ⦂ (＇ X ⇒ ＇ X)
constant-abstract-typed n entry =
  ⊢ƛ (⊢conceal (⊢↓-seal entry) (⊢$ (κℕ n)))

constant-call : ∀ {Δ} (Σ : TyStore Δ) X n m
  → ∃ λ (trace : constant-abstract X n · ($ (κℕ m) ↓ seal X (‵ `ℕ))
      —↠[ keep ∷ [] ] $ (κℕ n) ↓ seal X (‵ `ℕ)) →
      interpretFrom Σ 1
        (constant-abstract X n · ($ (κℕ m) ↓ seal X (‵ `ℕ)))
        ≡ returned (E.result Δ (keep ∷ [])
          ($ (κℕ n) ↓ seal X (‵ `ℕ)) trace ($ (κℕ n) ↓ seal))
constant-call Σ X n m = _ , refl

constant-future : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    (p : ScopeFuture S T) X n
  → liftTerm p (constant-abstract X n) ≡ constant-abstract (liftVar p X) n
constant-future stay X n = refl
constant-future (grow p) X n rewrite toRename-wk-eq X =
  constant-future p (Fin.suc X) n

sealed-naturals-related : ∀ {Δᴵ Δᴾ} (S : PhysicalScope initial Δᴵ)
    (T : PhysicalScope initial Δᴾ) n {k}
  → B.related (B.nominal B.natural Fin.zero Fin.zero (Z∋ refl) (Z∋ refl))
      S T k ($ (κℕ n) ↓ seal (scopeVar S Fin.zero) (‵ `ℕ))
        ($ (κℕ n) ↓ seal (scopeVar T Fin.zero) (‵ `ℕ))
sealed-naturals-related S T n rewrite scope-natural S | scope-natural T =
  related-seals ($ (κℕ n)) ($ (κℕ n)) (same-natural n)

constant-abstract-related : ∀ n k
  → B.related (B.arrow
      (B.nominal B.natural Fin.zero Fin.zero (Z∋ refl) (Z∋ refl))
      (B.nominal B.natural Fin.zero Fin.zero (Z∋ refl) (Z∋ refl)))
      root root k (constant-abstract Fin.zero n) (constant-abstract Fin.zero n)
constant-abstract-related n k = B.arrow-values (ƛ _) (ƛ _)
  (constant-abstract-typed n (Z∋ refl))
  (constant-abstract-typed n (Z∋ refl)) call
  where
  call : ∀ {Δᴵ Δᴾ} {S : PhysicalScope initial Δᴵ}
      {T : PhysicalScope initial Δᴾ} {j U V}
    → (p : ScopeFuture root S) → (q : ScopeFuture root T)
    → j Data.Nat.< k
    → B.related (B.nominal B.natural Fin.zero Fin.zero (Z∋ refl) (Z∋ refl))
        S T j U V
    → B.ObservedComputations
        (B.nominal B.natural Fin.zero Fin.zero (Z∋ refl) (Z∋ refl)) S T j
        (liftTerm p (constant-abstract Fin.zero n) · U)
        (liftTerm q (constant-abstract Fin.zero n) · V)
  call {S = S} {T} p q j<k (related-seals vU vV (same-natural m))
      rewrite constant-future p Fin.zero n | constant-future q Fin.zero n
        | lift-root-variable p Fin.zero | lift-root-variable q Fin.zero
        | scope-natural S | scope-natural T
      with constant-call (scopeStore S) (scopeVar S Fin.zero) n m
         | constant-call (scopeStore T) (scopeVar T Fin.zero) n m
  call {S = S} {T} {j} p q j<k (related-seals vU vV (same-natural m))
      | traceᴵ , retᴵ | traceᴾ , retᴾ =
    B.observed-from-returns {S = S} {T = T} {gasᴵ = 1} {gasᴾ = 1}
      retᴵ retᴾ (sealed-naturals-related S T n {k = j})

constant-public : ℕ → Term 1
constant-public n = reveal-function Fin.zero (‵ `ℕ) Fin.zero (‵ `ℕ)
  (constant-abstract Fin.zero n)

constant-public-related : ∀ n k
  → B.related (B.arrow B.natural B.natural) root root k
      (constant-public n) (constant-public n)
constant-public-related n k = K.function-seals-related B.natural B.natural
  Fin.zero Fin.zero Fin.zero Fin.zero (Z∋ refl) (Z∋ refl) (Z∋ refl) (Z∋ refl)
  (constant-abstract-related n k)

constant-public-typed : ∀ n
  → ⟨ 1 , initial , [] ⟩ ⊢ constant-public n ⦂ (‵ `ℕ ⇒ ‵ `ℕ)
constant-public-typed n = B.imprecise-typed (B.arrow B.natural B.natural)
  (constant-public-related n 0)

constant-public-trace : ∀ n m → constant-public n · $ (κℕ m)
  —↠[ keep ∷ keep ∷ keep ∷ [] ] $ (κℕ n)
constant-public-trace n m =
    constant-public n · $ (κℕ m)
  —→[ keep ]⟨ pure-step (β-reveal-⇒ (ƛ _) ($ (κℕ m))) ⟩
    (constant-abstract Fin.zero n · ($ (κℕ m) ↓ seal Fin.zero (‵ `ℕ)))
      ↑ unseal Fin.zero (‵ `ℕ)
  —→[ keep ]⟨ ξ-reveal (pure-step (β ($ (κℕ m) ↓ seal))) refl ⟩
    ($ (κℕ n) ↓ seal Fin.zero (‵ `ℕ)) ↑ unseal Fin.zero (‵ `ℕ)
  —→[ keep ]⟨ pure-step (conceal-reveal ($ (κℕ n))) ⟩
    $ (κℕ n) ∎[]

constant-public-return : ∀ n m
  → interpretFrom initial 3 (constant-public n · $ (κℕ m)) ≡ returned
      (E.result 1 (keep ∷ keep ∷ keep ∷ []) ($ (κℕ n))
        (constant-public-trace n m) ($ (κℕ n)))
constant-public-return n m = refl

-- The precise body can instead blame. This exercises both the permitted
-- precise-blame alternative and, when both bodies blame, forward blame.

blaming-future : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
    {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
    (p : ScopeFuture S T)
  → liftTerm p (ƛ blame) ≡ ƛ blame
blaming-future stay = refl
blaming-future (grow p) = blaming-future p

blaming-call : ∀ {Δ} (Σ : TyStore Δ) X A m
  → BlamesFrom Σ 1 ((ƛ blame) · ($ (κℕ m) ↓ seal X A))
blaming-call {Δ} Σ X A m = Δ , keep ∷ [] ,
  (((ƛ blame) · ($ (κℕ m) ↓ seal X A))
    —→[ keep ]⟨ pure-step (β ($ (κℕ m) ↓ seal)) ⟩ blame ∎[]) , refl

right-blaming-abstract-related : ∀ {F : Term 1} k
  → Value F → ⟨ 1 , initial , [] ⟩ ⊢ F ⦂ (＇ Fin.zero ⇒ ＇ Fin.zero)
  → B.related (B.arrow
      (B.nominal B.natural Fin.zero Fin.zero (Z∋ refl) (Z∋ refl))
      (B.nominal B.natural Fin.zero Fin.zero (Z∋ refl) (Z∋ refl)))
      root root k F (ƛ blame)
right-blaming-abstract-related {F} k vF typedF =
  B.arrow-values vF (ƛ blame) typedF (⊢ƛ ⊢blame) call
  where
  call : ∀ {Δᴵ Δᴾ} {S : PhysicalScope initial Δᴵ}
      {T : PhysicalScope initial Δᴾ} {j U V}
    → (p : ScopeFuture root S) → (q : ScopeFuture root T)
    → j Data.Nat.< k
    → B.related (B.nominal B.natural Fin.zero Fin.zero (Z∋ refl) (Z∋ refl))
        S T j U V
    → B.ObservedComputations
        (B.nominal B.natural Fin.zero Fin.zero (Z∋ refl) (Z∋ refl)) S T j
        (liftTerm p F · U) (liftTerm q (ƛ blame) · V)
  call {S = S} {T} p q j<k (related-seals vU vV (same-natural m))
      rewrite blaming-future q =
    B.observed-from-right-blame {S = S} {T = T} {gas = 1}
      (blaming-call (scopeStore T) (scopeVar T Fin.zero) (scopeTy T (‵ `ℕ)) m)

blaming-public : Term 1
blaming-public = reveal-function Fin.zero (‵ `ℕ) Fin.zero (‵ `ℕ) (ƛ blame)

right-blaming-public-related : ∀ n k
  → B.related (B.arrow B.natural B.natural) root root k
      (constant-public n) blaming-public
right-blaming-public-related n k = K.function-seals-related
  B.natural B.natural Fin.zero Fin.zero Fin.zero Fin.zero
  (Z∋ refl) (Z∋ refl) (Z∋ refl) (Z∋ refl)
  (right-blaming-abstract-related k (ƛ _) (constant-abstract-typed n (Z∋ refl)))

blaming-public-related : ∀ k
  → B.related (B.arrow B.natural B.natural) root root k
      blaming-public blaming-public
blaming-public-related k = K.function-seals-related
  B.natural B.natural Fin.zero Fin.zero Fin.zero Fin.zero
  (Z∋ refl) (Z∋ refl) (Z∋ refl) (Z∋ refl)
  (right-blaming-abstract-related k (ƛ blame) (⊢ƛ ⊢blame))

blaming-public-typed : ⟨ 1 , initial , [] ⟩
  ⊢ blaming-public ⦂ (‵ `ℕ ⇒ ‵ `ℕ)
blaming-public-typed = B.imprecise-typed (B.arrow B.natural B.natural)
  (blaming-public-related 0)

blaming-public-blames : ∀ m → BlamesFrom initial 3 (blaming-public · $ (κℕ m))
blaming-public-blames m = 1 , keep ∷ keep ∷ keep ∷ [] ,
  (blaming-public · $ (κℕ m)
    —→[ keep ]⟨ pure-step (β-reveal-⇒ (ƛ blame) ($ (κℕ m))) ⟩
      ((ƛ blame) · ($ (κℕ m) ↓ seal Fin.zero (‵ `ℕ)))
        ↑ unseal Fin.zero (‵ `ℕ)
    —→[ keep ]⟨ ξ-reveal (pure-step (β ($ (κℕ m) ↓ seal))) refl ⟩
      blame ↑ unseal Fin.zero (‵ `ℕ)
    —→[ keep ]⟨ pure-step blame-reveal ⟩ blame ∎[]) , refl

forward-blame-through-compatibility : ∀ m
  → ∃[ gas ] BlamesFrom initial gas (blaming-public · $ (κℕ m))
forward-blame-through-compatibility m = B.ObservedComputations.forward-blame
  (B.ArrowValues.call (blaming-public-related 5) stay stay ≤-refl
    (same-natural m)) ≤-refl (blaming-public-blames m)
