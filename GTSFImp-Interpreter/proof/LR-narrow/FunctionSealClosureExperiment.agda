module proof.LR-narrow.FunctionSealClosureExperiment where

-- File Charter:
--   * Exercises general function-reveal compatibility with non-identity bodies.
--   * Both bodies return new constant closures; one allocates a private name
--     which remains in the closure's argument conversion after it escapes.
--   * Proves their behavior on arbitrary value arguments and checks complete
--     natural observations with the interpreter. No live LR is changed.

open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import TermCtx using (Z; S)
open import Primitives using (κℕ)
open import CastTerms
open import Conversion
open import Reduction
import Eval as E
open import Interpreter
open import proof.Reduction using (appL-↠)
open import proof.LR-narrow.PrivateSealBehavior using (_—↠[_]⟨_⟩+_)
open import proof.LR-narrow.FunctionSealCompatibility

-- X represents naturals; Y represents functions on naturals.

initial : TyStore 2
initial = store-bind (store-bind store-empty (‵ `ℕ)) (‵ `ℕ ⇒ ‵ `ℕ)

physical : TyStore 3
physical = store-bind initial (‵ `ℕ)

-- In named notation these bodies are
--   λn:X. (λx:ℕ. n ↑ unseal X ℕ) ↓ seal Y (ℕ⇒ℕ)
--   λn:X. ((Λα. λx:α. n ↑ unseal X ℕ)[ℕ]) ↓ seal Y (ℕ⇒ℕ).
-- The second one allocates Z during its application, not before it.

make-bare : Term 2
make-bare = ƛ ((ƛ ((` 1) ↑ unseal (Fin.suc Fin.zero) (‵ `ℕ)))
  ↓ seal Fin.zero (‵ `ℕ ⇒ ‵ `ℕ))

make-private : Term 2
make-private = ƛ (((Λ (ƛ ((` 1)
  ↑ unseal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ))))
    ⦂∀ (＇ Fin.zero ⇒ ‵ `ℕ) [ ‵ `ℕ ])
  ↓ seal Fin.zero (‵ `ℕ ⇒ ‵ `ℕ))

make-bare-value : Value make-bare
make-bare-value = ƛ _

make-private-value : Value make-private
make-private-value = ƛ _

make-bare-⊢ : ⟨ 2 , initial , [] ⟩
  ⊢ make-bare ⦂ (＇ (Fin.suc Fin.zero) ⇒ ＇ Fin.zero)
make-bare-⊢ = ⊢ƛ (⊢conceal (⊢↓-seal (Z∋ refl))
  (⊢ƛ (⊢reveal (⊢↑-unseal (S-bind∋ (Z∋ refl) refl)) (⊢` (S Z)))))

make-private-⊢ : ⟨ 2 , initial , [] ⟩
  ⊢ make-private ⦂ (＇ (Fin.suc Fin.zero) ⇒ ＇ Fin.zero)
make-private-⊢ = ⊢ƛ (⊢conceal (⊢↓-seal (Z∋ refl))
  (⊢• (⊢Λ (ƛ _) (⊢ƛ (⊢reveal
    (⊢↑-unseal (S-lift∋ (S-bind∋ (Z∋ refl) refl) refl)) (⊢` (S Z)))))))

fresh-bare : ℕ → Term 2
fresh-bare n = ƛ (($ (κℕ n) ↓ seal (Fin.suc Fin.zero) (‵ `ℕ))
  ↑ unseal (Fin.suc Fin.zero) (‵ `ℕ))

fresh-private : ℕ → Term 3
fresh-private n = (ƛ (($ (κℕ n)
  ↓ seal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ))
    ↑ unseal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ)))
  ↑ (seal Fin.zero (‵ `ℕ) ↦↑ id↑ (‵ `ℕ))

fresh-bare-value : ∀ n → Value (fresh-bare n)
fresh-bare-value n = ƛ _

fresh-private-value : ∀ n → Value (fresh-private n)
fresh-private-value n = (ƛ _) ↑ fun

fresh-bare-⊢ : ∀ n → ⟨ 2 , initial , [] ⟩
  ⊢ fresh-bare n ⦂ (‵ `ℕ ⇒ ‵ `ℕ)
fresh-bare-⊢ n = ⊢ƛ (⊢reveal (⊢↑-unseal (S-bind∋ (Z∋ refl) refl))
  (⊢conceal (⊢↓-seal (S-bind∋ (Z∋ refl) refl)) (⊢$ (κℕ n))))

fresh-private-⊢ : ∀ n → ⟨ 3 , physical , [] ⟩
  ⊢ fresh-private n ⦂ (‵ `ℕ ⇒ ‵ `ℕ)
fresh-private-⊢ n = ⊢reveal (⊢↑-⇒ (⊢↓-seal (Z∋ refl)) ⊢↑-id)
  (⊢ƛ (⊢reveal (⊢↑-unseal (S-bind∋ (S-bind∋ (Z∋ refl) refl) refl))
    (⊢conceal (⊢↓-seal (S-bind∋ (S-bind∋ (Z∋ refl) refl) refl))
      (⊢$ (κℕ n)))))

make-bare-↠ : ∀ n
  → make-bare · ($ (κℕ n) ↓ seal (Fin.suc Fin.zero) (‵ `ℕ))
      —↠[ keep ∷ [] ] fresh-bare n ↓ seal Fin.zero (‵ `ℕ ⇒ ‵ `ℕ)
make-bare-↠ n =
    make-bare · ($ (κℕ n) ↓ seal (Fin.suc Fin.zero) (‵ `ℕ))
  —→[ keep ]⟨ pure-step (β ($ (κℕ n) ↓ seal)) ⟩
    fresh-bare n ↓ seal Fin.zero (‵ `ℕ ⇒ ‵ `ℕ) ∎[]

make-private-↠ : ∀ n
  → make-private · ($ (κℕ n) ↓ seal (Fin.suc Fin.zero) (‵ `ℕ))
      —↠[ keep ∷ bind (‵ `ℕ) ∷ [] ]
      fresh-private n ↓ seal (Fin.suc Fin.zero) (‵ `ℕ ⇒ ‵ `ℕ)
make-private-↠ n =
    make-private · ($ (κℕ n) ↓ seal (Fin.suc Fin.zero) (‵ `ℕ))
  —→[ keep ]⟨ pure-step (β ($ (κℕ n) ↓ seal)) ⟩
    ((Λ (ƛ (($ (κℕ n) ↓ seal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ))
      ↑ unseal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ))))
      ⦂∀ (＇ Fin.zero ⇒ ‵ `ℕ) [ ‵ `ℕ ])
      ↓ seal Fin.zero (‵ `ℕ ⇒ ‵ `ℕ)
  —→[ bind (‵ `ℕ) ]⟨ ξ-conceal (β-Λ (ƛ _)) refl ⟩
    fresh-private n ↓ seal (Fin.suc Fin.zero) (‵ `ℕ ⇒ ‵ `ℕ) ∎[]

public-bare : Term 2
public-bare = reveal-function (Fin.suc Fin.zero) (‵ `ℕ)
  Fin.zero (‵ `ℕ ⇒ ‵ `ℕ) make-bare

public-private : Term 2
public-private = reveal-function (Fin.suc Fin.zero) (‵ `ℕ)
  Fin.zero (‵ `ℕ ⇒ ‵ `ℕ) make-private

public-bare-⊢ : ⟨ 2 , initial , [] ⟩
  ⊢ public-bare ⦂ (‵ `ℕ ⇒ (‵ `ℕ ⇒ ‵ `ℕ))
public-bare-⊢ = reveal-function-typed (S-bind∋ (Z∋ refl) refl)
  (Z∋ refl) make-bare-⊢

public-private-⊢ : ⟨ 2 , initial , [] ⟩
  ⊢ public-private ⦂ (‵ `ℕ ⇒ (‵ `ℕ ⇒ ‵ `ℕ))
public-private-⊢ = reveal-function-typed (S-bind∋ (Z∋ refl) refl)
  (Z∋ refl) make-private-⊢

-- Use the typed theorem, including its canonical-form argument, to derive
-- these public traces from the arbitrary bodies' sealed return traces.

public-bare-↠ : ∀ n → public-bare · $ (κℕ n)
  —↠[ keep ∷ keep ∷ keep ∷ [] ] fresh-bare n
public-bare-↠ n with typed-reveal-function-return
  (S-bind∋ (Z∋ refl) refl) (Z∋ refl) make-bare-value ($ (κℕ n))
  make-bare-⊢ (⊢$ (κℕ n)) (make-bare-↠ n) (fresh-bare-value n ↓ seal)
public-bare-↠ n | .(fresh-bare n) , vU , typed , refl , trace = trace

public-private-↠ : ∀ n → public-private · $ (κℕ n)
  —↠[ keep ∷ keep ∷ bind (‵ `ℕ) ∷ keep ∷ [] ] fresh-private n
public-private-↠ n with typed-reveal-function-return
  (S-bind∋ (Z∋ refl) refl) (Z∋ refl) make-private-value ($ (κℕ n))
  make-private-⊢ (⊢$ (κℕ n)) (make-private-↠ n)
  (fresh-private-value n ↓ seal)
public-private-↠ n | .(fresh-private n) , vU , typed , refl , trace = trace

-- These are constant functions, not identity adapters: they return the
-- captured n for EVERY value argument, independently at the two endpoints.

fresh-bare-↠ : ∀ n {W} → Value W
  → fresh-bare n · W —↠[ keep ∷ keep ∷ [] ] $ (κℕ n)
fresh-bare-↠ n {W} vW =
    fresh-bare n · W
  —→[ keep ]⟨ pure-step (β vW) ⟩
    ($ (κℕ n) ↓ seal (Fin.suc Fin.zero) (‵ `ℕ))
      ↑ unseal (Fin.suc Fin.zero) (‵ `ℕ)
  —→[ keep ]⟨ pure-step (conceal-reveal ($ (κℕ n))) ⟩
    $ (κℕ n) ∎[]

fresh-private-↠ : ∀ n {W} → Value W
  → fresh-private n · W
      —↠[ keep ∷ keep ∷ keep ∷ keep ∷ [] ] $ (κℕ n)
fresh-private-↠ n {W} vW =
    fresh-private n · W
  —→[ keep ]⟨ pure-step (β-reveal-⇒ (ƛ _) vW) ⟩
    ((ƛ (($ (κℕ n) ↓ seal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ))
      ↑ unseal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ)))
      · (W ↓ seal Fin.zero (‵ `ℕ))) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ ξ-reveal (pure-step (β (vW ↓ seal))) refl ⟩
    (($ (κℕ n) ↓ seal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ))
      ↑ unseal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ)) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ ξ-reveal (pure-step (conceal-reveal ($ (κℕ n)))) refl ⟩
    $ (κℕ n) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ pure-step (id-reveal ($ (κℕ n))) ⟩
    $ (κℕ n) ∎[]

-- The pair theorem consumes a PROVED relation on fresh body results.
-- Its behavioral component quantifies over independent arguments, so it
-- cannot be discharged merely by returning the original input unchanged.

related-public-results : ∀ n → ∃[ Uᴵ ] ∃[ Uᴾ ]
    (public-bare · $ (κℕ n)
      —↠[ keep ∷ keep ∷ keep ∷ [] ] Uᴵ)
    × (public-private · $ (κℕ n)
      —↠[ keep ∷ keep ∷ bind (‵ `ℕ) ∷ keep ∷ [] ] Uᴾ)
    × (∀ {Wᴵ Wᴾ} → Value Wᴵ → Value Wᴾ
        → (Uᴵ · Wᴵ —↠[ keep ∷ keep ∷ [] ] $ (κℕ n))
          × (Uᴾ · Wᴾ —↠[ keep ∷ keep ∷ keep ∷ keep ∷ [] ] $ (κℕ n)))
related-public-results n = related-function-reveals-return
  (Fin.suc Fin.zero) (‵ `ℕ) Fin.zero (‵ `ℕ ⇒ ‵ `ℕ)
  (Fin.suc Fin.zero) (‵ `ℕ) Fin.zero (‵ `ℕ ⇒ ‵ `ℕ)
  make-bare-value ($ (κℕ n)) make-private-value ($ (κℕ n))
  (make-bare-↠ n) (make-private-↠ n)
  (λ Uᴵ Uᴾ → ∀ {Wᴵ Wᴾ} → Value Wᴵ → Value Wᴾ
    → (Uᴵ · Wᴵ —↠[ keep ∷ keep ∷ [] ] $ (κℕ n))
      × (Uᴾ · Wᴾ —↠[ keep ∷ keep ∷ keep ∷ keep ∷ [] ] $ (κℕ n)))
  (related-seals (fresh-bare-value n) (fresh-private-value n)
    (λ vWᴵ vWᴾ → fresh-bare-↠ n vWᴵ , fresh-private-↠ n vWᴾ))

observe-bare : ℕ → ℕ → Term 2
observe-bare n m = (public-bare · $ (κℕ n)) · $ (κℕ m)

observe-private : ℕ → ℕ → Term 2
observe-private n m = (public-private · $ (κℕ n)) · $ (κℕ m)

observe-bare-⊢ : ∀ n m → ⟨ 2 , initial , [] ⟩
  ⊢ observe-bare n m ⦂ ‵ `ℕ
observe-bare-⊢ n m = ⊢· (⊢· public-bare-⊢ (⊢$ (κℕ n))) (⊢$ (κℕ m))

observe-private-⊢ : ∀ n m → ⟨ 2 , initial , [] ⟩
  ⊢ observe-private n m ⦂ ‵ `ℕ
observe-private-⊢ n m =
  ⊢· (⊢· public-private-⊢ (⊢$ (κℕ n))) (⊢$ (κℕ m))

observe-bare-↠ : ∀ n m → observe-bare n m
  —↠[ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ] $ (κℕ n)
observe-bare-↠ n m =
    observe-bare n m
  —↠[ keep ∷ keep ∷ keep ∷ [] ]⟨ appL-↠ (public-bare-↠ n) ⟩+
    fresh-bare n · $ (κℕ m)
  —↠[ keep ∷ keep ∷ [] ]⟨ fresh-bare-↠ n ($ (κℕ m)) ⟩
    $ (κℕ n) ∎[]

observe-private-↠ : ∀ n m → observe-private n m
  —↠[ keep ∷ keep ∷ bind (‵ `ℕ) ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ]
    $ (κℕ n)
observe-private-↠ n m =
    observe-private n m
  —↠[ keep ∷ keep ∷ bind (‵ `ℕ) ∷ keep ∷ [] ]⟨
      appL-↠ (public-private-↠ n) ⟩+
    fresh-private n · $ (κℕ m)
  —↠[ keep ∷ keep ∷ keep ∷ keep ∷ [] ]⟨ fresh-private-↠ n ($ (κℕ m)) ⟩
    $ (κℕ n) ∎[]

-- Independent evaluator checks, with exact fuel and final physical stores.
-- Setting n = 7 and m = 9 observes 7, not the closure's argument 9.

observe-bare-eval : ∀ n m → ∃[ changes ]
  ∃ λ (trace : observe-bare n m —↠[ changes ] $ (κℕ n)) →
  (interpretFrom initial 5 (observe-bare n m)
    ≡ returned (E.result 2 changes ($ (κℕ n)) trace ($ (κℕ n))))
  × (changes ▶ˢ initial ≡ initial)
observe-bare-eval n m = _ , _ , refl , refl

observe-private-eval : ∀ n m → ∃[ changes ]
  ∃ λ (trace : observe-private n m —↠[ changes ] $ (κℕ n)) →
  (interpretFrom initial 8 (observe-private n m)
    ≡ returned (E.result 3 changes ($ (κℕ n)) trace ($ (κℕ n))))
  × (changes ▶ˢ initial ≡ physical)
observe-private-eval n m = _ , _ , refl , refl
