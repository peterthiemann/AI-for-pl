module proof.LR-narrow.NominalObservationExamples where

-- File Charter:
--   * Negative controls for representation-only nominal correspondence.
--   * Two names with equal representations remain dynamically distinguishable,
--     including when the differing package is hidden in a function result.
--   * Gives typing and data/blame observations, not an imprecision derivation
--     for the deliberately distinguishable pairs. Uses the unchanged evaluator.
--   * Checks that a pending seal/unseal observation is a computation, not a
--     value, even though it immediately returns the expected natural payload.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Empty using (⊥)
open import Data.Product using (∃-syntax; _,_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Types
open import TyStore
open import Primitives using (κℕ)
open import CastTerms
open import Conversion
open import Reduction
import Consistency as C
import Eval as E
open import Interpreter
open import proof.DGG.CtxImp using (resolveVar)

private
  X Y : TyVar 2
  X = Fin.suc Fin.zero
  Y = Fin.zero

  tags projections : C.Env∼ 2
  tags _ = C.X∼★
  projections _ = C.★∼X

  inject : ∀ Z → tags C.⊢ ＇ Z ∼ ★
  inject Z = C.id (＇ Z) C.!

  project : ∀ Z → projections C.⊢ ★ ∼ ＇ Z
  project Z = C.？ (C.idᵍ (＇ Z))

two-names : TyStore 2
two-names = store-bind (store-bind store-empty (‵ `ℕ)) (‵ `ℕ)

natural-entry : ∀ Z → two-names ∋ Z ⦂ ‵ `ℕ
natural-entry Fin.zero = Z∋ refl
natural-entry (Fin.suc Fin.zero) = S-bind∋ (Z∋ refl) refl

same-representation : resolveVar two-names X ≡ resolveVar two-names Y
same-representation = refl

distinct-tags : _≢_ {A = Ty 2} (＇ X) (＇ Y)
distinct-tags ()

package : TyVar 2 → ℕ → Term 2
package Z n = ($ (κℕ n) ↓ seal Z (‵ `ℕ)) ⟨ inject Z ⟩

package-⊢ : ∀ Z n (Γ : List (Ty 2))
  → ⟨ 2 , two-names , Γ ⟩ ⊢ package Z n ⦂ ★
package-⊢ Z n Γ =
  ⊢⟨⟩ (⊢conceal (⊢↓-seal (natural-entry Z)) (⊢$ (κℕ n))) (inject Z)

package-value : ∀ Z n → Value (package Z n)
package-value Z n = (($ (κℕ n)) ↓ seal) 《 inj 》

inspect : TyVar 2 → TyVar 2 → ℕ → Term 2
inspect Z W n = package Z n ⟨ project W ⟩ ↑ unseal W (‵ `ℕ)

inspect-⊢ : ∀ Z W n → ⟨ 2 , two-names , [] ⟩ ⊢ inspect Z W n ⦂ ‵ `ℕ
inspect-⊢ Z W n = ⊢reveal (⊢↑-unseal (natural-entry W))
  (⊢⟨⟩ (package-⊢ Z n []) (project W))

matching-↠ : ∀ Z n → inspect Z Z n —↠[ keep ∷ keep ∷ [] ] $ (κℕ n)
matching-↠ Z n =
    inspect Z Z n
  —→[ keep ]⟨ ξ-reveal (pure-step (tag-untag (($ (κℕ n)) ↓ seal)))
      refl ⟩
    ($ (κℕ n) ↓ seal Z (‵ `ℕ)) ↑ unseal Z (‵ `ℕ)
  —→[ keep ]⟨ pure-step (conceal-reveal ($ (κℕ n))) ⟩
    $ (κℕ n) ∎[]

matching-eval : ∀ Z n → interpretFrom two-names 2 (inspect Z Z n)
  ≡ returned (E.result 2 (keep ∷ keep ∷ []) ($ (κℕ n))
      (matching-↠ Z n) ($ (κℕ n)))
matching-eval Fin.zero n = refl
matching-eval (Fin.suc Fin.zero) n = refl

mismatching-↠ : ∀ n → inspect X Y n —↠[ keep ∷ keep ∷ [] ] blame
mismatching-↠ n =
    inspect X Y n
  —→[ keep ]⟨ ξ-reveal
      (pure-step (tag-untag-bad (($ (κℕ n)) ↓ seal) distinct-tags)) refl ⟩
    blame ↑ unseal Y (‵ `ℕ)
  —→[ keep ]⟨ pure-step blame-reveal ⟩
    blame ∎[]

mismatching-eval : ∀ n → interpretFrom two-names 2 (inspect X Y n)
  ≡ blamed (keep ∷ keep ∷ []) (mismatching-↠ n)
mismatching-eval n = refl

producer : TyVar 2 → ℕ → Term 2
producer Z n = ƛ (package Z n)

producer-⊢ : ∀ Z n → ⟨ 2 , two-names , [] ⟩
  ⊢ producer Z n ⦂ (‵ `ℕ ⇒ ★)
producer-⊢ Z n = ⊢ƛ (package-⊢ Z n (‵ `ℕ ∷ []))

producer-value : ∀ Z n → Value (producer Z n)
producer-value Z n = ƛ (package Z n)

call-and-inspect : TyVar 2 → TyVar 2 → ℕ → Term 2
call-and-inspect Z W n =
  (producer Z n · $ (κℕ 0)) ⟨ project W ⟩ ↑ unseal W (‵ `ℕ)

call-and-inspect-⊢ : ∀ Z W n → ⟨ 2 , two-names , [] ⟩
  ⊢ call-and-inspect Z W n ⦂ ‵ `ℕ
call-and-inspect-⊢ Z W n = ⊢reveal (⊢↑-unseal (natural-entry W))
  (⊢⟨⟩ (⊢· (producer-⊢ Z n) (⊢$ (κℕ 0))) (project W))

matching-call-↠ : ∀ Z n
  → call-and-inspect Z Z n —↠[ keep ∷ keep ∷ keep ∷ [] ] $ (κℕ n)
matching-call-↠ Z n =
    call-and-inspect Z Z n
  —→[ keep ]⟨ ξ-reveal (ξ-⟨⟩ (pure-step (β ($ (κℕ 0)))) refl) refl ⟩
    inspect Z Z n
  —↠[ keep ∷ keep ∷ [] ]⟨ matching-↠ Z n ⟩
    $ (κℕ n) ∎[]

matching-call-eval : ∀ Z n
  → interpretFrom two-names 3 (call-and-inspect Z Z n)
    ≡ returned (E.result 2 (keep ∷ keep ∷ keep ∷ []) ($ (κℕ n))
        (matching-call-↠ Z n) ($ (κℕ n)))
matching-call-eval Fin.zero n = refl
matching-call-eval (Fin.suc Fin.zero) n = refl

mismatching-call-↠ : ∀ n
  → call-and-inspect X Y n —↠[ keep ∷ keep ∷ keep ∷ [] ] blame
mismatching-call-↠ n =
    call-and-inspect X Y n
  —→[ keep ]⟨ ξ-reveal (ξ-⟨⟩ (pure-step (β ($ (κℕ 0)))) refl) refl ⟩
    inspect X Y n
  —↠[ keep ∷ keep ∷ [] ]⟨ mismatching-↠ n ⟩
    blame ∎[]

mismatching-call-eval : ∀ n
  → interpretFrom two-names 3 (call-and-inspect X Y n)
    ≡ blamed (keep ∷ keep ∷ keep ∷ []) (mismatching-call-↠ n)
mismatching-call-eval n = refl

-- A representation-only matching rule predicts success for the bad query.
-- Refute that precise rule, rather than calling this a CTI counterexample.

representation-only-projection-impossible :
  (∀ Z W n → resolveVar two-names Z ≡ resolveVar two-names W
    → ∃[ out ] interpretFrom two-names 2 (inspect Z W n) ≡ returned out)
  → ⊥
representation-only-projection-impossible rule with rule X Y 7 refl
representation-only-projection-impossible rule | out , ()

representation-only-call-impossible :
  (∀ Z W n → resolveVar two-names Z ≡ resolveVar two-names W
    → ∃[ out ] interpretFrom two-names 3 (call-and-inspect Z W n)
        ≡ returned out)
  → ⊥
representation-only-call-impossible rule with rule X Y 7 refl
representation-only-call-impossible rule | out , ()

pending : ℕ → Term 2
pending n = ($ (κℕ n) ↓ seal Y (‵ `ℕ)) ↑ unseal Y (‵ `ℕ)

pending-⊢ : ∀ n → ⟨ 2 , two-names , [] ⟩ ⊢ pending n ⦂ ‵ `ℕ
pending-⊢ n = ⊢reveal (⊢↑-unseal (natural-entry Y))
  (⊢conceal (⊢↓-seal (natural-entry Y)) (⊢$ (κℕ n)))

pending-↠ : ∀ n → pending n —↠[ keep ∷ [] ] $ (κℕ n)
pending-↠ n =
    pending n
  —→[ keep ]⟨ pure-step (conceal-reveal ($ (κℕ n))) ⟩
    $ (κℕ n) ∎[]

pending-eval : ∀ n → interpretFrom two-names 1 (pending n)
  ≡ returned (E.result 2 (keep ∷ []) ($ (κℕ n))
      (pending-↠ n) ($ (κℕ n)))
pending-eval n = refl

pending-not-value : ∀ n → Value (pending n) → ⊥
pending-not-value n (v ↑ ())
