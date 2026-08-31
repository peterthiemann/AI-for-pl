module proof.LR-narrow.GeneralInstantiationExperiments where

-- File Charter:
--   * Concrete operational regressions for arbitrary-type instantiation
--     prefixes from GeneralInstantiationSteps.
--   * Covers bare and identity-universal-wrapped producer instantiations at
--     function, dynamic, and universal payloads, recovering each emitted packet
--     through matching nominal projection/unseal and eliminating to Nat data.
--   * Starts at the actual returned adapters and post-prefix stores; the
--     initial allocation prefixes are proved separately in the steps module.
--   * These are evaluator/typing tests only; no semantic relatedness or
--     arbitrary-instantiation LR property is claimed.

open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _,_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import TermCtx using (Z)
import Consistency as C
open import CastTerms
open import Conversion
open import Reduction
open import Primitives using (κℕ)
open import Interpreter
import Eval as E
import proof.LR-narrow.GeneralInstantiationSteps as GIS

nat⇒nat : Ty zero
nat⇒nat = ‵ `ℕ ⇒ ‵ `ℕ

poly-id-type : Ty zero
poly-id-type = `∀ (＇ Fin.zero ⇒ ＇ Fin.zero)

base-gate : C.instᵐ (C.idᶜ {zero}) C.⊢ ＇ Fin.zero ∼★
base-gate = C.X∼★ᵍ refl

bareX? : C.genᵐ (C.idᶜ {zero}) C.⊢ ★ ∼ ＇ Fin.zero
bareX? = C.？ (C.id (＇ Fin.zero))

wrappedY? : C.genᵐ (C.idᶜ {suc zero}) C.⊢ ★ ∼ ＇ Fin.zero
wrappedY? = C.？ (C.id (＇ Fin.zero))

bareℕ? : C.idᶜ {suc zero} C.⊢ ★ ∼ ‵ `ℕ
bareℕ? = C.？ (C.id (‵ `ℕ))

wrappedℕ? : C.idᶜ {suc (suc zero)} C.⊢ ★ ∼ ‵ `ℕ
wrappedℕ? = C.？ (C.id (‵ `ℕ))

bareℕ! : C.idᶜ {suc zero} C.⊢ ‵ `ℕ ∼ ★
bareℕ! = C.id (‵ `ℕ) C.!

wrappedℕ! : C.idᶜ {suc (suc zero)} C.⊢ ‵ `ℕ ∼ ★
wrappedℕ! = C.id (‵ `ℕ) C.!

bare-store : Ty zero → TyStore (suc zero)
bare-store R = store-bind store-empty R

wrapped-store : Ty zero → TyStore (suc (suc zero))
wrapped-store R = store-bind (store-bind store-empty R) (＇ Fin.zero)

bare-recover : (R : Ty zero) → Term (suc zero) → Term (suc zero)
bare-recover R P = (P ⟨ bareX? ⟩) ↑ unseal Fin.zero (⇑ᵗ R)

wrapped-recover : (R : Ty zero) → Term (suc (suc zero))
  → Term (suc (suc zero))
wrapped-recover R P =
  ((P ⟨ wrappedY? ⟩) ↑ unseal Fin.zero (＇ (Fin.suc Fin.zero)))
    ↑ unseal (Fin.suc Fin.zero) (⇑ᵗ (⇑ᵗ R))

bare-recover-⊢ : ∀ {R P}
  → ⟨ suc zero , bare-store R , [] ⟩ ⊢ P ⦂ ★
  → ⟨ suc zero , bare-store R , [] ⟩ ⊢ bare-recover R P ⦂ ⇑ᵗ R
bare-recover-⊢ P⊢ =
  ⊢reveal (⊢↑-unseal (Z∋ refl)) (⊢⟨⟩ P⊢ bareX?)

wrapped-recover-⊢ : ∀ {R P}
  → ⟨ suc (suc zero) , wrapped-store R , [] ⟩ ⊢ P ⦂ ★
  → ⟨ suc (suc zero) , wrapped-store R , [] ⟩
      ⊢ wrapped-recover R P ⦂ ⇑ᵗ (⇑ᵗ R)
wrapped-recover-⊢ P⊢ =
  ⊢reveal (⊢↑-unseal (S-bind∋ (Z∋ refl) refl))
    (⊢reveal (⊢↑-unseal (Z∋ refl)) (⊢⟨⟩ P⊢ wrappedY?))

bare-function-runtime : ℕ → Term (suc zero)
bare-function-runtime n =
  bare-recover nat⇒nat
    (GIS.instantiated-function nat⇒nat base-gate · (ƛ (` zero)))
    · $ (κℕ n)

wrapped-function-runtime : ℕ → Term (suc (suc zero))
wrapped-function-runtime n =
  wrapped-recover nat⇒nat
    (GIS.wrapped-instantiated-function nat⇒nat base-gate · (ƛ (` zero)))
    · $ (κℕ n)

bare-dynamic-runtime : ℕ → Term (suc zero)
bare-dynamic-runtime n =
  bare-recover ★
    (GIS.instantiated-function ★ base-gate · ($ (κℕ n) ⟨ bareℕ! ⟩))
    ⟨ bareℕ? ⟩

wrapped-dynamic-runtime : ℕ → Term (suc (suc zero))
wrapped-dynamic-runtime n =
  wrapped-recover ★
    (GIS.wrapped-instantiated-function ★ base-gate
      · ($ (κℕ n) ⟨ wrappedℕ! ⟩))
    ⟨ wrappedℕ? ⟩

bare-universal-runtime : ℕ → Term (suc zero)
bare-universal-runtime n =
  (bare-recover poly-id-type
    (GIS.instantiated-function poly-id-type base-gate
      · (Λ (ƛ (` zero))))
    ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ‵ `ℕ ])
    · $ (κℕ n)

wrapped-universal-runtime : ℕ → Term (suc (suc zero))
wrapped-universal-runtime n =
  (wrapped-recover poly-id-type
    (GIS.wrapped-instantiated-function poly-id-type base-gate
      · (Λ (ƛ (` zero))))
    ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ‵ `ℕ ])
    · $ (κℕ n)

bare-function-runtime-⊢ : ∀ n
  → ⟨ suc zero , bare-store nat⇒nat , [] ⟩
      ⊢ bare-function-runtime n ⦂ ‵ `ℕ
bare-function-runtime-⊢ n =
  ⊢· (bare-recover-⊢ (⊢· GIS.instantiated-function-⊢ (⊢ƛ (⊢` Z))))
    (⊢$ (κℕ n))

wrapped-function-runtime-⊢ : ∀ n
  → ⟨ suc (suc zero) , wrapped-store nat⇒nat , [] ⟩
      ⊢ wrapped-function-runtime n ⦂ ‵ `ℕ
wrapped-function-runtime-⊢ n =
  ⊢· (wrapped-recover-⊢
      (⊢· GIS.wrapped-instantiated-function-⊢ (⊢ƛ (⊢` Z))))
    (⊢$ (κℕ n))

bare-dynamic-runtime-⊢ : ∀ n
  → ⟨ suc zero , bare-store ★ , [] ⟩
      ⊢ bare-dynamic-runtime n ⦂ ‵ `ℕ
bare-dynamic-runtime-⊢ n =
  ⊢⟨⟩ (bare-recover-⊢
      (⊢· GIS.instantiated-function-⊢
        (⊢⟨⟩ (⊢$ (κℕ n)) bareℕ!)))
    bareℕ?

wrapped-dynamic-runtime-⊢ : ∀ n
  → ⟨ suc (suc zero) , wrapped-store ★ , [] ⟩
      ⊢ wrapped-dynamic-runtime n ⦂ ‵ `ℕ
wrapped-dynamic-runtime-⊢ n =
  ⊢⟨⟩ (wrapped-recover-⊢
      (⊢· GIS.wrapped-instantiated-function-⊢
        (⊢⟨⟩ (⊢$ (κℕ n)) wrappedℕ!)))
    wrappedℕ?

bare-universal-runtime-⊢ : ∀ n
  → ⟨ suc zero , bare-store poly-id-type , [] ⟩
      ⊢ bare-universal-runtime n ⦂ ‵ `ℕ
bare-universal-runtime-⊢ n =
  ⊢· (⊢• (bare-recover-⊢
        (⊢· GIS.instantiated-function-⊢
          (⊢Λ (ƛ (` zero)) (⊢ƛ (⊢` Z))))))
    (⊢$ (κℕ n))

wrapped-universal-runtime-⊢ : ∀ n
  → ⟨ suc (suc zero) , wrapped-store poly-id-type , [] ⟩
      ⊢ wrapped-universal-runtime n ⦂ ‵ `ℕ
wrapped-universal-runtime-⊢ n =
  ⊢· (⊢• (wrapped-recover-⊢
        (⊢· GIS.wrapped-instantiated-function-⊢
          (⊢Λ (ƛ (` zero)) (⊢ƛ (⊢` Z))))))
    (⊢$ (κℕ n))

bare-function-runtime-return : ∀ n
  → ∃[ tr ] interpretFrom (bare-store nat⇒nat) 6
      (bare-function-runtime n)
      ≡ returned (E.result (suc zero)
        (keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ n)) tr ($ (κℕ n)))
bare-function-runtime-return n = _ , refl

wrapped-function-runtime-return : ∀ n
  → ∃[ tr ] interpretFrom (wrapped-store nat⇒nat) 9
      (wrapped-function-runtime n)
      ≡ returned (E.result (suc (suc zero))
        (keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep
          ∷ keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ n)) tr ($ (κℕ n)))
wrapped-function-runtime-return n = _ , refl

bare-dynamic-runtime-return : ∀ n
  → ∃[ tr ] interpretFrom (bare-store ★) 6
      (bare-dynamic-runtime n)
      ≡ returned (E.result (suc zero)
        (keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ n)) tr ($ (κℕ n)))
bare-dynamic-runtime-return n = _ , refl

wrapped-dynamic-runtime-return : ∀ n
  → ∃[ tr ] interpretFrom (wrapped-store ★) 9
      (wrapped-dynamic-runtime n)
      ≡ returned (E.result (suc (suc zero))
        (keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep
          ∷ keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ n)) tr ($ (κℕ n)))
wrapped-dynamic-runtime-return n = _ , refl

bare-universal-runtime-return : ∀ n
  → ∃[ tr ] interpretFrom (bare-store poly-id-type) 9
      (bare-universal-runtime n)
      ≡ returned (E.result (suc (suc zero))
        (keep ∷ keep ∷ keep ∷ keep ∷ keep
          ∷ bind (‵ `ℕ) ∷ keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ n)) tr ($ (κℕ n)))
bare-universal-runtime-return n = _ , refl

wrapped-universal-runtime-return : ∀ n
  → ∃[ tr ] interpretFrom (wrapped-store poly-id-type) 12
      (wrapped-universal-runtime n)
      ≡ returned (E.result (suc (suc (suc zero)))
        (keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep
          ∷ keep ∷ keep ∷ bind (‵ `ℕ)
          ∷ keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ n)) tr ($ (κℕ n)))
wrapped-universal-runtime-return n = _ , refl
