module proof.LR-narrow.IntegratedEscapingProducer where

-- File Charter:
--   * E13/E15 before their final natural projection: the universal producer
--     returns fresh nominal packets related by the integrated dynamic type.
--   * Installs matches/precise-only capabilities in actual returned scopes.
--   * These are all-index, all-natural-input observations of concrete calls,
--     not an arbitrary-body universal compatibility theorem.

open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; ∃-syntax; proj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import Reduction
open import Primitives using (κℕ)
open import Interpreter
import Eval as E
import Consistency as C
open import LR-narrow.LogicalRelation using (groundInjection)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.IntegratedModel
import proof.LR-narrow.IntegratedWorld as IW
import proof.LR-narrow.IntegratedData as ID
import proof.LR-narrow.IntegratedProjection as IP
import proof.LR-narrow.DynamicWrapperExamples as D

open Model store-empty store-empty
open IW.Worlds store-empty store-empty
open ID.Data store-empty store-empty

private
  bare-gate : C.instᵐ (C.idᶜ {0}) C.⊢ ＇ Fin.zero ∼★
  bare-gate = C.X∼★ᵍ refl

  wrapped-gate : C.renameEnv∼ (C.keep C.wk↪ᵗ) (C.instᵐ (C.idᶜ {0}))
    C.⊢ ＇ Fin.zero ∼★
  wrapped-gate = C.X∼★ᵍ refl

-- The 4/8/1-step fuel bounds below use constructor form so overloaded
-- numeral instance search does not block inference of the trace existential.
bare-return : ∀ (n : ℕ)
  → ∃[ tr ] interpretFrom store-empty (suc (suc (suc (suc zero))))
      ((D.payload-function ⦂∀ D.payload-body [ ‵ `ℕ ]) · $ (κℕ n))
      ≡ returned (E.result (suc zero)
        (bind (‵ `ℕ) ∷ keep ∷ keep ∷ keep ∷ [])
        (($ (κℕ n) ↓ seal Fin.zero (‵ `ℕ))
          ⟨ groundInjection (＇ Fin.zero) bare-gate ⟩) tr
        ((($ (κℕ n)) ↓ seal {X = Fin.zero} {R = ‵ `ℕ})
          《 inj ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ G∼★ = bare-gate ⦄
            ⦃ Gns = nonstar-X ⦄ 》))
bare-return n = _ , refl

wrapped-return : ∀ (n : ℕ)
  → ∃[ tr ] interpretFrom store-empty
      (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))
      (((D.payload-function ↑ D.payload-reveal)
          ⦂∀ D.payload-body [ ‵ `ℕ ]) · $ (κℕ n))
      ≡ returned (E.result (suc (suc zero))
        (bind (‵ `ℕ) ∷ bind (＇ Fin.zero)
          ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [])
        ((($ (κℕ n) ↓ seal (Fin.suc Fin.zero) (‵ `ℕ))
          ↓ seal Fin.zero (＇ (Fin.suc Fin.zero)))
          ⟨ groundInjection (＇ Fin.zero) wrapped-gate ⟩) tr
        (((($ (κℕ n)) ↓ seal {X = Fin.suc Fin.zero} {R = ‵ `ℕ})
            ↓ seal {X = Fin.zero} {R = ＇ (Fin.suc Fin.zero)})
          《 inj ⦃ Gᵍ = ＇ Fin.zero ⦄ ⦃ G∼★ = wrapped-gate ⦄
            ⦃ Gns = nonstar-X ⦄ 》))
wrapped-return n = _ , refl

wrapped-call-observed : ∀ n k
  → Observed dataDynamic (empty {S = root} {T = root}) k
      (((D.payload-function ↑ D.payload-reveal)
          ⦂∀ D.payload-body [ ‵ `ℕ ]) · $ (κℕ n))
      ((D.payload-function ⦂∀ D.payload-body [ ‵ `ℕ ]) · $ (κℕ n))
wrapped-call-observed n k =
  observed-from-returns {gasI = 8} {gasP = 4}
    {W′ = extend-paired (extend-privateI empty (‵ `ℕ))
      (＇ Fin.zero) (‵ `ℕ)} (proj₂ (wrapped-return n)) (proj₂ (bare-return n))
    (record { matched-future = λ (); only-future = λ () })
    (matched-name-tagged new-paired
      (I.ground-packet _ _
        (I.payload-seal (Z∋ refl)
          (I.payload-seal (S-bind∋ (Z∋ refl) refl) I.payload-natural))
        wrapped-gate refl)
      (P.ground-packet _ _ (P.payload-seal (Z∋ refl) P.payload-natural)
        bare-gate refl))

erased-return : ∀ (n : ℕ)
  → ∃[ tr ] interpretFrom store-empty (suc zero)
      (D.erased-target · ($ (κℕ n) ⟨ D.ℕ! ⟩))
      ≡ returned (E.result zero (keep ∷ [])
        ($ (κℕ n) ⟨ D.ℕ! ⟩) tr
        (($ (κℕ n)) 《 inj ⦃ Gᵍ = ‵ `ℕ ⦄
          ⦃ G∼★ = C.ι∼★ {μ = C.idᶜ} ⦄ ⦃ Gns = nonstar-ι ⦄ 》))
erased-return n = _ , refl

bare-call-⊢ : ∀ n → ⟨ 0 , store-empty , [] ⟩
  ⊢ (D.payload-function ⦂∀ D.payload-body [ ‵ `ℕ ]) · $ (κℕ n) ⦂ ★
bare-call-⊢ n = ⊢· (⊢• D.payload-function-⊢) (⊢$ (κℕ n))

wrapped-call-⊢ : ∀ n → ⟨ 0 , store-empty , [] ⟩
  ⊢ ((D.payload-function ↑ D.payload-reveal)
      ⦂∀ D.payload-body [ ‵ `ℕ ]) · $ (κℕ n) ⦂ ★
wrapped-call-⊢ n = ⊢·
  (⊢• (⊢reveal (⊢↑-∀ ⊢↑-id) D.payload-function-⊢)) (⊢$ (κℕ n))

erased-call-⊢ : ∀ n → ⟨ 0 , store-empty , [] ⟩
  ⊢ D.erased-target · ($ (κℕ n) ⟨ D.ℕ! ⟩) ⦂ ★
erased-call-⊢ n =
  ⊢· D.erased-target-⊢ (⊢⟨⟩ (⊢$ (κℕ n)) D.ℕ!)

erased-call-observed : ∀ n k
  → Observed dataDynamic (empty {S = root} {T = root}) k
      (D.erased-target · ($ (κℕ n) ⟨ D.ℕ! ⟩))
      ((D.payload-function ⦂∀ D.payload-body [ ‵ `ℕ ]) · $ (κℕ n))
erased-call-observed n k =
  observed-from-returns {gasI = 1} {gasP = 4}
    {W′ = extend-only empty (‵ `ℕ)}
    (proj₂ (erased-return n)) (proj₂ (bare-return n))
    (record { matched-future = λ (); only-future = λ () })
    (precise-only-tagged new-precise-only
      (I.ground-packet _ _ I.payload-natural C.ι∼★ refl)
      (P.ground-packet _ _ (P.payload-seal (Z∋ refl) P.payload-natural)
        bare-gate refl))

-- These endpoint theorems now factor through the dynamic relation and the
-- shared frame rule, rather than being justified solely by final blame.
wrapped-projection-observed : ∀ n k
  → Observed natural (empty {S = root} {T = root}) k
      (D.wrapped-payload-runtime n) (D.payload-runtime n)
wrapped-projection-observed n k =
  IP.Projections.natural-query-observed store-empty store-empty
    (wrapped-call-observed n k)

erased-projection-observed : ∀ n k
  → Observed natural (empty {S = root} {T = root}) k
      (D.erased-runtime n) (D.payload-runtime n)
erased-projection-observed n k =
  IP.Projections.natural-query-observed store-empty store-empty
    (erased-call-observed n k)
