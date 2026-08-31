module proof.LR-narrow.RepeatedBoundaryControls where

-- File Charter:
--   * Adversarial nominal observations after three mixed cast/seal roundtrips.
--   * The payload is produced under allocating universal wrappers; its old
--     nominal tag remains observable despite its name-free function type.
--   * Typed positive and negative controls, not a claimed CTI pair. Depends
--     only on the unchanged calculus and its proof-carrying evaluator.

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_)
open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import TermCtx using (Z)
open import Primitives using (κℕ; addℕ)
open import CastTerms
open import Conversion
open import Reduction
import Consistency as C
import Eval as E
open import Interpreter

inject : ∀ {Δ} (X : TyVar Δ) → C.idᶜ C.⊢ ＇ X ∼ ★
inject X = C.id (＇ X) C.!

project : ∀ {Δ} (X : TyVar Δ) → C.idᶜ C.⊢ ★ ∼ ＇ X
project X = C.？ (C.id (＇ X))

roundtrip : ∀ {Δ} → TyVar Δ → Term Δ → Term Δ
roundtrip X M =
  (((M ↓ seal X (‵ `ℕ)) ⟨ inject X ⟩) ⟨ project X ⟩)
    ↑ unseal X (‵ `ℕ)

roundtrip-⊢ : ∀ {Δ Σ Γ X} {M : Term Δ}
  → Σ ∋ X ⦂ ‵ `ℕ
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ ‵ `ℕ
  → ⟨ Δ , Σ , Γ ⟩ ⊢ roundtrip X M ⦂ ‵ `ℕ
roundtrip-⊢ {X = X} entry d = ⊢reveal (⊢↑-unseal entry)
  (⊢⟨⟩ (⊢⟨⟩ (⊢conceal (⊢↓-seal entry) d) (inject X)) (project X))

producer : ∀ {Δ} → TyVar Δ → TyVar Δ → Term Δ
producer X Y = ƛ
  (roundtrip X (roundtrip Y (roundtrip X
    (` zero ⊕[ addℕ ] $ (κℕ 1)))))

producer-⊢ : ∀ {Δ Σ X Y}
  → Σ ∋ X ⦂ ‵ `ℕ
  → Σ ∋ Y ⦂ ‵ `ℕ
  → ⟨ Δ , Σ , [] ⟩ ⊢ producer X Y ⦂ (‵ `ℕ ⇒ ‵ `ℕ)
producer-⊢ ex ey = ⊢ƛ (roundtrip-⊢ ex (roundtrip-⊢ ey
  (roundtrip-⊢ ex (⊢⊕ addℕ (⊢` Z) (⊢$ (κℕ 1))))))

exporter : ∀ {Δ} → TyVar Δ → TyVar Δ → Term Δ
exporter X Y = ƛ
  (((producer X Y · ` zero) ↓ seal X (‵ `ℕ)) ⟨ inject X ⟩)

exporter-⊢ : ∀ {Δ Σ X Y}
  → Σ ∋ X ⦂ ‵ `ℕ
  → Σ ∋ Y ⦂ ‵ `ℕ
  → ⟨ Δ , Σ , [] ⟩ ⊢ exporter X Y ⦂ (‵ `ℕ ⇒ ★)
exporter-⊢ {X = X} ex ey = ⊢ƛ (⊢⟨⟩ (⊢conceal (⊢↓-seal ex)
  (⊢· (⊢ƛ (roundtrip-⊢ ex (roundtrip-⊢ ey
    (roundtrip-⊢ ex (⊢⊕ addℕ (⊢` Z) (⊢$ (κℕ 1)))))))
    (⊢` Z))) (inject X))

two-names : TyStore 2
two-names = store-bind (store-bind store-empty (‵ `ℕ)) (‵ `ℕ)

X Y : TyVar 2
X = Fin.suc Fin.zero
Y = Fin.zero

entry : ∀ Q → two-names ∋ Q ⦂ ‵ `ℕ
entry Fin.zero = Z∋ refl
entry (Fin.suc Fin.zero) = S-bind∋ (Z∋ refl) refl

poly-exporter : Term 2
poly-exporter = Λ (exporter (Fin.suc X) (Fin.suc Y))

poly-exporter-⊢ :
  ⟨ 2 , two-names , [] ⟩ ⊢ poly-exporter ⦂ `∀ (‵ `ℕ ⇒ ★)
poly-exporter-⊢ = ⊢Λ (ƛ _) (exporter-⊢
  (S-lift∋ (entry X) refl) (S-lift∋ (entry Y) refl))

-- The wrappers have equal endpoint types, but allocate on instantiation.
-- The three inner rounds use actual names and nonidentity casts/conversions.

r : Conv↑ 2 (`∀ (‵ `ℕ ⇒ ★)) (`∀ (‵ `ℕ ⇒ ★))
r = `∀↑ (id↑ (‵ `ℕ ⇒ ★))

c : Conv↓ 2 (`∀ (‵ `ℕ ⇒ ★)) (`∀ (‵ `ℕ ⇒ ★))
c = `∀↓ (id↓ (‵ `ℕ ⇒ ★))

observe : TyVar 2 → ℕ → Term 2
observe Q n =
  ((((poly-exporter ↑ r) ↓ c) ⦂∀ (‵ `ℕ ⇒ ★) [ ‵ `ℕ ])
    · $ (κℕ n)) ⟨ project Q ⟩ ↑ unseal Q (‵ `ℕ)

observe-⊢ : ∀ Q n
  → ⟨ 2 , two-names , [] ⟩ ⊢ observe Q n ⦂ ‵ `ℕ
observe-⊢ Q n = ⊢reveal (⊢↑-unseal (entry Q))
  (⊢⟨⟩ (⊢· (⊢• (⊢conceal (⊢↓-∀ ⊢↓-id)
    (⊢reveal (⊢↑-∀ ⊢↑-id) poly-exporter-⊢)))
    (⊢$ (κℕ n))) (project Q))

matching-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ χ ∈ StoreChanges 2 Δ′ ]
    Σ[ trace ∈ observe X n —↠[ χ ] $ (κℕ (n + 1)) ]
      interpretFrom two-names 64 (observe X n)
        ≡ returned (E.result Δ′ χ ($ (κℕ (n + 1))) trace ($ (κℕ (n + 1))))
matching-return n = _ , _ , _ , refl

mismatching-blame : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ χ ∈ StoreChanges 2 Δ′ ]
    Σ[ trace ∈ observe Y n —↠[ χ ] blame ]
      interpretFrom two-names 64 (observe Y n) ≡ blamed χ trace
mismatching-blame n = _ , _ , _ , refl

-- Repeated successful crossings and equal representations still do not make
-- the two final nominal queries interchangeable.

query-independent-success-impossible :
  (∀ Q n → ∃[ out ]
    interpretFrom two-names 64 (observe Q n) ≡ returned out)
  → ⊥
query-independent-success-impossible rule with rule Y 7
query-independent-success-impossible rule | out , ()
