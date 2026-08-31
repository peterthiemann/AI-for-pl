module proof.LR-narrow.MixedBoundaryExamples where

-- File Charter:
--   * Repeated genuine casts interleaved with nominal seal/unseal conversions.
--   * Checks whole-program CTI, typing, and data observations for function,
--     allocating universal, and asymmetric latent-blame examples.
--   * Uses the unchanged calculus and LR; no cancellation principle is assumed.

open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ-syntax; _,_)
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
import Imprecision as I
import Eval as E
open import Interpreter
import proof.DGG.CtxImp as CTX
import proof.DGG.CastTermImprecision as CTI
open CTI using (_∣_⊢²_⊑_∶_)
import proof.DGG.Examples2 as Ex

nat-store : TyStore 1
nat-store = store-bind store-empty (‵ `ℕ)

W : CTX.World 1 1 1
W = Ex.reflWorld nat-store

rebase-X : CTX.RebaseAt W W Fin.zero Fin.zero
rebase-X = CTX.sameWorldRebaseAt refl (CTX.store-rep-imp I.ι⊑ι)

-- Actual cast boundaries, not identity conversions.

up : ∀ {Δ} {μ : C.Env∼ Δ}
  → μ C.⊢ (‵ `ℕ ⇒ ‵ `ℕ) ∼ (★ ⇒ ★)
up = C.？ (C.id (‵ `ℕ)) C.↦ (C.id (‵ `ℕ) C.!)

down : ∀ {Δ} {μ : C.Env∼ Δ}
  → μ C.⊢ (★ ⇒ ★) ∼ (‵ `ℕ ⇒ ‵ `ℕ)
down = (C.id (‵ `ℕ) C.!) C.↦ C.？ (C.id (‵ `ℕ))

cast-round : ∀ {Δ} → Term Δ → Term Δ
cast-round M = M ⟨ up {μ = C.idᶜ} ⟩ ⟨ down {μ = C.idᶜ} ⟩

cast-round-⊢ : ∀ {Δ Σ Γ} {M : Term Δ}
  → ⟨ Δ , Σ , Γ ⟩ ⊢ M ⦂ (‵ `ℕ ⇒ ‵ `ℕ)
  → ⟨ Δ , Σ , Γ ⟩ ⊢ cast-round M ⦂ (‵ `ℕ ⇒ ‵ `ℕ)
cast-round-⊢ d = ⊢⟨⟩ (⊢⟨⟩ d up) down

cast-round² : ∀ {M N}
  → W ∣ [] ⊢² M ⊑ N ∶ I.⇒⊑⇒ I.ι⊑ι I.ι⊑ι
  → W ∣ [] ⊢² M ⊑ cast-round N ∶ I.⇒⊑⇒ I.ι⊑ι I.ι⊑ι
cast-round² d = CTI.⊑cast² down
  (CTI.⊑cast² up d (I.⇒⊑⇒ I.ι⊑★ I.ι⊑★))
  (I.⇒⊑⇒ I.ι⊑ι I.ι⊑ι)

seal-function :
  Conv↓ 1 (‵ `ℕ ⇒ ‵ `ℕ) (＇ Fin.zero ⇒ ＇ Fin.zero)
seal-function = unseal Fin.zero (‵ `ℕ) ↦↓ seal Fin.zero (‵ `ℕ)

unseal-function :
  Conv↑ 1 (＇ Fin.zero ⇒ ＇ Fin.zero) (‵ `ℕ ⇒ ‵ `ℕ)
unseal-function = seal Fin.zero (‵ `ℕ) ↦↑ unseal Fin.zero (‵ `ℕ)

seal-function-⊢ˣ : nat-store ⊢↓[ just Fin.zero ] seal-function
seal-function-⊢ˣ = ⊢↓-⇒ˣ join-both
  (⊢↑-unsealˣ (Z∋ refl)) (⊢↓-sealˣ (Z∋ refl))

unseal-function-⊢ˣ : nat-store ⊢↑[ just Fin.zero ] unseal-function
unseal-function-⊢ˣ = ⊢↑-⇒ˣ join-both
  (⊢↓-sealˣ (Z∋ refl)) (⊢↑-unsealˣ (Z∋ refl))

seal-round : Term 1 → Term 1
seal-round M = (M ↓ seal-function) ↑ unseal-function

seal-round-⊢ : ∀ {M}
  → ⟨ 1 , nat-store , [] ⟩ ⊢ M ⦂ (‵ `ℕ ⇒ ‵ `ℕ)
  → ⟨ 1 , nat-store , [] ⟩ ⊢ seal-round M ⦂ (‵ `ℕ ⇒ ‵ `ℕ)
seal-round-⊢ d = ⊢reveal
  (⊢↑-⇒ (⊢↓-seal (Z∋ refl)) (⊢↑-unseal (Z∋ refl)))
  (⊢conceal
    (⊢↓-⇒ (⊢↑-unseal (Z∋ refl)) (⊢↓-seal (Z∋ refl))) d)

seal-round² : ∀ {M N}
  → W ∣ [] ⊢² M ⊑ N ∶ I.⇒⊑⇒ I.ι⊑ι I.ι⊑ι
  → W ∣ [] ⊢² seal-round M ⊑ seal-round N
      ∶ I.⇒⊑⇒ I.ι⊑ι I.ι⊑ι
seal-round² d = CTI.reveal⊑reveal² (λ _ eq → eq) rebase-X CTX.same-[]
  unseal-function-⊢ˣ unseal-function-⊢ˣ
  (CTI.conceal⊑conceal² CTX.matched-fun-conceal-target
    (λ _ eq → eq) rebase-X CTX.same-[]
    seal-function-⊢ˣ seal-function-⊢ˣ d (I.⇒⊑⇒ I.X⊑X I.X⊑X))
  (I.⇒⊑⇒ I.ι⊑ι I.ι⊑ι)

increment : ∀ {Δ} → Term Δ
increment = ƛ ((` zero) ⊕[ addℕ ] $ (κℕ 1))

increment-⊢ : ∀ {Δ Σ}
  → ⟨ Δ , Σ , [] ⟩ ⊢ increment ⦂ (‵ `ℕ ⇒ ‵ `ℕ)
increment-⊢ = ⊢ƛ (⊢⊕ addℕ (⊢` Z) (⊢$ (κℕ 1)))

increment² :
  W ∣ [] ⊢² increment ⊑ increment ∶ I.⇒⊑⇒ I.ι⊑ι I.ι⊑ι
increment² = CTI.ƛ⊑ƛ² (CTI.⊕⊑⊕² addℕ
  (CTI.x⊑x² CTX.Zʷ) (CTI.κ⊑κ² (κℕ 1) I.ι⊑ι) I.ι⊑ι)

-- M1: two nominal roundtrips, three interleaved function-cast roundtrips.
-- Both programs force the higher-order wrappers by applying them to n.

interleaved-source : ℕ → Term 1
interleaved-source n = seal-round (seal-round increment) · $ (κℕ n)

interleaved-target : ℕ → Term 1
interleaved-target n =
  cast-round (seal-round (cast-round (seal-round (cast-round increment))))
    · $ (κℕ n)

interleaved-source-⊢ : ∀ n
  → ⟨ 1 , nat-store , [] ⟩ ⊢ interleaved-source n ⦂ ‵ `ℕ
interleaved-source-⊢ n =
  ⊢· (seal-round-⊢ (seal-round-⊢ increment-⊢)) (⊢$ (κℕ n))

interleaved-target-⊢ : ∀ n
  → ⟨ 1 , nat-store , [] ⟩ ⊢ interleaved-target n ⦂ ‵ `ℕ
interleaved-target-⊢ n =
  ⊢· (cast-round-⊢ (seal-round-⊢ (cast-round-⊢
    (seal-round-⊢ (cast-round-⊢ increment-⊢))))) (⊢$ (κℕ n))

interleaved² : ∀ n
  → W ∣ [] ⊢² interleaved-source n ⊑ interleaved-target n ∶ I.ι⊑ι
interleaved² n = CTI.·⊑·²
  (cast-round² (seal-round² (cast-round² (seal-round²
    (cast-round² increment²))))) (CTI.κ⊑κ² (κℕ n) I.ι⊑ι)

interleaved-source-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ χ ∈ StoreChanges 1 Δ′ ]
    Σ[ trace ∈ interleaved-source n —↠[ χ ] $ (κℕ (n + 1)) ]
      interpretFrom nat-store 32 (interleaved-source n)
        ≡ returned
          (E.result Δ′ χ ($ (κℕ (n + 1))) trace ($ (κℕ (n + 1))))
interleaved-source-return n = _ , _ , _ , refl

interleaved-target-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ χ ∈ StoreChanges 1 Δ′ ]
    Σ[ trace ∈ interleaved-target n —↠[ χ ] $ (κℕ (n + 1)) ]
      interpretFrom nat-store 64 (interleaved-target n)
        ≡ returned
          (E.result Δ′ χ ($ (κℕ (n + 1))) trace ($ (κℕ (n + 1))))
interleaved-target-return n = _ , _ , _ , refl

-- M2: the same interaction under an allocating universal; these conversions
-- change the old X inside the body, unlike the earlier ∀↑ id↑ examples.

seal-poly : Conv↓ 1 (`∀ (‵ `ℕ ⇒ ‵ `ℕ))
  (`∀ (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero)))
seal-poly = `∀↓ (unseal (Fin.suc Fin.zero) (‵ `ℕ)
  ↦↓ seal (Fin.suc Fin.zero) (‵ `ℕ))

unseal-poly : Conv↑ 1
  (`∀ (＇ (Fin.suc Fin.zero) ⇒ ＇ (Fin.suc Fin.zero)))
  (`∀ (‵ `ℕ ⇒ ‵ `ℕ))
unseal-poly = `∀↑ (seal (Fin.suc Fin.zero) (‵ `ℕ)
  ↦↑ unseal (Fin.suc Fin.zero) (‵ `ℕ))

seal-poly-⊢ˣ : nat-store ⊢↓[ just Fin.zero ] seal-poly
seal-poly-⊢ˣ = ⊢↓-∀ˣ (⊢↓-⇒ˣ join-both
  (⊢↑-unsealˣ (S-lift∋ (Z∋ refl) refl))
  (⊢↓-sealˣ (S-lift∋ (Z∋ refl) refl)))

unseal-poly-⊢ˣ : nat-store ⊢↑[ just Fin.zero ] unseal-poly
unseal-poly-⊢ˣ = ⊢↑-∀ˣ (⊢↑-⇒ˣ join-both
  (⊢↓-sealˣ (S-lift∋ (Z∋ refl) refl))
  (⊢↑-unsealˣ (S-lift∋ (Z∋ refl) refl)))

seal-poly-round : Term 1 → Term 1
seal-poly-round M = (M ↓ seal-poly) ↑ unseal-poly

seal-poly-round-⊢ : ∀ {M}
  → ⟨ 1 , nat-store , [] ⟩ ⊢ M ⦂ `∀ (‵ `ℕ ⇒ ‵ `ℕ)
  → ⟨ 1 , nat-store , [] ⟩ ⊢ seal-poly-round M
      ⦂ `∀ (‵ `ℕ ⇒ ‵ `ℕ)
seal-poly-round-⊢ d = ⊢reveal (⊢↑-∀ (⊢↑-⇒
  (⊢↓-seal (S-lift∋ (Z∋ refl) refl))
  (⊢↑-unseal (S-lift∋ (Z∋ refl) refl))))
  (⊢conceal (⊢↓-∀ (⊢↓-⇒
    (⊢↑-unseal (S-lift∋ (Z∋ refl) refl))
    (⊢↓-seal (S-lift∋ (Z∋ refl) refl)))) d)

seal-poly-round² : ∀ {M N}
  → W ∣ [] ⊢² M ⊑ N ∶ I.∀⊑∀ (I.⇒⊑⇒ I.ι⊑ι I.ι⊑ι)
  → W ∣ [] ⊢² seal-poly-round M ⊑ seal-poly-round N
      ∶ I.∀⊑∀ (I.⇒⊑⇒ I.ι⊑ι I.ι⊑ι)
seal-poly-round² d =
  CTI.reveal⊑reveal² (λ _ eq → eq) rebase-X CTX.same-[]
  unseal-poly-⊢ˣ unseal-poly-⊢ˣ
  (CTI.conceal⊑conceal² CTX.matched-all-conceal-target
    (λ _ eq → eq) rebase-X CTX.same-[] seal-poly-⊢ˣ seal-poly-⊢ˣ d
    (I.∀⊑∀ (I.⇒⊑⇒ I.X⊑X I.X⊑X)))
  (I.∀⊑∀ (I.⇒⊑⇒ I.ι⊑ι I.ι⊑ι))

cast-poly-round : Term 1 → Term 1
cast-poly-round M =
  M ⟨ C.∀ᶜ (up {μ = C.extᵐ C.idᶜ}) ⟩
    ⟨ C.∀ᶜ (down {μ = C.extᵐ C.idᶜ}) ⟩

cast-poly-round-⊢ : ∀ {M}
  → ⟨ 1 , nat-store , [] ⟩ ⊢ M ⦂ `∀ (‵ `ℕ ⇒ ‵ `ℕ)
  → ⟨ 1 , nat-store , [] ⟩ ⊢ cast-poly-round M
      ⦂ `∀ (‵ `ℕ ⇒ ‵ `ℕ)
cast-poly-round-⊢ d = ⊢⟨⟩ (⊢⟨⟩ d (C.∀ᶜ up)) (C.∀ᶜ down)

cast-poly-round² : ∀ {M N}
  → W ∣ [] ⊢² M ⊑ N ∶ I.∀⊑∀ (I.⇒⊑⇒ I.ι⊑ι I.ι⊑ι)
  → W ∣ [] ⊢² M ⊑ cast-poly-round N
      ∶ I.∀⊑∀ (I.⇒⊑⇒ I.ι⊑ι I.ι⊑ι)
cast-poly-round² d = CTI.⊑cast² (C.∀ᶜ down)
  (CTI.⊑cast² (C.∀ᶜ up) d
    (I.∀⊑∀ (I.⇒⊑⇒ I.ι⊑★ I.ι⊑★)))
  (I.∀⊑∀ (I.⇒⊑⇒ I.ι⊑ι I.ι⊑ι))

poly-increment : Term 1
poly-increment = Λ increment

poly-increment-⊢ :
  ⟨ 1 , nat-store , [] ⟩ ⊢ poly-increment ⦂ `∀ (‵ `ℕ ⇒ ‵ `ℕ)
poly-increment-⊢ =
  ⊢Λ (ƛ ((` zero) ⊕[ addℕ ] $ (κℕ 1))) increment-⊢

poly-increment² : W ∣ [] ⊢² poly-increment ⊑ poly-increment
  ∶ I.∀⊑∀ (I.⇒⊑⇒ I.ι⊑ι I.ι⊑ι)
poly-increment² = CTI.Λ⊑Λ² CTX.lift-[] (ƛ _) (ƛ _)
  (CTI.ƛ⊑ƛ² (CTI.⊕⊑⊕² addℕ
    (CTI.x⊑x² {p = I.ι⊑ι} CTX.Zʷ)
    (CTI.κ⊑κ² (κℕ 1) I.ι⊑ι) I.ι⊑ι))
  (I.∀⊑∀ (I.⇒⊑⇒ I.ι⊑ι I.ι⊑ι))

allocating-source : ℕ → Term 1
allocating-source n =
  (seal-poly-round (seal-poly-round poly-increment)
    ⦂∀ (‵ `ℕ ⇒ ‵ `ℕ) [ ‵ `ℕ ]) · $ (κℕ n)

allocating-target : ℕ → Term 1
allocating-target n =
  (cast-poly-round (seal-poly-round
    (cast-poly-round (seal-poly-round (cast-poly-round poly-increment))))
    ⦂∀ (‵ `ℕ ⇒ ‵ `ℕ) [ ‵ `ℕ ]) · $ (κℕ n)

allocating-source-⊢ : ∀ n
  → ⟨ 1 , nat-store , [] ⟩ ⊢ allocating-source n ⦂ ‵ `ℕ
allocating-source-⊢ n = ⊢·
  (⊢• (seal-poly-round-⊢ (seal-poly-round-⊢ poly-increment-⊢)))
  (⊢$ (κℕ n))

allocating-target-⊢ : ∀ n
  → ⟨ 1 , nat-store , [] ⟩ ⊢ allocating-target n ⦂ ‵ `ℕ
allocating-target-⊢ n =
  ⊢· (⊢• (cast-poly-round-⊢ (seal-poly-round-⊢
    (cast-poly-round-⊢ (seal-poly-round-⊢
      (cast-poly-round-⊢ poly-increment-⊢)))))) (⊢$ (κℕ n))

allocating² : ∀ n
  → W ∣ [] ⊢² allocating-source n ⊑ allocating-target n ∶ I.ι⊑ι
allocating² n = CTI.·⊑·²
  (CTI.•⊑•² (I.∀⊑∀ (I.⇒⊑⇒ I.ι⊑ι I.ι⊑ι))
    (cast-poly-round² (seal-poly-round² (cast-poly-round²
      (seal-poly-round² (cast-poly-round² poly-increment²)))))
    I.ι⊑ι (I.⇒⊑⇒ I.ι⊑ι I.ι⊑ι))
  (CTI.κ⊑κ² (κℕ n) I.ι⊑ι)

allocating-source-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ χ ∈ StoreChanges 1 Δ′ ]
    Σ[ trace ∈ allocating-source n —↠[ χ ] $ (κℕ (n + 1)) ]
      interpretFrom nat-store 64 (allocating-source n)
        ≡ returned
          (E.result Δ′ χ ($ (κℕ (n + 1))) trace ($ (κℕ (n + 1))))
allocating-source-return n = _ , _ , _ , refl

allocating-target-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ χ ∈ StoreChanges 1 Δ′ ]
    Σ[ trace ∈ allocating-target n —↠[ χ ] $ (κℕ (n + 1)) ]
      interpretFrom nat-store 128 (allocating-target n)
        ≡ returned
          (E.result Δ′ χ ($ (κℕ (n + 1))) trace ($ (κℕ (n + 1))))
allocating-target-return n = _ , _ , _ , refl

------------------------------------------------------------------------
-- M3: asymmetric repeated mixed boundaries with latent precise blame.
------------------------------------------------------------------------

star-store : TyStore 1
star-store = store-bind store-empty ★

W★ : CTX.World 1 1 1
W★ = CTX.world C.id↪ᵗ C.id↪ᵗ (λ _ → I.X⊑★) nat-store star-store

rebase-X★ : CTX.RebaseAt W★ W★ Fin.zero Fin.zero
rebase-X★ = CTX.sameWorldRebaseAt refl (CTX.store-rep-imp I.ι⊑★)

𝔹ᵗ : Ty 0
𝔹ᵗ = ‵ `𝔹

ℕ! : ∀ {Δ} {μ : C.Env∼ Δ} → C._⊢_∼_ μ (‵ `ℕ) ★
ℕ! = C.id (‵ `ℕ) C.!

ℕ? : ∀ {Δ} {μ : C.Env∼ Δ} → C._⊢_∼_ μ ★ (‵ `ℕ)
ℕ? = C.？ (C.id (‵ `ℕ))

𝔹! : ∀ {Δ} {μ : C.Env∼ Δ} → C._⊢_∼_ μ (‵ `𝔹) ★
𝔹! = C.id (‵ `𝔹) C.!

𝔹? : ∀ {Δ} {μ : C.Env∼ Δ} → C._⊢_∼_ μ ★ (‵ `𝔹)
𝔹? = C.？ (C.id (‵ `𝔹))

star-seal-function : Conv↓ 1 (★ ⇒ ★) (＇ Fin.zero ⇒ ＇ Fin.zero)
star-seal-function = unseal Fin.zero ★ ↦↓ seal Fin.zero ★

star-unseal-function : Conv↑ 1 (＇ Fin.zero ⇒ ＇ Fin.zero) (★ ⇒ ★)
star-unseal-function = seal Fin.zero ★ ↦↑ unseal Fin.zero ★

star-seal-function-⊢ˣ : star-store ⊢↓[ just Fin.zero ] star-seal-function
star-seal-function-⊢ˣ = ⊢↓-⇒ˣ join-both
  (⊢↑-unsealˣ (Z∋ refl)) (⊢↓-sealˣ (Z∋ refl))

star-unseal-function-⊢ˣ :
  star-store ⊢↑[ just Fin.zero ] star-unseal-function
star-unseal-function-⊢ˣ = ⊢↑-⇒ˣ join-both
  (⊢↓-sealˣ (Z∋ refl)) (⊢↑-unsealˣ (Z∋ refl))

star-seal-round : Term 1 → Term 1
star-seal-round M = (M ↓ star-seal-function) ↑ star-unseal-function

star-seal-round-⊢ : ∀ {M}
  → ⟨ 1 , star-store , [] ⟩ ⊢ M ⦂ (★ ⇒ ★)
  → ⟨ 1 , star-store , [] ⟩ ⊢ star-seal-round M ⦂ (★ ⇒ ★)
star-seal-round-⊢ d = ⊢reveal
  (⊢↑-⇒ (⊢↓-seal (Z∋ refl)) (⊢↑-unseal (Z∋ refl)))
  (⊢conceal (⊢↓-⇒ (⊢↑-unseal (Z∋ refl))
    (⊢↓-seal (Z∋ refl))) d)

natFun⊑starFun★ :
  (‵ `ℕ ⇒ ‵ `ℕ) CTX.⊑ᵂ⟨ W★ ⟩ (★ ⇒ ★)
natFun⊑starFun★ = I.⇒⊑⇒ I.ι⊑★ I.ι⊑★

starFun⊑starFun★ : (★ ⇒ ★) CTX.⊑ᵂ⟨ W★ ⟩ (★ ⇒ ★)
starFun⊑starFun★ = I.⇒⊑⇒ I.★⊑★ I.★⊑★

nomFun⊑nomFun★ :
  (＇ Fin.zero ⇒ ＇ Fin.zero) CTX.⊑ᵂ⟨ W★ ⟩
  (＇ Fin.zero ⇒ ＇ Fin.zero)
nomFun⊑nomFun★ = I.⇒⊑⇒ I.X⊑X I.X⊑X

mixed-cast-round² : ∀ {M N}
  → W★ ∣ [] ⊢² M ⊑ N ∶ natFun⊑starFun★
  → W★ ∣ [] ⊢² cast-round M ⊑ N ∶ natFun⊑starFun★
mixed-cast-round² d = CTI.cast⊑² down
  (CTI.cast⊑² up d starFun⊑starFun★)
  natFun⊑starFun★

mixed-seal-round² : ∀ {M N}
  → W★ ∣ [] ⊢² M ⊑ N ∶ natFun⊑starFun★
  → W★ ∣ [] ⊢² seal-round M ⊑ star-seal-round N
      ∶ natFun⊑starFun★
mixed-seal-round² d =
  CTI.reveal⊑reveal² (λ _ eq → eq) rebase-X★ CTX.same-[]
    unseal-function-⊢ˣ star-unseal-function-⊢ˣ
    (CTI.conceal⊑conceal² CTX.matched-fun-conceal-target
      (λ _ eq → eq) rebase-X★ CTX.same-[]
      seal-function-⊢ˣ star-seal-function-⊢ˣ d nomFun⊑nomFun★)
    natFun⊑starFun★

bad : Term 1
bad =
  ƛ ((((` zero) ⟨ ℕ! {μ = C.idᶜ} ⟩)
    ⟨ 𝔹? {μ = C.idᶜ} ⟩)
    ⟨ 𝔹! {μ = C.idᶜ} ⟩)
    ⟨ ℕ? {μ = C.idᶜ} ⟩

bad-⊢ : ⟨ 1 , nat-store , [] ⟩ ⊢ bad ⦂ (‵ `ℕ ⇒ ‵ `ℕ)
bad-⊢ = ⊢ƛ (⊢⟨⟩ (⊢⟨⟩ (⊢⟨⟩ (⊢⟨⟩ (⊢` Z)
  ℕ!) 𝔹?) 𝔹!) ℕ?)

dynId : Term 1
dynId = ƛ (` zero)

dynId-⊢ : ⟨ 1 , star-store , [] ⟩ ⊢ dynId ⦂ (★ ⇒ ★)
dynId-⊢ = ⊢ƛ (⊢` Z)

bad⊑dynId² : W★ ∣ [] ⊢² bad ⊑ dynId ∶ natFun⊑starFun★
bad⊑dynId² =
  CTI.ƛ⊑ƛ²
    (CTI.cast⊑² ℕ?
      (CTI.cast⊑² 𝔹!
        (CTI.cast⊑² 𝔹?
          (CTI.cast⊑² ℕ!
            (CTI.x⊑x² {p = I.ι⊑★} CTX.Zʷ)
            I.★⊑★)
          I.ι⊑★)
        I.★⊑★)
      I.ι⊑★)

mixed-latent-source-fun : Term 1
mixed-latent-source-fun =
  seal-round
    (cast-round
      (seal-round (cast-round (cast-round bad))))

mixed-latent-target-fun : Term 1
mixed-latent-target-fun =
  star-seal-round (star-seal-round dynId)

mixed-latent-source-fun-⊢ :
  ⟨ 1 , nat-store , [] ⟩ ⊢ mixed-latent-source-fun
    ⦂ (‵ `ℕ ⇒ ‵ `ℕ)
mixed-latent-source-fun-⊢ =
  seal-round-⊢
    (cast-round-⊢
      (seal-round-⊢ (cast-round-⊢ (cast-round-⊢ bad-⊢))))

mixed-latent-target-fun-⊢ :
  ⟨ 1 , star-store , [] ⟩ ⊢ mixed-latent-target-fun ⦂ (★ ⇒ ★)
mixed-latent-target-fun-⊢ =
  star-seal-round-⊢ (star-seal-round-⊢ dynId-⊢)

mixed-latent-fun² :
  W★ ∣ [] ⊢² mixed-latent-source-fun
    ⊑ mixed-latent-target-fun ∶ natFun⊑starFun★
mixed-latent-fun² =
  mixed-seal-round²
    (mixed-cast-round²
      (mixed-seal-round²
        (mixed-cast-round² (mixed-cast-round² bad⊑dynId²))))

mixed-latent-source : ℕ → Term 1
mixed-latent-source n = mixed-latent-source-fun · $ (κℕ n)

mixed-latent-target : ℕ → Term 1
mixed-latent-target n =
  (mixed-latent-target-fun · ($ (κℕ n) ⟨ ℕ! {μ = C.idᶜ} ⟩))
    ⟨ ℕ? {μ = C.idᶜ} ⟩

mixed-latent-source-⊢ : ∀ n
  → ⟨ 1 , nat-store , [] ⟩ ⊢ mixed-latent-source n ⦂ ‵ `ℕ
mixed-latent-source-⊢ n =
  ⊢· mixed-latent-source-fun-⊢ (⊢$ (κℕ n))

mixed-latent-target-⊢ : ∀ n
  → ⟨ 1 , star-store , [] ⟩ ⊢ mixed-latent-target n ⦂ ‵ `ℕ
mixed-latent-target-⊢ n =
  ⊢⟨⟩
    (⊢· mixed-latent-target-fun-⊢ (⊢⟨⟩ (⊢$ (κℕ n)) ℕ!))
    ℕ?

mixed-latent² : ∀ n
  → W★ ∣ [] ⊢² mixed-latent-source n
      ⊑ mixed-latent-target n ∶ I.ι⊑ι
mixed-latent² n =
  CTI.⊑cast² ℕ?
    (CTI.·⊑·² mixed-latent-fun²
      (CTI.⊑cast² ℕ! (CTI.κ⊑κ² (κℕ n) I.ι⊑ι) I.ι⊑★))
    I.ι⊑ι

mixed-latent-source-blame : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ χ ∈ StoreChanges 1 Δ′ ]
    Σ[ trace ∈ mixed-latent-source n —↠[ χ ] blame ]
      interpretFrom nat-store 128 (mixed-latent-source n)
        ≡ blamed χ trace
mixed-latent-source-blame n = _ , _ , _ , refl

mixed-latent-target-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ χ ∈ StoreChanges 1 Δ′ ]
    Σ[ trace ∈ mixed-latent-target n —↠[ χ ] $ (κℕ n) ]
      interpretFrom star-store 128 (mixed-latent-target n)
        ≡ returned (E.result Δ′ χ ($ (κℕ n)) trace ($ (κℕ n)))
mixed-latent-target-return n = _ , _ , _ , refl
