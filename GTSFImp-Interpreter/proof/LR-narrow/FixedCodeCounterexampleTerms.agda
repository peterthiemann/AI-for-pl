module proof.LR-narrow.FixedCodeCounterexampleTerms where

-- File Charter:
--   * Concrete operational fixtures for the fixed-code counterexample.
--   * Builds two final physical scopes over empty roots where source and
--     target packets carry extensionally different constant functions.
--   * Exposes typing and data-ending evaluator witnesses only; the semantic
--     counterexample is assembled by the integrated model modules.

open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (∃-syntax; _,_)
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
open import proof.LR-narrow.GroundTagSteps using (groundProjection)
open import proof.LR-narrow.PhysicalScope

private
  seven : ℕ
  seven = suc (suc (suc (suc (suc (suc (suc zero))))))

S : PhysicalScope store-empty (suc (suc zero))
S = allocate (allocate root (‵ `ℕ)) (＇ Fin.zero ⇒ ‵ `ℕ)

T : PhysicalScope store-empty (suc (suc (suc zero)))
T = allocate (allocate (allocate root (‵ `ℕ)) (＇ Fin.zero))
  (＇ Fin.zero ⇒ ‵ `ℕ)

P : TyVar (suc (suc zero))
P = Fin.zero

X : TyVar (suc (suc zero))
X = Fin.suc Fin.zero

Q : TyVar (suc (suc (suc zero)))
Q = Fin.zero

Y : TyVar (suc (suc (suc zero)))
Y = Fin.suc Fin.zero

Z : TyVar (suc (suc (suc zero)))
Z = Fin.suc (Fin.suc Fin.zero)

entryX : scopeStore S ∋ X ⦂ ‵ `ℕ
entryX = S-bind∋ (Z∋ refl) refl

entryP : scopeStore S ∋ P ⦂ (＇ X ⇒ ‵ `ℕ)
entryP = Z∋ refl

entryY : scopeStore T ∋ Y ⦂ ＇ Z
entryY = S-bind∋ (Z∋ refl) refl

entryZ : scopeStore T ∋ Z ⦂ ‵ `ℕ
entryZ = S-bind∋ (S-bind∋ (Z∋ refl) refl) refl

entryQ : scopeStore T ∋ Q ⦂ (＇ Y ⇒ ‵ `ℕ)
entryQ = Z∋ refl

F : Term (suc (suc zero))
F = ƛ ($ (κℕ zero))

G : Term (suc (suc (suc zero)))
G = ƛ ($ (κℕ (suc zero)))

F-value : Value F
F-value = ƛ ($ (κℕ zero))

G-value : Value G
G-value = ƛ ($ (κℕ (suc zero)))

F-⊢ : ⟨ suc (suc zero) , scopeStore S , [] ⟩
  ⊢ F ⦂ (＇ X ⇒ ‵ `ℕ)
F-⊢ = ⊢ƛ (⊢$ (κℕ zero))

G-⊢ : ⟨ suc (suc (suc zero)) , scopeStore T , [] ⟩
  ⊢ G ⦂ (＇ Y ⇒ ‵ `ℕ)
G-⊢ = ⊢ƛ (⊢$ (κℕ (suc zero)))

argI : Term (suc (suc zero))
argI = $ (κℕ seven) ↓ seal X (‵ `ℕ)

argP : Term (suc (suc (suc zero)))
argP = ($ (κℕ seven) ↓ seal Z (‵ `ℕ)) ↓ seal Y (＇ Z)

argI-value : Value argI
argI-value = ($ (κℕ seven)) ↓ seal

argP-value : Value argP
argP-value = (($ (κℕ seven)) ↓ seal) ↓ seal

argI-⊢ : ⟨ suc (suc zero) , scopeStore S , [] ⟩ ⊢ argI ⦂ ＇ X
argI-⊢ = ⊢conceal (⊢↓-seal entryX) (⊢$ (κℕ seven))

argP-⊢ : ⟨ suc (suc (suc zero)) , scopeStore T , [] ⟩ ⊢ argP ⦂ ＇ Y
argP-⊢ =
  ⊢conceal (⊢↓-seal entryY)
    (⊢conceal (⊢↓-seal entryZ) (⊢$ (κℕ seven)))

sealedF : Term (suc (suc zero))
sealedF = F ↓ seal P (＇ X ⇒ ‵ `ℕ)

sealedG : Term (suc (suc (suc zero)))
sealedG = G ↓ seal Q (＇ Y ⇒ ‵ `ℕ)

sealedF-value : Value sealedF
sealedF-value = F-value ↓ seal

sealedG-value : Value sealedG
sealedG-value = G-value ↓ seal

sealedF-⊢ : ⟨ suc (suc zero) , scopeStore S , [] ⟩ ⊢ sealedF ⦂ ＇ P
sealedF-⊢ = ⊢conceal (⊢↓-seal entryP) F-⊢

sealedG-⊢ : ⟨ suc (suc (suc zero)) , scopeStore T , [] ⟩
  ⊢ sealedG ⦂ ＇ Q
sealedG-⊢ = ⊢conceal (⊢↓-seal entryQ) G-⊢

source-tag-env : C.Env∼ (suc (suc zero))
source-tag-env _ = C.X∼★

target-tag-env : C.Env∼ (suc (suc (suc zero)))
target-tag-env _ = C.X∼★

source-project-env : C.Env∼ (suc (suc zero))
source-project-env _ = C.★∼X

target-project-env : C.Env∼ (suc (suc (suc zero)))
target-project-env _ = C.★∼X

P! : source-tag-env C.⊢ ＇ P ∼ ★
P! = groundInjection (＇ P) (C.X∼★ᵍ refl)

Q! : target-tag-env C.⊢ ＇ Q ∼ ★
Q! = groundInjection (＇ Q) (C.X∼★ᵍ refl)

P? : source-project-env C.⊢ ★ ∼ ＇ P
P? = groundProjection (＇ P) (C.★∼Xᵍ refl) (C.id (＇ P)) nonstar-X

Q? : target-project-env C.⊢ ★ ∼ ＇ Q
Q? = groundProjection (＇ Q) (C.★∼Xᵍ refl) (C.id (＇ Q)) nonstar-X

source-packet : Term (suc (suc zero))
source-packet = sealedF ⟨ P! ⟩

target-packet : Term (suc (suc (suc zero)))
target-packet = sealedG ⟨ Q! ⟩

source-packet-value : Value source-packet
source-packet-value =
  sealedF-value 《 inj ⦃ Gᵍ = ＇ P ⦄
    ⦃ G∼★ = C.X∼★ᵍ refl ⦄ ⦃ Gns = nonstar-X ⦄ 》

target-packet-value : Value target-packet
target-packet-value =
  sealedG-value 《 inj ⦃ Gᵍ = ＇ Q ⦄
    ⦃ G∼★ = C.X∼★ᵍ refl ⦄ ⦃ Gns = nonstar-X ⦄ 》

source-packet-⊢ : ⟨ suc (suc zero) , scopeStore S , [] ⟩
  ⊢ source-packet ⦂ ★
source-packet-⊢ = ⊢⟨⟩ sealedF-⊢ P!

target-packet-⊢ : ⟨ suc (suc (suc zero)) , scopeStore T , [] ⟩
  ⊢ target-packet ⦂ ★
target-packet-⊢ = ⊢⟨⟩ sealedG-⊢ Q!

source-projection : Term (suc (suc zero))
source-projection = source-packet ⟨ P? ⟩

target-projection : Term (suc (suc (suc zero)))
target-projection = target-packet ⟨ Q? ⟩

source-projection-⊢ : ⟨ suc (suc zero) , scopeStore S , [] ⟩
  ⊢ source-projection ⦂ ＇ P
source-projection-⊢ = ⊢⟨⟩ source-packet-⊢ P?

target-projection-⊢ : ⟨ suc (suc (suc zero)) , scopeStore T , [] ⟩
  ⊢ target-projection ⦂ ＇ Q
target-projection-⊢ = ⊢⟨⟩ target-packet-⊢ Q?

direct-source : Term (suc (suc zero))
direct-source = F · argI

direct-target : Term (suc (suc (suc zero)))
direct-target = G · argP

direct-source-⊢ : ⟨ suc (suc zero) , scopeStore S , [] ⟩
  ⊢ direct-source ⦂ ‵ `ℕ
direct-source-⊢ = ⊢· F-⊢ argI-⊢

direct-target-⊢ : ⟨ suc (suc (suc zero)) , scopeStore T , [] ⟩
  ⊢ direct-target ⦂ ‵ `ℕ
direct-target-⊢ = ⊢· G-⊢ argP-⊢

source-runtime : Term (suc (suc zero))
source-runtime =
  (source-projection ↑ unseal P (＇ X ⇒ ‵ `ℕ)) · argI

target-runtime : Term (suc (suc (suc zero)))
target-runtime =
  (target-projection ↑ unseal Q (＇ Y ⇒ ‵ `ℕ)) · argP

source-runtime-⊢ : ⟨ suc (suc zero) , scopeStore S , [] ⟩
  ⊢ source-runtime ⦂ ‵ `ℕ
source-runtime-⊢ =
  ⊢· (⊢reveal (⊢↑-unseal entryP) source-projection-⊢) argI-⊢

target-runtime-⊢ : ⟨ suc (suc (suc zero)) , scopeStore T , [] ⟩
  ⊢ target-runtime ⦂ ‵ `ℕ
target-runtime-⊢ =
  ⊢· (⊢reveal (⊢↑-unseal entryQ) target-projection-⊢) argP-⊢

source-projection-return : ∃[ tr ] interpretFrom (scopeStore S)
    (suc zero) source-projection
    ≡ returned (E.result (suc (suc zero)) (keep ∷ [])
      sealedF tr sealedF-value)
source-projection-return = _ , refl

target-projection-return : ∃[ tr ] interpretFrom (scopeStore T)
    (suc zero) target-projection
    ≡ returned (E.result (suc (suc (suc zero))) (keep ∷ [])
      sealedG tr sealedG-value)
target-projection-return = _ , refl

argI-return : ∃[ tr ] interpretFrom (scopeStore S) (suc zero)
    (argI ↑ unseal X (‵ `ℕ))
    ≡ returned (E.result (suc (suc zero)) (keep ∷ [])
      ($ (κℕ seven)) tr ($ (κℕ seven)))
argI-return = _ , refl

argP-return : ∃[ tr ] interpretFrom (scopeStore T) (suc (suc zero))
    ((argP ↑ unseal Y (＇ Z)) ↑ unseal Z (‵ `ℕ))
    ≡ returned (E.result (suc (suc (suc zero))) (keep ∷ keep ∷ [])
      ($ (κℕ seven)) tr ($ (κℕ seven)))
argP-return = _ , refl

direct-source-return : ∃[ tr ] interpretFrom (scopeStore S)
    (suc zero) direct-source
    ≡ returned (E.result (suc (suc zero)) (keep ∷ [])
      ($ (κℕ zero)) tr ($ (κℕ zero)))
direct-source-return = _ , refl

direct-target-return : ∃[ tr ] interpretFrom (scopeStore T)
    (suc zero) direct-target
    ≡ returned (E.result (suc (suc (suc zero))) (keep ∷ [])
      ($ (κℕ (suc zero))) tr ($ (κℕ (suc zero))))
direct-target-return = _ , refl

source-runtime-return : ∃[ tr ] interpretFrom (scopeStore S)
    (suc (suc (suc zero))) source-runtime
    ≡ returned (E.result (suc (suc zero))
      (keep ∷ keep ∷ keep ∷ [])
      ($ (κℕ zero)) tr ($ (κℕ zero)))
source-runtime-return = _ , refl

target-runtime-return : ∃[ tr ] interpretFrom (scopeStore T)
    (suc (suc (suc zero))) target-runtime
    ≡ returned (E.result (suc (suc (suc zero)))
      (keep ∷ keep ∷ keep ∷ [])
      ($ (κℕ (suc zero))) tr ($ (κℕ (suc zero))))
target-runtime-return = _ , refl
