module proof.LR-narrow.RepeatedSealExamples where

-- File Charter:
--   * Executable regressions for repeated nonidentity seal/unseal conversion
--     cycles. These are CTI/runtime examples only, not LR validation.
--   * S1 uses a three-name representation chain; S2 uses a structural
--     function conversion; S3 uses a higher-order body mentioning an old name.
--   * Every exported program has typing evidence and a data-ending evaluator
--     companion.

open import Data.List using (_∷_; [])
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (Σ-syntax; _,_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import TermCtx using (Z)
open import Consistency using (_⊢_∼_; idᶜ; id; _!; ？_)
open import CastTerms
open import Conversion
open import Primitives using (κℕ; addℕ; δ-add)
open import Reduction
open import Interpreter
import Imprecision as Imp
import Eval as E
open import proof.DGG.CtxImp using
  (World; StoreRepImp; world; store-rep-imp; sameWorldRebaseAt;
   rebase-varᴸ; rebase-varᴿ; same-[]; _⊑ᵂ⟨_⟩_)
import proof.DGG.CtxImp as CTX
import proof.DGG.CastTermImprecision as CTI
open CTI using (_∣_⊢²_⊑_∶_)
import proof.DGG.Examples2 as Ex2

ℕ!₁ : idᶜ {Δ = 1} ⊢ ‵ `ℕ ∼ ★
ℕ!₁ = id (‵ `ℕ) !

ℕ?₁ : idᶜ {Δ = 1} ⊢ ★ ∼ ‵ `ℕ
ℕ?₁ = ？ (id (‵ `ℕ))

ℕ!₃ : idᶜ {Δ = 3} ⊢ ‵ `ℕ ∼ ★
ℕ!₃ = id (‵ `ℕ) !

ℕ?₃ : idᶜ {Δ = 3} ⊢ ★ ∼ ‵ `ℕ
ℕ?₃ = ？ (id (‵ `ℕ))

same-rebase : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
  → CTX.RebaseAt (Ex2.reflWorld Σ) (Ex2.reflWorld Σ) X X
same-rebase {Σ = Σ} {X = X} =
  sameWorldRebaseAt refl
    (store-rep-imp
      (Ex2.reflTy² {Σ = Σ} (CTX.resolveVar Σ X)))

reveal-same : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {M N : Term Δ} {A B : Ty Δ} {c : Conv↑ Δ A B}
  → Σ ⊢↑[ just X ] c
  → Ex2.reflWorld Σ ∣ [] ⊢² M ⊑ N ∶ Ex2.reflTy² {Σ = Σ} A
  → Ex2.reflWorld Σ ∣ [] ⊢² M ↑ c ⊑ N ↑ c ∶
      Ex2.reflTy² {Σ = Σ} B
reveal-same {Σ = Σ} {X = X} {B = B} c⊢ M² =
  CTI.reveal⊑reveal² (λ _ eq → eq) (same-rebase {Σ = Σ} {X = X})
    same-[] c⊢ c⊢ M² (Ex2.reflTy² {Σ = Σ} B)

conceal-same : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {M N : Term Δ} {A B : Ty Δ} {c : Conv↓ Δ A B}
  → CTX.MatchedConcealPartnerOK (Ex2.reflWorld Σ) M c (just X) N
  → Σ ⊢↓[ just X ] c
  → Ex2.reflWorld Σ ∣ [] ⊢² M ⊑ N ∶ Ex2.reflTy² {Σ = Σ} A
  → Ex2.reflWorld Σ ∣ [] ⊢² M ↓ c ⊑ N ↓ c ∶
      Ex2.reflTy² {Σ = Σ} B
conceal-same {Σ = Σ} {X = X} {B = B} ok c⊢ M² =
  CTI.conceal⊑conceal² ok (λ _ eq → eq)
    (same-rebase {Σ = Σ} {X = X}) same-[] c⊢ c⊢ M²
    (Ex2.reflTy² {Σ = Σ} B)

------------------------------------------------------------------------
-- Common stores and conversions
------------------------------------------------------------------------

X₁ : TyVar 1
X₁ = Fin.zero

one-name-store : TyStore 1
one-name-store = store-bind store-empty (‵ `ℕ)

one-name-world : World 1 1 1
one-name-world = Ex2.reflWorld one-name-store

one-name-entry : one-name-store ∋ X₁ ⦂ ‵ `ℕ
one-name-entry = Z∋ refl

X↓ℕ : Conv↓ 1 (‵ `ℕ) (＇ X₁)
X↓ℕ = seal X₁ (‵ `ℕ)

X↑ℕ : Conv↑ 1 (＇ X₁) (‵ `ℕ)
X↑ℕ = unseal X₁ (‵ `ℕ)

X↓ℕ-⊢ : one-name-store ⊢↓ X↓ℕ
X↓ℕ-⊢ = ⊢↓-seal one-name-entry

X↑ℕ-⊢ : one-name-store ⊢↑ X↑ℕ
X↑ℕ-⊢ = ⊢↑-unseal one-name-entry

X↓ℕ-⊢ˣ : one-name-store ⊢↓[ just X₁ ] X↓ℕ
X↓ℕ-⊢ˣ = ⊢↓-sealˣ one-name-entry

X↑ℕ-⊢ˣ : one-name-store ⊢↑[ just X₁ ] X↑ℕ
X↑ℕ-⊢ˣ = ⊢↑-unsealˣ one-name-entry

X⇒X↑ℕ⇒ℕ : Conv↑ 1 (＇ X₁ ⇒ ＇ X₁) (‵ `ℕ ⇒ ‵ `ℕ)
X⇒X↑ℕ⇒ℕ = X↓ℕ ↦↑ X↑ℕ

ℕ⇒ℕ↓X⇒X : Conv↓ 1 (‵ `ℕ ⇒ ‵ `ℕ) (＇ X₁ ⇒ ＇ X₁)
ℕ⇒ℕ↓X⇒X = X↑ℕ ↦↓ X↓ℕ

X⇒X↑ℕ⇒ℕ-⊢ : one-name-store ⊢↑ X⇒X↑ℕ⇒ℕ
X⇒X↑ℕ⇒ℕ-⊢ = ⊢↑-⇒ X↓ℕ-⊢ X↑ℕ-⊢

ℕ⇒ℕ↓X⇒X-⊢ : one-name-store ⊢↓ ℕ⇒ℕ↓X⇒X
ℕ⇒ℕ↓X⇒X-⊢ = ⊢↓-⇒ X↑ℕ-⊢ X↓ℕ-⊢

X⇒X↑ℕ⇒ℕ-⊢ˣ : one-name-store ⊢↑[ just X₁ ] X⇒X↑ℕ⇒ℕ
X⇒X↑ℕ⇒ℕ-⊢ˣ = ⊢↑-⇒ˣ join-both X↓ℕ-⊢ˣ X↑ℕ-⊢ˣ

ℕ⇒ℕ↓X⇒X-⊢ˣ : one-name-store ⊢↓[ just X₁ ] ℕ⇒ℕ↓X⇒X
ℕ⇒ℕ↓X⇒X-⊢ˣ = ⊢↓-⇒ˣ join-both X↑ℕ-⊢ˣ X↓ℕ-⊢ˣ

one-name-rebase : CTX.RebaseAt one-name-world one-name-world X₁ X₁
one-name-rebase =
  sameWorldRebaseAt refl
    (store-rep-imp (Ex2.reflTy² {Σ = one-name-store} (‵ `ℕ)))

------------------------------------------------------------------------
-- S1. Three-name representation chain, repeated roundtrips to data.
------------------------------------------------------------------------

X₃ Y₃ Z₃ : TyVar 3
X₃ = Fin.suc (Fin.suc Fin.zero)
Y₃ = Fin.suc Fin.zero
Z₃ = Fin.zero

chain-store : TyStore 3
chain-store =
  store-bind
    (store-bind (store-bind store-empty (‵ `ℕ)) (＇ Fin.zero))
    (＇ Fin.zero)

chain-world : World 3 3 3
chain-world = Ex2.reflWorld chain-store

chain-X-entry : chain-store ∋ X₃ ⦂ ‵ `ℕ
chain-X-entry = S-bind∋ (S-bind∋ (Z∋ refl) refl) refl

chain-Y-entry : chain-store ∋ Y₃ ⦂ ＇ X₃
chain-Y-entry = S-bind∋ (Z∋ refl) refl

chain-Z-entry : chain-store ∋ Z₃ ⦂ ＇ Y₃
chain-Z-entry = Z∋ refl

chain-seal-X : Conv↓ 3 (‵ `ℕ) (＇ X₃)
chain-seal-X = seal X₃ (‵ `ℕ)

chain-unseal-X : Conv↑ 3 (＇ X₃) (‵ `ℕ)
chain-unseal-X = unseal X₃ (‵ `ℕ)

chain-seal-Y : Conv↓ 3 (＇ X₃) (＇ Y₃)
chain-seal-Y = seal Y₃ (＇ X₃)

chain-unseal-Y : Conv↑ 3 (＇ Y₃) (＇ X₃)
chain-unseal-Y = unseal Y₃ (＇ X₃)

chain-seal-Z : Conv↓ 3 (＇ Y₃) (＇ Z₃)
chain-seal-Z = seal Z₃ (＇ Y₃)

chain-unseal-Z : Conv↑ 3 (＇ Z₃) (＇ Y₃)
chain-unseal-Z = unseal Z₃ (＇ Y₃)

chain-seal-X-⊢ˣ : chain-store ⊢↓[ just X₃ ] chain-seal-X
chain-seal-X-⊢ˣ = ⊢↓-sealˣ chain-X-entry

chain-unseal-X-⊢ˣ : chain-store ⊢↑[ just X₃ ] chain-unseal-X
chain-unseal-X-⊢ˣ = ⊢↑-unsealˣ chain-X-entry

chain-seal-Y-⊢ˣ : chain-store ⊢↓[ just Y₃ ] chain-seal-Y
chain-seal-Y-⊢ˣ = ⊢↓-sealˣ chain-Y-entry

chain-unseal-Y-⊢ˣ : chain-store ⊢↑[ just Y₃ ] chain-unseal-Y
chain-unseal-Y-⊢ˣ = ⊢↑-unsealˣ chain-Y-entry

chain-seal-Z-⊢ˣ : chain-store ⊢↓[ just Z₃ ] chain-seal-Z
chain-seal-Z-⊢ˣ = ⊢↓-sealˣ chain-Z-entry

chain-unseal-Z-⊢ˣ : chain-store ⊢↑[ just Z₃ ] chain-unseal-Z
chain-unseal-Z-⊢ˣ = ⊢↑-unsealˣ chain-Z-entry

chain-cycle : Term 3 → Term 3
chain-cycle M =
  (((((M ↓ chain-seal-X) ↓ chain-seal-Y) ↓ chain-seal-Z)
    ↑ chain-unseal-Z) ↑ chain-unseal-Y) ↑ chain-unseal-X

chain-cycle-⊢ : ∀ {M}
  → ⟨ 3 , chain-store , [] ⟩ ⊢ M ⦂ ‵ `ℕ
  → ⟨ 3 , chain-store , [] ⟩ ⊢ chain-cycle M ⦂ ‵ `ℕ
chain-cycle-⊢ M⊢ =
  ⊢reveal (⊢↑-unseal chain-X-entry)
    (⊢reveal (⊢↑-unseal chain-Y-entry)
      (⊢reveal (⊢↑-unseal chain-Z-entry)
        (⊢conceal (⊢↓-seal chain-Z-entry)
          (⊢conceal (⊢↓-seal chain-Y-entry)
            (⊢conceal (⊢↓-seal chain-X-entry) M⊢)))))

chain-payload : ℕ → Term 3
chain-payload n = $ (κℕ n) ⊕[ addℕ ] $ (κℕ 1)

chain-payload-⊢ : ∀ n → ⟨ 3 , chain-store , [] ⟩
  ⊢ chain-payload n ⦂ ‵ `ℕ
chain-payload-⊢ n = ⊢⊕ addℕ (⊢$ (κℕ n)) (⊢$ (κℕ 1))

chain-payload² : ∀ n
  → chain-world ∣ [] ⊢² chain-payload n ⊑ chain-payload n ∶
      Ex2.reflTy² {Σ = chain-store} (‵ `ℕ)
chain-payload² n =
  CTI.⊕⊑⊕² addℕ
    (CTI.κ⊑κ² (κℕ n) (Ex2.reflTy² {Σ = chain-store} (‵ `ℕ)))
    (CTI.κ⊑κ² (κℕ 1) (Ex2.reflTy² {Σ = chain-store} (‵ `ℕ)))
    (Ex2.reflTy² {Σ = chain-store} (‵ `ℕ))

s1-source : ℕ → Term 3
s1-source n = chain-cycle (chain-cycle (chain-cycle (chain-payload n)))

s1-target : ℕ → Term 3
s1-target n = s1-source n ⟨ ℕ!₃ ⟩ ⟨ ℕ?₃ ⟩

s1-source-⊢ : ∀ n → ⟨ 3 , chain-store , [] ⟩ ⊢ s1-source n ⦂ ‵ `ℕ
s1-source-⊢ n =
  chain-cycle-⊢ (chain-cycle-⊢ (chain-cycle-⊢ (chain-payload-⊢ n)))

s1-target-⊢ : ∀ n → ⟨ 3 , chain-store , [] ⟩ ⊢ s1-target n ⦂ ‵ `ℕ
s1-target-⊢ n = ⊢⟨⟩ (⊢⟨⟩ (s1-source-⊢ n) ℕ!₃) ℕ?₃

chain-three-cycles : ℕ → Term 3
chain-three-cycles n = chain-cycle (chain-cycle (chain-cycle ($ (κℕ n))))

chain-three-cycles-⊢ : ∀ n
  → ⟨ 3 , chain-store , [] ⟩ ⊢ chain-three-cycles n ⦂ ‵ `ℕ
chain-three-cycles-⊢ n =
  chain-cycle-⊢ (chain-cycle-⊢ (chain-cycle-⊢ (⊢$ (κℕ n))))

chain-cycle² : ∀ {M}
  → chain-world ∣ [] ⊢² M ⊑ M ∶ Ex2.reflTy² {Σ = chain-store} (‵ `ℕ)
  → chain-world ∣ [] ⊢² chain-cycle M ⊑ chain-cycle M ∶
      Ex2.reflTy² {Σ = chain-store} (‵ `ℕ)
chain-cycle² M² =
  reveal-same chain-unseal-X-⊢ˣ
    (reveal-same chain-unseal-Y-⊢ˣ
      (reveal-same chain-unseal-Z-⊢ˣ
        (conceal-same (CTX.matched-seal-nonstar nonstar-X)
          chain-seal-Z-⊢ˣ
          (conceal-same (CTX.matched-seal-nonstar nonstar-X)
            chain-seal-Y-⊢ˣ
            (conceal-same (CTX.matched-seal-nonstar nonstar-ι)
              chain-seal-X-⊢ˣ M²)))))

chain-three-cycles² : ∀ n
  → chain-world ∣ [] ⊢² chain-three-cycles n ⊑ chain-three-cycles n ∶
      Ex2.reflTy² {Σ = chain-store} (‵ `ℕ)
chain-three-cycles² n =
  chain-cycle² (chain-cycle²
    (chain-cycle²
      (CTI.κ⊑κ² (κℕ n)
        (Ex2.reflTy² {Σ = chain-store} (‵ `ℕ)))))

s1-source² : ∀ n
  → chain-world ∣ [] ⊢² s1-source n ⊑ s1-source n ∶
      Ex2.reflTy² {Σ = chain-store} (‵ `ℕ)
s1-source² n = chain-cycle² (chain-cycle² (chain-cycle² (chain-payload² n)))

s1-pair² : ∀ n
  → chain-world ∣ [] ⊢² s1-source n ⊑ s1-target n ∶
      Ex2.reflTy² {Σ = chain-store} (‵ `ℕ)
s1-pair² n =
  CTI.⊑cast² ℕ?₃
    (CTI.⊑cast² ℕ!₃
      (s1-source² n)
      Imp.ι⊑★)
    (Ex2.reflTy² {Σ = chain-store} (‵ `ℕ))

s1-source-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 3 Δ′ ]
    Σ[ trace ∈ s1-source n —↠[ changes ] $ (κℕ (n + 1)) ]
      interpretFrom chain-store 20 (s1-source n)
        ≡ returned
            (E.result Δ′ changes ($ (κℕ (n + 1))) trace ($ (κℕ (n + 1))))
s1-source-return n = _ , _ , _ , refl

s1-target-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 3 Δ′ ]
    Σ[ trace ∈ s1-target n —↠[ changes ] $ (κℕ (n + 1)) ]
      interpretFrom chain-store 30 (s1-target n)
        ≡ returned
            (E.result Δ′ changes ($ (κℕ (n + 1))) trace ($ (κℕ (n + 1))))
s1-target-return n = _ , _ , _ , refl

chain-three-cycles-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 3 Δ′ ]
    Σ[ trace ∈ chain-three-cycles n —↠[ changes ] $ (κℕ n) ]
      interpretFrom chain-store 18 (chain-three-cycles n)
        ≡ returned (E.result Δ′ changes ($ (κℕ n)) trace ($ (κℕ n)))
chain-three-cycles-return n = _ , _ , _ , refl

------------------------------------------------------------------------
-- S2. Structural function conversion through X↦ℕ, applied to data.
------------------------------------------------------------------------

add-one : Term 1
add-one = ƛ ((` 0) ⊕[ addℕ ] $ (κℕ 1))

add-one-⊢ : ⟨ 1 , one-name-store , [] ⟩
  ⊢ add-one ⦂ ‵ `ℕ ⇒ ‵ `ℕ
add-one-⊢ = ⊢ƛ (⊢⊕ addℕ (⊢` Z) (⊢$ (κℕ 1)))

function-two-cycles : Term 1
function-two-cycles =
  ((add-one ↓ ℕ⇒ℕ↓X⇒X) ↑ X⇒X↑ℕ⇒ℕ
    ↓ ℕ⇒ℕ↓X⇒X) ↑ X⇒X↑ℕ⇒ℕ

function-two-cycles-⊢ : ⟨ 1 , one-name-store , [] ⟩
  ⊢ function-two-cycles ⦂ ‵ `ℕ ⇒ ‵ `ℕ
function-two-cycles-⊢ =
  ⊢reveal X⇒X↑ℕ⇒ℕ-⊢
    (⊢conceal ℕ⇒ℕ↓X⇒X-⊢
      (⊢reveal X⇒X↑ℕ⇒ℕ-⊢
        (⊢conceal ℕ⇒ℕ↓X⇒X-⊢ add-one-⊢)))

add-one² :
  one-name-world ∣ [] ⊢² add-one ⊑ add-one ∶
    Ex2.reflTy² {Σ = one-name-store} (‵ `ℕ ⇒ ‵ `ℕ)
add-one² =
  CTI.ƛ⊑ƛ²
    (CTI.⊕⊑⊕² addℕ
      (CTI.x⊑x² CTX.Zʷ)
      (CTI.κ⊑κ² (κℕ 1)
        (Ex2.reflTy² {Σ = one-name-store} (‵ `ℕ)))
      (Ex2.reflTy² {Σ = one-name-store} (‵ `ℕ)))

function-two-cycles² :
  one-name-world ∣ [] ⊢² function-two-cycles ⊑ function-two-cycles ∶
    Ex2.reflTy² {Σ = one-name-store} (‵ `ℕ ⇒ ‵ `ℕ)
function-two-cycles² =
  reveal-same X⇒X↑ℕ⇒ℕ-⊢ˣ
    (conceal-same CTX.matched-fun-conceal-target ℕ⇒ℕ↓X⇒X-⊢ˣ
      (reveal-same X⇒X↑ℕ⇒ℕ-⊢ˣ
        (conceal-same CTX.matched-fun-conceal-target ℕ⇒ℕ↓X⇒X-⊢ˣ
          add-one²)))

function-two-cycles-call : ℕ → Term 1
function-two-cycles-call n = function-two-cycles · $ (κℕ n)

function-two-cycles-call-⊢ : ∀ n → ⟨ 1 , one-name-store , [] ⟩
  ⊢ function-two-cycles-call n ⦂ ‵ `ℕ
function-two-cycles-call-⊢ n =
  ⊢· function-two-cycles-⊢ (⊢$ (κℕ n))

function-two-cycles-call² : ∀ n
  → one-name-world ∣ [] ⊢² function-two-cycles-call n
      ⊑ function-two-cycles-call n ∶
      Ex2.reflTy² {Σ = one-name-store} (‵ `ℕ)
function-two-cycles-call² n =
  CTI.·⊑·² function-two-cycles²
    (CTI.κ⊑κ² (κℕ n)
      (Ex2.reflTy² {Σ = one-name-store} (‵ `ℕ)))

s2-source : ℕ → Term 1
s2-source = function-two-cycles-call

s2-target : ℕ → Term 1
s2-target n =
  (function-two-cycles · (($ (κℕ n) ⟨ ℕ!₁ ⟩) ⟨ ℕ?₁ ⟩)
    ⟨ ℕ!₁ ⟩) ⟨ ℕ?₁ ⟩

s2-source-⊢ : ∀ n → ⟨ 1 , one-name-store , [] ⟩ ⊢ s2-source n ⦂ ‵ `ℕ
s2-source-⊢ = function-two-cycles-call-⊢

s2-target-⊢ : ∀ n → ⟨ 1 , one-name-store , [] ⟩ ⊢ s2-target n ⦂ ‵ `ℕ
s2-target-⊢ n =
  ⊢⟨⟩
    (⊢⟨⟩
      (⊢· function-two-cycles-⊢
        (⊢⟨⟩ (⊢⟨⟩ (⊢$ (κℕ n)) ℕ!₁) ℕ?₁))
      ℕ!₁)
    ℕ?₁

s2-pair² : ∀ n
  → one-name-world ∣ [] ⊢² s2-source n ⊑ s2-target n ∶
      Ex2.reflTy² {Σ = one-name-store} (‵ `ℕ)
s2-pair² n =
  CTI.⊑cast² ℕ?₁
    (CTI.⊑cast² ℕ!₁
      (CTI.·⊑·² function-two-cycles²
        (CTI.⊑cast² ℕ?₁
          (CTI.⊑cast² ℕ!₁
            (CTI.κ⊑κ² (κℕ n)
              (Ex2.reflTy² {Σ = one-name-store} (‵ `ℕ)))
            Imp.ι⊑★)
          (Ex2.reflTy² {Σ = one-name-store} (‵ `ℕ))))
      Imp.ι⊑★)
    (Ex2.reflTy² {Σ = one-name-store} (‵ `ℕ))

s2-source-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 1 Δ′ ]
    Σ[ trace ∈ s2-source n —↠[ changes ] $ (κℕ (n + 1)) ]
      interpretFrom one-name-store 18 (s2-source n)
        ≡ returned
            (E.result Δ′ changes ($ (κℕ (n + 1))) trace ($ (κℕ (n + 1))))
s2-source-return n = _ , _ , _ , refl

s2-target-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 1 Δ′ ]
    Σ[ trace ∈ s2-target n —↠[ changes ] $ (κℕ (n + 1)) ]
      interpretFrom one-name-store 24 (s2-target n)
        ≡ returned
            (E.result Δ′ changes ($ (κℕ (n + 1))) trace ($ (κℕ (n + 1))))
s2-target-return n = _ , _ , _ , refl

function-two-cycles-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 1 Δ′ ]
    Σ[ trace ∈ function-two-cycles-call n —↠[ changes ] $ (κℕ (n + 1)) ]
      interpretFrom one-name-store 18 (function-two-cycles-call n)
        ≡ returned
            (E.result Δ′ changes ($ (κℕ (n + 1))) trace ($ (κℕ (n + 1))))
function-two-cycles-return n = _ , _ , _ , refl

------------------------------------------------------------------------
-- S3. Higher-order producer mentioning old X, then apply to data.
------------------------------------------------------------------------

higher-X-body : Ty 1
higher-X-body = (＇ X₁ ⇒ ＇ X₁) ⇒ (＇ X₁ ⇒ ＇ X₁)

higher-X : Term 1
higher-X = ƛ (` 0)

higher-X-⊢ : ⟨ 1 , one-name-store , [] ⟩ ⊢ higher-X ⦂ higher-X-body
higher-X-⊢ = ⊢ƛ (⊢` Z)

higher-X↑ℕ : Conv↑ 1 higher-X-body
  ((‵ `ℕ ⇒ ‵ `ℕ) ⇒ (‵ `ℕ ⇒ ‵ `ℕ))
higher-X↑ℕ = ℕ⇒ℕ↓X⇒X ↦↑ X⇒X↑ℕ⇒ℕ

higher-ℕ↓X : Conv↓ 1
  ((‵ `ℕ ⇒ ‵ `ℕ) ⇒ (‵ `ℕ ⇒ ‵ `ℕ)) higher-X-body
higher-ℕ↓X = X⇒X↑ℕ⇒ℕ ↦↓ ℕ⇒ℕ↓X⇒X

higher-X↑ℕ-⊢ : one-name-store ⊢↑ higher-X↑ℕ
higher-X↑ℕ-⊢ = ⊢↑-⇒ ℕ⇒ℕ↓X⇒X-⊢ X⇒X↑ℕ⇒ℕ-⊢

higher-ℕ↓X-⊢ : one-name-store ⊢↓ higher-ℕ↓X
higher-ℕ↓X-⊢ = ⊢↓-⇒ X⇒X↑ℕ⇒ℕ-⊢ ℕ⇒ℕ↓X⇒X-⊢

higher-X↑ℕ-⊢ˣ : one-name-store ⊢↑[ just X₁ ] higher-X↑ℕ
higher-X↑ℕ-⊢ˣ =
  ⊢↑-⇒ˣ join-both ℕ⇒ℕ↓X⇒X-⊢ˣ X⇒X↑ℕ⇒ℕ-⊢ˣ

higher-ℕ↓X-⊢ˣ : one-name-store ⊢↓[ just X₁ ] higher-ℕ↓X
higher-ℕ↓X-⊢ˣ =
  ⊢↓-⇒ˣ join-both X⇒X↑ℕ⇒ℕ-⊢ˣ ℕ⇒ℕ↓X⇒X-⊢ˣ

higher-two-cycles : Term 1
higher-two-cycles =
  ((higher-X ↑ higher-X↑ℕ) ↓ higher-ℕ↓X
    ↑ higher-X↑ℕ) ↓ higher-ℕ↓X

higher-two-cycles-⊢ : ⟨ 1 , one-name-store , [] ⟩
  ⊢ higher-two-cycles ⦂ higher-X-body
higher-two-cycles-⊢ =
  ⊢conceal higher-ℕ↓X-⊢
    (⊢reveal higher-X↑ℕ-⊢
      (⊢conceal higher-ℕ↓X-⊢
        (⊢reveal higher-X↑ℕ-⊢ higher-X-⊢)))

higher-X² :
  one-name-world ∣ [] ⊢² higher-X ⊑ higher-X ∶
    Ex2.reflTy² {Σ = one-name-store} higher-X-body
higher-X² = CTI.ƛ⊑ƛ² (CTI.x⊑x² CTX.Zʷ)

higher-two-cycles² :
  one-name-world ∣ [] ⊢² higher-two-cycles ⊑ higher-two-cycles ∶
    Ex2.reflTy² {Σ = one-name-store} higher-X-body
higher-two-cycles² =
  conceal-same CTX.matched-fun-conceal-target higher-ℕ↓X-⊢ˣ
    (reveal-same higher-X↑ℕ-⊢ˣ
      (conceal-same CTX.matched-fun-conceal-target higher-ℕ↓X-⊢ˣ
        (reveal-same higher-X↑ℕ-⊢ˣ higher-X²)))

higher-two-cycles-call : ℕ → Term 1
higher-two-cycles-call n =
  ((higher-two-cycles · (add-one ↓ ℕ⇒ℕ↓X⇒X))
    · ($ (κℕ n) ↓ X↓ℕ)) ↑ X↑ℕ

higher-two-cycles-call-⊢ : ∀ n → ⟨ 1 , one-name-store , [] ⟩
  ⊢ higher-two-cycles-call n ⦂ ‵ `ℕ
higher-two-cycles-call-⊢ n =
  ⊢reveal X↑ℕ-⊢
    (⊢· (⊢· higher-two-cycles-⊢
      (⊢conceal ℕ⇒ℕ↓X⇒X-⊢ add-one-⊢))
      (⊢conceal X↓ℕ-⊢ (⊢$ (κℕ n))))

higher-two-cycles-call² : ∀ n
  → one-name-world ∣ [] ⊢² higher-two-cycles-call n
      ⊑ higher-two-cycles-call n ∶
      Ex2.reflTy² {Σ = one-name-store} (‵ `ℕ)
higher-two-cycles-call² n =
  reveal-same X↑ℕ-⊢ˣ
    (CTI.·⊑·²
      (CTI.·⊑·² higher-two-cycles²
        (conceal-same CTX.matched-fun-conceal-target ℕ⇒ℕ↓X⇒X-⊢ˣ
          add-one²))
      (conceal-same (CTX.matched-seal-nonstar nonstar-ι) X↓ℕ-⊢ˣ
        (CTI.κ⊑κ² (κℕ n)
          (Ex2.reflTy² {Σ = one-name-store} (‵ `ℕ)))))

s3-source : ℕ → Term 1
s3-source = higher-two-cycles-call

s3-target : ℕ → Term 1
s3-target n =
  (((higher-two-cycles · (add-one ↓ ℕ⇒ℕ↓X⇒X))
    · ((($ (κℕ n) ⟨ ℕ!₁ ⟩) ⟨ ℕ?₁ ⟩) ↓ X↓ℕ)) ↑ X↑ℕ
    ⟨ ℕ!₁ ⟩) ⟨ ℕ?₁ ⟩

s3-source-⊢ : ∀ n → ⟨ 1 , one-name-store , [] ⟩ ⊢ s3-source n ⦂ ‵ `ℕ
s3-source-⊢ = higher-two-cycles-call-⊢

s3-target-⊢ : ∀ n → ⟨ 1 , one-name-store , [] ⟩ ⊢ s3-target n ⦂ ‵ `ℕ
s3-target-⊢ n =
  ⊢⟨⟩
    (⊢⟨⟩
      (⊢reveal X↑ℕ-⊢
        (⊢· (⊢· higher-two-cycles-⊢
          (⊢conceal ℕ⇒ℕ↓X⇒X-⊢ add-one-⊢))
          (⊢conceal X↓ℕ-⊢
            (⊢⟨⟩ (⊢⟨⟩ (⊢$ (κℕ n)) ℕ!₁) ℕ?₁))))
      ℕ!₁)
    ℕ?₁

s3-pair² : ∀ n
  → one-name-world ∣ [] ⊢² s3-source n ⊑ s3-target n ∶
      Ex2.reflTy² {Σ = one-name-store} (‵ `ℕ)
s3-pair² n =
  CTI.⊑cast² ℕ?₁
    (CTI.⊑cast² ℕ!₁
      (reveal-same X↑ℕ-⊢ˣ
        (CTI.·⊑·²
          (CTI.·⊑·² higher-two-cycles²
            (conceal-same CTX.matched-fun-conceal-target
              ℕ⇒ℕ↓X⇒X-⊢ˣ add-one²))
          (conceal-same (CTX.matched-seal-nonstar nonstar-ι) X↓ℕ-⊢ˣ
            (CTI.⊑cast² ℕ?₁
              (CTI.⊑cast² ℕ!₁
                (CTI.κ⊑κ² (κℕ n)
                  (Ex2.reflTy² {Σ = one-name-store} (‵ `ℕ)))
                Imp.ι⊑★)
              (Ex2.reflTy² {Σ = one-name-store} (‵ `ℕ))))))
      Imp.ι⊑★)
    (Ex2.reflTy² {Σ = one-name-store} (‵ `ℕ))

s3-source-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 1 Δ′ ]
    Σ[ trace ∈ s3-source n —↠[ changes ] $ (κℕ (n + 1)) ]
      interpretFrom one-name-store 40 (s3-source n)
        ≡ returned
            (E.result Δ′ changes ($ (κℕ (n + 1))) trace ($ (κℕ (n + 1))))
s3-source-return n = _ , _ , _ , refl

s3-target-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 1 Δ′ ]
    Σ[ trace ∈ s3-target n —↠[ changes ] $ (κℕ (n + 1)) ]
      interpretFrom one-name-store 50 (s3-target n)
        ≡ returned
            (E.result Δ′ changes ($ (κℕ (n + 1))) trace ($ (κℕ (n + 1))))
s3-target-return n = _ , _ , _ , refl

higher-two-cycles-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 1 Δ′ ]
    Σ[ trace ∈ higher-two-cycles-call n —↠[ changes ] $ (κℕ (n + 1)) ]
      interpretFrom one-name-store 40 (higher-two-cycles-call n)
        ≡ returned
            (E.result Δ′ changes ($ (κℕ (n + 1))) trace ($ (κℕ (n + 1))))
higher-two-cycles-return n = _ , _ , _ , refl
