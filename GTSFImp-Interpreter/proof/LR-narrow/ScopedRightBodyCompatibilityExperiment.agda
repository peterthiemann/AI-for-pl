module proof.LR-narrow.ScopedRightBodyCompatibilityExperiment where

-- File Charter:
--   * Right-only runtime regression for body-local reveal over a fresh
--     precise slot and an older shared natural slot.
--   * The source endpoint stays unconverted; the target endpoint uses the
--     generated reveal for the body `((α⇒X)⇒(α⇒X))`.
--   * Checks exact typing, reduction chains, and evaluator results at a
--     first-order natural endpoint. Exercises both structural compatibility
--     APIs at arbitrary independent futures, plus concrete shifted pivots.

open import Data.List using ([])
open import Data.Nat using (ℕ; zero)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans)

open import Types
open import TyStore
open import TermCtx using (Z)
open import CastTerms
open import Conversion
open import Reduction
open import Primitives using (κℕ)
open import Interpreter
import Eval as Eval
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedBodyInterpretation
  using (BodyFragment; variable-body; arrow-body)
open import proof.LR-narrow.ScopedConversionTransport
  using (scope↑; scope↓; scope↑-cong; scope↑-generated)
open import proof.LR-narrow.TypeRenamingComposition using (pack↑)
open import proof.LR-narrow.ScopedIdentity as SI
import proof.LR-narrow.ScopedBodyInterpretation as BI
import proof.LR-narrow.ScopedConversionCompatibility as CC
import proof.LR-narrow.ScopedRightBodyConversion as RBC
import proof.LR-narrow.ScopedRightBodyCompatibility as RCompat

source-store : TyStore 1
source-store = store-bind store-empty (‵ `ℕ)

target-store : TyStore 2
target-store = store-bind source-store (‵ `ℕ)

source-var : TyVar 1
source-var = Fin.zero

fresh-var : TyVar 2
fresh-var = Fin.zero

target-var : TyVar 2
target-var = Fin.suc Fin.zero

fixtureTy : Ty 2
fixtureTy =
  ((＇ fresh-var ⇒ ＇ target-var) ⇒
   (＇ fresh-var ⇒ ＇ target-var))

publicFixtureTy : Ty 2
publicFixtureTy =
  ((‵ `ℕ ⇒ ＇ target-var) ⇒
   (‵ `ℕ ⇒ ＇ target-var))

source-argumentTy : Ty 1
source-argumentTy = ‵ `ℕ ⇒ ＇ source-var

target-argumentTy : Ty 2
target-argumentTy = ＇ fresh-var ⇒ ＇ target-var

public-argumentTy : Ty 2
public-argumentTy = ‵ `ℕ ⇒ ＇ target-var

target-old-entry : target-store ∋ target-var ⦂ ‵ `ℕ
target-old-entry = S-bind∋ (Z∋ refl) refl

source-entry : source-store ∋ source-var ⦂ ‵ `ℕ
source-entry = Z∋ refl

module New = Model source-store target-store
module I = BI.Interpretation source-store target-store
module C = CC.Compatibility source-store target-store
module BC = RBC.Conversions source-store target-store
module K = RCompat.Compatibility source-store target-store

argument-body : BodyFragment {n = 2} (＇ fresh-var ⇒ ＇ target-var)
argument-body = arrow-body variable-body variable-body

fixture-body : BodyFragment {n = 2}
  ((＇ fresh-var ⇒ ＇ target-var) ⇒
   (＇ fresh-var ⇒ ＇ target-var))
fixture-body = arrow-body argument-body argument-body

η : TyVar 2 → BC.RightVariableConversion
η Fin.zero = BC.right-slot New.natural Fin.zero (Z∋ refl)
η (Fin.suc Fin.zero) =
  BC.unchanged
    (New.nominal New.natural source-var target-var source-entry
      target-old-entry)

abstract-argument : New.ScopedType
abstract-argument =
  I.interpret-body argument-body (λ X → BC.abstract-type (η X))

public-argument : New.ScopedType
public-argument = I.interpret-body argument-body (λ X → BC.public-type (η X))

source-identity : Term 1
source-identity = ƛ (` zero)

source-identity-value : Value source-identity
source-identity-value = ƛ (` zero)

source-identity-⊢ : ⟨ 1 , source-store , [] ⟩
  ⊢ source-identity ⦂ (source-argumentTy ⇒ source-argumentTy)
source-identity-⊢ = ⊢ƛ (⊢` Z)

source-argument : Term 1
source-argument = ƛ (` zero ↓ seal source-var (‵ `ℕ))

source-argument-value : Value source-argument
source-argument-value = ƛ (` zero ↓ seal source-var (‵ `ℕ))

source-argument-⊢ : ⟨ 1 , source-store , [] ⟩
  ⊢ source-argument ⦂ source-argumentTy
source-argument-⊢ = ⊢ƛ (⊢conceal (⊢↓-seal (Z∋ refl)) (⊢` Z))

source-runtime : ℕ → Term 1
source-runtime n =
  (((source-identity · source-argument) · $ (κℕ n))
    ↑ unseal source-var (‵ `ℕ))

source-runtime-⊢ : ∀ n → ⟨ 1 , source-store , [] ⟩
  ⊢ source-runtime n ⦂ ‵ `ℕ
source-runtime-⊢ n = ⊢reveal (⊢↑-unseal (Z∋ refl))
  (⊢· (⊢· source-identity-⊢ source-argument-⊢) (⊢$ (κℕ n)))

source-runtime-↠ : ∀ n → source-runtime n
  —↠[ keep ∷ keep ∷ keep ∷ [] ] $ (κℕ n)
source-runtime-↠ n =
    source-runtime n
  —→[ keep ]⟨ ξ-reveal
      (ξ-·₁ (pure-step (β source-argument-value)) refl) refl ⟩
    ((source-argument · $ (κℕ n)) ↑ unseal source-var (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal (pure-step (β ($ (κℕ n)))) refl ⟩
    (($ (κℕ n) ↓ seal source-var (‵ `ℕ)) ↑ unseal source-var (‵ `ℕ))
  —→[ keep ]⟨ pure-step (conceal-reveal ($ (κℕ n))) ⟩
    $ (κℕ n) ∎[]

source-runtime-return : ∀ n
  → interpretFrom source-store 3 (source-runtime n)
      ≡ returned (Eval.result 1
        (keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ n)) (source-runtime-↠ n) ($ (κℕ n)))
source-runtime-return n = refl

target-reveal : Conv↑ 2 fixtureTy publicFixtureTy
target-reveal = BC.revealᴾ fixture-body η

target-reveal-generated : target-reveal ≡ 〖 fresh-var , ‵ `ℕ ↑ fixtureTy 〗
target-reveal-generated = refl

target-reveal-typed : target-store ⊢↑ target-reveal
target-reveal-typed = ⊢↑-⇒
  (⊢↓-⇒ (⊢↑-unseal (Z∋ refl)) ⊢↓-id)
  (⊢↑-⇒ (⊢↓-seal (Z∋ refl)) ⊢↑-id)

target-identity : Term 2
target-identity = (ƛ (` zero)) ↑ target-reveal

target-identity-⊢ : ⟨ 2 , target-store , [] ⟩
  ⊢ target-identity ⦂ publicFixtureTy
target-identity-⊢ = ⊢reveal target-reveal-typed (⊢ƛ (⊢` Z))

target-argument : Term 2
target-argument = ƛ (` zero ↓ seal target-var (‵ `ℕ))

target-argument-value : Value target-argument
target-argument-value = ƛ (` zero ↓ seal target-var (‵ `ℕ))

target-argument-⊢ : ⟨ 2 , target-store , [] ⟩
  ⊢ target-argument ⦂ public-argumentTy
target-argument-⊢ =
  ⊢ƛ (⊢conceal (⊢↓-seal target-old-entry) (⊢` Z))

target-runtime : ℕ → Term 2
target-runtime n =
  (((target-identity · target-argument) · $ (κℕ n))
    ↑ unseal target-var (‵ `ℕ))

target-runtime-⊢ : ∀ n → ⟨ 2 , target-store , [] ⟩
  ⊢ target-runtime n ⦂ ‵ `ℕ
target-runtime-⊢ n = ⊢reveal (⊢↑-unseal target-old-entry)
  (⊢· (⊢· target-identity-⊢ target-argument-⊢) (⊢$ (κℕ n)))

target-runtime-↠ : ∀ n → target-runtime n
  —↠[ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷
       keep ∷ [] ] $ (κℕ n)
target-runtime-↠ n =
    target-runtime n
  —→[ keep ]⟨ ξ-reveal
      (ξ-·₁ (pure-step
        (β-reveal-⇒ (ƛ (` zero)) target-argument-value)) refl) refl ⟩
    (((((ƛ (` zero)) · (target-argument ↓ makeConceal fresh-var
          (‵ `ℕ) target-argumentTy))
        ↑ 〖 fresh-var , ‵ `ℕ ↑ target-argumentTy 〗) · $ (κℕ n))
      ↑ unseal target-var (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (ξ-·₁ (ξ-reveal
        (pure-step (β (target-argument-value ↓ fun))) refl) refl) refl ⟩
    ((((target-argument ↓ makeConceal fresh-var (‵ `ℕ) target-argumentTy)
        ↑ 〖 fresh-var , ‵ `ℕ ↑ target-argumentTy 〗) · $ (κℕ n))
      ↑ unseal target-var (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (pure-step (β-reveal-⇒ (target-argument-value ↓ fun) ($ (κℕ n))))
      refl ⟩
    ((((target-argument ↓ makeConceal fresh-var (‵ `ℕ) target-argumentTy)
        · ($ (κℕ n) ↓ seal fresh-var (‵ `ℕ)))
        ↑ id↑ (＇ target-var))
      ↑ unseal target-var (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (ξ-reveal (pure-step
        (β-conceal-⇒ target-argument-value (($ (κℕ n)) ↓ seal)))
        refl) refl ⟩
    ((((target-argument ·
        (($ (κℕ n) ↓ seal fresh-var (‵ `ℕ))
          ↑ unseal fresh-var (‵ `ℕ)))
        ↓ id↓ (＇ target-var))
        ↑ id↑ (＇ target-var))
      ↑ unseal target-var (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (ξ-reveal (ξ-conceal
        (ξ-·₂ target-argument-value
          (pure-step (conceal-reveal ($ (κℕ n)))) refl) refl) refl) refl ⟩
    ((((target-argument · $ (κℕ n))
        ↓ id↓ (＇ target-var))
        ↑ id↑ (＇ target-var))
      ↑ unseal target-var (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (ξ-reveal
        (ξ-conceal (pure-step (β ($ (κℕ n)))) refl) refl) refl ⟩
    (((($ (κℕ n) ↓ seal target-var (‵ `ℕ))
        ↓ id↓ (＇ target-var))
        ↑ id↑ (＇ target-var))
      ↑ unseal target-var (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (ξ-reveal (pure-step (id-conceal (($ (κℕ n)) ↓ seal))) refl) refl ⟩
    ((($ (κℕ n) ↓ seal target-var (‵ `ℕ))
        ↑ id↑ (＇ target-var))
      ↑ unseal target-var (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (pure-step (id-reveal (($ (κℕ n)) ↓ seal))) refl ⟩
    (($ (κℕ n) ↓ seal target-var (‵ `ℕ))
      ↑ unseal target-var (‵ `ℕ))
  —→[ keep ]⟨ pure-step (conceal-reveal ($ (κℕ n))) ⟩
    $ (κℕ n) ∎[]

target-runtime-return : ∀ n
  → interpretFrom target-store 9 (target-runtime n)
      ≡ returned (Eval.result 2
        (keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep
          ∷ keep ∷ [])
        ($ (κℕ n)) (target-runtime-↠ n) ($ (κℕ n)))
target-runtime-return n = refl

abstract-identity-observed : ∀ {Δᴵ Δᴾ}
    {S : PhysicalScope source-store Δᴵ} {T : PhysicalScope target-store Δᴾ}
    (p : ScopeFuture root S) (q : ScopeFuture root T) k
  → New.ObservedComputations
      (I.interpret-body fixture-body (λ X → BC.abstract-type (η X)))
      S T k (liftTerm p (ƛ (` zero))) (liftTerm q (ƛ (` zero)))
abstract-identity-observed p q k =
  C.values-observed
    (I.interpret-body fixture-body (λ X → BC.abstract-type (η X)))
    (New.future-closed
      (I.interpret-body fixture-body (λ X → BC.abstract-type (η X)))
      p q (SI.identity-related abstract-argument k))

public-identity-observed : ∀ {Δᴵ Δᴾ}
    {S : PhysicalScope source-store Δᴵ} {T : PhysicalScope target-store Δᴾ}
    (p : ScopeFuture root S) (q : ScopeFuture root T) k
  → New.ObservedComputations
      (I.interpret-body fixture-body (λ X → BC.public-type (η X)))
      S T k (liftTerm p (ƛ (` zero))) (liftTerm q (ƛ (` zero)))
public-identity-observed p q k =
  C.values-observed
    (I.interpret-body fixture-body (λ X → BC.public-type (η X)))
    (New.future-closed
      (I.interpret-body fixture-body (λ X → BC.public-type (η X)))
      p q (SI.identity-related public-argument k))

right-reveal-identity-observed : ∀ {Δᴵ Δᴾ}
    {S : PhysicalScope source-store Δᴵ} {T : PhysicalScope target-store Δᴾ}
    (p : ScopeFuture root S) (q : ScopeFuture root T) k
  → New.ObservedComputations
      (I.interpret-body fixture-body (λ X → BC.public-type (η X)))
      S T k
      (liftTerm p (ƛ (` zero)))
      (liftTerm q (ƛ (` zero)) ↑ scope↑ T (BC.revealᴾ fixture-body η))
right-reveal-identity-observed p q k =
  K.right-reveal-observed fixture-body η (abstract-identity-observed p q k)

right-conceal-identity-observed : ∀ {Δᴵ Δᴾ}
    {S : PhysicalScope source-store Δᴵ} {T : PhysicalScope target-store Δᴾ}
    (p : ScopeFuture root S) (q : ScopeFuture root T) k
  → New.ObservedComputations
      (I.interpret-body fixture-body (λ X → BC.abstract-type (η X)))
      S T k
      (liftTerm p (ƛ (` zero)))
      (liftTerm q (ƛ (` zero)) ↓ scope↓ T (BC.concealᴾ fixture-body η))
right-conceal-identity-observed p q k =
  K.right-conceal-observed fixture-body η (public-identity-observed p q k)

one-more-source : PhysicalScope source-store 2
one-more-source = allocate root (‵ `ℕ)

two-more-target : PhysicalScope target-store 4
two-more-target = allocate (allocate root (‵ `ℕ)) (‵ `ℕ)

target-reveal-generated-two-more : pack↑
    (scope↑ two-more-target (BC.revealᴾ fixture-body η))
  ≡ pack↑ 〖 Fin.suc (Fin.suc Fin.zero) , ‵ `ℕ
      ↑ ((＇ Fin.suc (Fin.suc Fin.zero)
            ⇒ ＇ Fin.suc (Fin.suc (Fin.suc Fin.zero))) ⇒
         (＇ Fin.suc (Fin.suc Fin.zero)
            ⇒ ＇ Fin.suc (Fin.suc (Fin.suc Fin.zero)))) 〗
target-reveal-generated-two-more =
  trans
    (scope↑-cong two-more-target (cong pack↑ target-reveal-generated))
    (scope↑-generated two-more-target fresh-var (‵ `ℕ) fixtureTy)

right-reveal-identity-two-more : ∀ k
  → New.ObservedComputations
      (I.interpret-body fixture-body (λ X → BC.public-type (η X)))
      one-more-source two-more-target k (ƛ (` zero))
      ((ƛ (` zero)) ↑ 〖 Fin.suc (Fin.suc Fin.zero) , ‵ `ℕ
        ↑ ((＇ Fin.suc (Fin.suc Fin.zero)
              ⇒ ＇ Fin.suc (Fin.suc (Fin.suc Fin.zero))) ⇒
           (＇ Fin.suc (Fin.suc Fin.zero)
              ⇒ ＇ Fin.suc (Fin.suc (Fin.suc Fin.zero)))) 〗)
right-reveal-identity-two-more k =
  right-reveal-identity-observed (grow stay) (grow (grow stay)) k
