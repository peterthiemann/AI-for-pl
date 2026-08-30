module proof.LR-narrow.DynamicWrapperExamples where

-- File Charter:
--   * Adversarial CTI examples for universal identity wrappers around a
--     dynamic payload producer.
--   * Keeps the examples operational: closed programs instantiate the
--     universal, apply a natural argument, project the dynamic result back to
--     natural data, and record executable evaluator witnesses.
--   * This file only exercises existing syntax, CTI, and evaluator behavior;
--     it does not assume or change a semantic closure theorem. The final
--     data observations also instantiate the existing scoped computation LR.

open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ; zero)
open import Data.Product using (Σ-syntax; _,_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import TermCtx using (Z)
open import Consistency using (_⊢_∼_; idᶜ; instᵐ; genᵐ; id; _!; ？_)
open import CastTerms
open import Conversion
open import Imprecision using
  (X⊑X; X⊑★; ι⊑ι; ι⊑★; ★⊑★; ⇒⊑⇒; ∀⊑; ∀⊑∀)
open import Primitives using (κℕ)
open import Reduction
open import Interpreter
import Eval as E
import proof.DGG.CastTermImprecision as CTI
open CTI using (_∣_⊢²_⊑_∶_)
import proof.DGG.CtxImp as CTX
import proof.DGG.Examples2 as Ex2
open import LR-narrow.LogicalRelation using (same-natural)
open import proof.LR-narrow.PhysicalScope using (root)
import proof.LR-narrow.ScopedBehavior as Scoped

W₀ : CTX.World 0 0 0
W₀ = Ex2.reflWorld store-empty

payload-body : Ty 1
payload-body = ＇ Fin.zero ⇒ ★

payload∀ : Ty 0
payload∀ = `∀ payload-body

payload-reveal : Conv↑ 0 payload∀ payload∀
payload-reveal = `∀↑ id↑ payload-body

X! : instᵐ (idᶜ {Δ = 0}) ⊢ ＇ Fin.zero ∼ ★
X! = id (＇ Fin.zero) !

ℕ? : idᶜ {Δ = 0} ⊢ ★ ∼ ‵ `ℕ
ℕ? = ？ (id (‵ `ℕ))

ℕ! : idᶜ {Δ = 0} ⊢ ‵ `ℕ ∼ ★
ℕ! = id (‵ `ℕ) !

X? : genᵐ (idᶜ {Δ = 0}) ⊢ ★ ∼ ＇ Fin.zero
X? = ？ (id (＇ Fin.zero))

payload-function : Term 0
payload-function = Λ (ƛ (` zero ⟨ X! ⟩))

payload-function-value : Value payload-function
payload-function-value = Λ (ƛ (` zero ⟨ X! ⟩))

payload-function-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ payload-function ⦂ payload∀
payload-function-⊢ = ⊢Λ (ƛ (` zero ⟨ X! ⟩) )
  (⊢ƛ (⊢⟨⟩ (⊢` Z) X!))

payload∀⊑payload∀ : payload∀ CTX.⊑ᵂ⟨ W₀ ⟩ payload∀
payload∀⊑payload∀ =
  ∀⊑∀ (⇒⊑⇒ (Ex2.X⊑X-lift² {W = W₀}) ★⊑★)

payload-refl² :
  W₀ ∣ [] ⊢² payload-function
    ⊑ payload-function ∶ payload∀⊑payload∀
payload-refl² =
  CTI.Λ⊑Λ² CTX.lift-[] (ƛ (` zero ⟨ X! ⟩)) (ƛ (` zero ⟨ X! ⟩))
    (CTI.ƛ⊑ƛ² {pA = Ex2.X⊑X-lift² {W = W₀}} {pB = ★⊑★}
      (CTI.cast⊑cast² X! X!
        (CTI.x⊑x² {p = Ex2.X⊑X-lift² {W = W₀}} CTX.Zʷ)
        ★⊑★))
    payload∀⊑payload∀

payload-reveal² :
  W₀ ∣ [] ⊢² payload-function
    ⊑ payload-function ↑ payload-reveal ∶ payload∀⊑payload∀
payload-reveal² =
  CTI.⊑reveal² (λ _ eq → eq) CTX.rebase-idᴿ CTX.same-[]
    (⊢↑-∀-idˣ ⊢↑-idˣ) payload-refl² payload∀⊑payload∀

payload-inst⊑payload-inst : (payload-body [ ‵ `ℕ ]ᵗ)
  CTX.⊑ᵂ⟨ W₀ ⟩ (payload-body [ ‵ `ℕ ]ᵗ)
payload-inst⊑payload-inst = ⇒⊑⇒ ι⊑ι ★⊑★

payload-inst⊑★⇒★ : (payload-body [ ‵ `ℕ ]ᵗ)
  CTX.⊑ᵂ⟨ W₀ ⟩ (★ ⇒ ★)
payload-inst⊑★⇒★ = ⇒⊑⇒ ι⊑★ ★⊑★

payload-call⊑payload-call : ∀ n
  → W₀ ∣ [] ⊢²
      (payload-function ⦂∀ payload-body [ ‵ `ℕ ]) · $ (κℕ n)
    ⊑ ((payload-function ↑ payload-reveal)
        ⦂∀ payload-body [ ‵ `ℕ ]) · $ (κℕ n)
    ∶ ★⊑★
payload-call⊑payload-call n =
  CTI.·⊑·²
    (CTI.•⊑•² payload∀⊑payload∀ payload-reveal² ι⊑ι
      payload-inst⊑payload-inst)
    (CTI.κ⊑κ² (κℕ n) ι⊑ι)

payload-runtime : ℕ → Term 0
payload-runtime n =
  ((payload-function ⦂∀ payload-body [ ‵ `ℕ ])
    · $ (κℕ n)) ⟨ ℕ? ⟩

payload-runtime-⊢ : ∀ n
  → ⟨ 0 , store-empty , [] ⟩ ⊢ payload-runtime n ⦂ ‵ `ℕ
payload-runtime-⊢ n =
  ⊢⟨⟩ (⊢· (⊢• payload-function-⊢) (⊢$ (κℕ n))) ℕ?

payload-runtime-blame : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 0 Δ′ ]
    Σ[ trace ∈ payload-runtime n —↠[ changes ] blame ]
      interpretFrom store-empty 8 (payload-runtime n)
        ≡ blamed changes trace
payload-runtime-blame n = _ , _ , _ , refl

wrapped-payload-runtime : ℕ → Term 0
wrapped-payload-runtime n =
  (((payload-function ↑ payload-reveal) ⦂∀ payload-body [ ‵ `ℕ ])
    · $ (κℕ n)) ⟨ ℕ? ⟩

payload-runtime² : ∀ n
  → W₀ ∣ [] ⊢² payload-runtime n
      ⊑ wrapped-payload-runtime n ∶ ι⊑ι
payload-runtime² n =
  CTI.cast⊑cast² ℕ? ℕ? (payload-call⊑payload-call n) ι⊑ι

wrapped-payload-runtime-⊢ : ∀ n
  → ⟨ 0 , store-empty , [] ⟩ ⊢ wrapped-payload-runtime n ⦂ ‵ `ℕ
wrapped-payload-runtime-⊢ n =
  ⊢⟨⟩ (⊢·
    (⊢• (⊢reveal (⊢↑-∀ ⊢↑-id) payload-function-⊢))
    (⊢$ (κℕ n))) ℕ?

wrapped-payload-runtime-blame : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 0 Δ′ ]
    Σ[ trace ∈ wrapped-payload-runtime n —↠[ changes ] blame ]
      interpretFrom store-empty 16 (wrapped-payload-runtime n)
        ≡ blamed changes trace
wrapped-payload-runtime-blame n = _ , _ , _ , refl

check-body : Ty 1
check-body = ＇ Fin.zero ⇒ ＇ Fin.zero

check∀ : Ty 0
check∀ = `∀ check-body

check-reveal : Conv↑ 0 check∀ check∀
check-reveal = `∀↑ id↑ check-body

check-function : Term 0
check-function = Λ (ƛ ((` zero ⟨ X! ⟩) ⟨ X? ⟩))

check-function-value : Value check-function
check-function-value = Λ (ƛ ((` zero ⟨ X! ⟩) ⟨ X? ⟩))

check-function-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ check-function ⦂ check∀
check-function-⊢ = ⊢Λ (ƛ ((` zero ⟨ X! ⟩) ⟨ X? ⟩))
  (⊢ƛ (⊢⟨⟩ (⊢⟨⟩ (⊢` Z) X!) X?))

check∀⊑check∀ : check∀ CTX.⊑ᵂ⟨ W₀ ⟩ check∀
check∀⊑check∀ = Ex2.∀X⇒X⊑∀X⇒X² {W = W₀}

check-refl² :
  W₀ ∣ [] ⊢² check-function ⊑ check-function ∶ check∀⊑check∀
check-refl² =
  CTI.Λ⊑Λ² CTX.lift-[] (ƛ ((` zero ⟨ X! ⟩) ⟨ X? ⟩))
    (ƛ ((` zero ⟨ X! ⟩) ⟨ X? ⟩))
    (CTI.ƛ⊑ƛ² {pA = Ex2.X⊑X-lift² {W = W₀}}
      {pB = Ex2.X⊑X-lift² {W = W₀}}
      (CTI.cast⊑cast² X? X?
        (CTI.cast⊑cast² X! X!
          (CTI.x⊑x² {p = Ex2.X⊑X-lift² {W = W₀}} CTX.Zʷ)
          ★⊑★)
        (Ex2.X⊑X-lift² {W = W₀})))
    check∀⊑check∀

check-reveal² :
  W₀ ∣ [] ⊢² check-function
    ⊑ check-function ↑ check-reveal ∶ check∀⊑check∀
check-reveal² =
  CTI.⊑reveal² (λ _ eq → eq) CTX.rebase-idᴿ CTX.same-[]
    (⊢↑-∀-idˣ ⊢↑-idˣ) check-refl² check∀⊑check∀

check-inst⊑check-inst : (check-body [ ‵ `ℕ ]ᵗ)
  CTX.⊑ᵂ⟨ W₀ ⟩ (check-body [ ‵ `ℕ ]ᵗ)
check-inst⊑check-inst = ⇒⊑⇒ ι⊑ι ι⊑ι

check-runtime : ℕ → Term 0
check-runtime n =
  (check-function ⦂∀ check-body [ ‵ `ℕ ]) · $ (κℕ n)

wrapped-check-runtime : ℕ → Term 0
wrapped-check-runtime n =
  ((check-function ↑ check-reveal) ⦂∀ check-body [ ‵ `ℕ ])
    · $ (κℕ n)

check-runtime² : ∀ n
  → W₀ ∣ [] ⊢² check-runtime n ⊑ wrapped-check-runtime n ∶ ι⊑ι
check-runtime² n =
  CTI.·⊑·²
    (CTI.•⊑•² check∀⊑check∀ check-reveal² ι⊑ι
      check-inst⊑check-inst)
    (CTI.κ⊑κ² (κℕ n) ι⊑ι)

check-runtime-⊢ : ∀ n
  → ⟨ 0 , store-empty , [] ⟩ ⊢ check-runtime n ⦂ ‵ `ℕ
check-runtime-⊢ n =
  ⊢· (⊢• check-function-⊢) (⊢$ (κℕ n))

wrapped-check-runtime-⊢ : ∀ n
  → ⟨ 0 , store-empty , [] ⟩ ⊢ wrapped-check-runtime n ⦂ ‵ `ℕ
wrapped-check-runtime-⊢ n =
  ⊢· (⊢• (⊢reveal (⊢↑-∀ ⊢↑-id) check-function-⊢))
    (⊢$ (κℕ n))

check-runtime-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 0 Δ′ ]
    Σ[ trace ∈ check-runtime n —↠[ changes ] $ (κℕ n) ]
      interpretFrom store-empty 8 (check-runtime n)
        ≡ returned (E.result Δ′ changes ($ (κℕ n)) trace ($ (κℕ n)))
check-runtime-return n = _ , _ , _ , refl

wrapped-check-runtime-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 0 Δ′ ]
    Σ[ trace ∈ wrapped-check-runtime n —↠[ changes ] $ (κℕ n) ]
      interpretFrom store-empty 16 (wrapped-check-runtime n)
        ≡ returned (E.result Δ′ changes ($ (κℕ n)) trace ($ (κℕ n)))
wrapped-check-runtime-return n = _ , _ , _ , refl

erased-target : Term 0
erased-target = ƛ (` zero)

erased-target-value : Value erased-target
erased-target-value = ƛ (` zero)

erased-target-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ erased-target ⦂ ★ ⇒ ★
erased-target-⊢ = ⊢ƛ (⊢` Z)

payload∀⊑★⇒★ : payload∀ CTX.⊑ᵂ⟨ W₀ ⟩ (★ ⇒ ★)
payload∀⊑★⇒★ =
  ∀⊑ nonvar-fun (∈-fun-left var-∈)
    (⇒⊑⇒ (X⊑★ refl) ★⊑★)

erased-body⊑ : payload-body
  CTX.⊑ᵂ⟨ CTX.liftWorldLeft X⊑★ W₀ ⟩ (★ ⇒ ★)
erased-body⊑ = ⇒⊑⇒ (X⊑★ refl) ★⊑★

payload-erased² :
  W₀ ∣ [] ⊢² payload-function
    ⊑ erased-target ∶ payload∀⊑★⇒★
payload-erased² =
  CTI.Λ⊑² nonvar-fun (∈-fun-left var-∈) CTX.liftᴸ-[]
    (ƛ (` zero ⟨ X! ⟩)) erased-target-⊢
    (CTI.ƛ⊑ƛ² {pA = X⊑★ refl} {pB = ★⊑★}
      (CTI.cast⊑² X!
        (CTI.x⊑x² {p = X⊑★ refl} CTX.Zʷ) ★⊑★))
    payload∀⊑★⇒★

erased-inst-call² : ∀ n
  → W₀ ∣ [] ⊢²
      (payload-function ⦂∀ payload-body [ ‵ `ℕ ]) · $ (κℕ n)
    ⊑ erased-target · ($ (κℕ n) ⟨ ℕ! ⟩)
    ∶ ★⊑★
erased-inst-call² n =
  CTI.·⊑·²
    (CTI.•⊑² payload∀⊑★⇒★ payload-erased² ι⊑★
      payload-inst⊑★⇒★)
    (CTI.⊑cast² ℕ! (CTI.κ⊑κ² (κℕ n) ι⊑ι) ι⊑★)

erased-runtime : ℕ → Term 0
erased-runtime n =
  (erased-target · ($ (κℕ n) ⟨ ℕ! ⟩)) ⟨ ℕ? ⟩

erased-runtime² : ∀ n
  → W₀ ∣ [] ⊢² payload-runtime n ⊑ erased-runtime n ∶ ι⊑ι
erased-runtime² n =
  CTI.cast⊑cast² ℕ? ℕ? (erased-inst-call² n) ι⊑ι

erased-runtime-⊢ : ∀ n
  → ⟨ 0 , store-empty , [] ⟩ ⊢ erased-runtime n ⦂ ‵ `ℕ
erased-runtime-⊢ n =
  ⊢⟨⟩ (⊢· erased-target-⊢ (⊢⟨⟩ (⊢$ (κℕ n)) ℕ!)) ℕ?

erased-runtime-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 0 Δ′ ]
    Σ[ trace ∈ erased-runtime n —↠[ changes ] $ (κℕ n) ]
      interpretFrom store-empty 4 (erased-runtime n)
        ≡ returned (E.result Δ′ changes ($ (κℕ n)) trace ($ (κℕ n)))
erased-runtime-return n = _ , _ , _ , refl

module Observations = Scoped.Model store-empty store-empty

-- Scoped observations use imprecise-first argument order. These theorems
-- concern the complete data-observing runs, not a general dynamic-value LR.

payload-runtime-observed : ∀ n k
  → Observations.ObservedComputations Observations.natural root root k
      (wrapped-payload-runtime n) (payload-runtime n)
payload-runtime-observed n k =
  Observations.observed-from-right-blame {gas = 8} (payload-runtime-blame n)

check-runtime-observed : ∀ n k
  → Observations.ObservedComputations Observations.natural root root k
      (wrapped-check-runtime n) (check-runtime n)
check-runtime-observed n k
    with check-runtime-return n | wrapped-check-runtime-return n
check-runtime-observed n k
    | Δᴾ , χᴾ , traceᴾ , retᴾ | Δᴵ , χᴵ , traceᴵ , retᴵ =
  Observations.observed-from-returns {gasᴵ = 16} {gasᴾ = 8}
    retᴵ retᴾ (same-natural n)

erased-runtime-observed : ∀ n k
  → Observations.ObservedComputations Observations.natural root root k
      (erased-runtime n) (payload-runtime n)
erased-runtime-observed n k =
  Observations.observed-from-right-blame {gas = 8} (payload-runtime-blame n)
