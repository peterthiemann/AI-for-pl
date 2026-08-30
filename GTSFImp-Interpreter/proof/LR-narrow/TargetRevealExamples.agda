module proof.LR-narrow.TargetRevealExamples where

-- File Charter:
--   * Regresses pending target observations at an atomic unseal.
--   * Checks typing, reduction to a natural, and materialization at all indices.
--   * Refutes the old requirement that the revealed term already be a value.
--   * Exercises both universal peel forms in complete applications to data.

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; ∃-syntax)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import Primitives using (κℕ)
open import TyStore using (Z∋)
import TermCtx as T
open import CastTerms
open import Conversion
open import Reduction
import Eval as E
open import Interpreter
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.SlotSequence using (fresh-target-slot)
open import proof.LR-narrow.Closure using (value-imprecision-endpoints)
open import proof.LR-narrow.Constant using (constant-values-related)
open import proof.LR-narrow.ImmediateReturn using (related-values-return)
open import proof.LR-narrow.TargetReveal

target-world : World 0 1 1
target-world = impreciseBindWorld emptyWorld (‵ `ℕ)

unsealed-seven : Term 1
unsealed-seven =
  ($ (κℕ 7) ↓ seal Fin.zero (‵ `ℕ)) ↑ unseal Fin.zero (‵ `ℕ)

unsealed-seven-⊢ :
  ⟨ 1 , impreciseStore (core target-world) , [] ⟩
    ⊢ unsealed-seven ⦂ ‵ `ℕ
unsealed-seven-⊢ = ⊢reveal (⊢↑-unseal (Z∋ refl))
  (⊢conceal (⊢↓-seal (Z∋ refl)) (⊢$ (κℕ 7)))

unsealed-seven-↠ : unsealed-seven —↠[ keep ∷ [] ] $ (κℕ 7)
unsealed-seven-↠ =
    ($ (κℕ 7) ↓ seal Fin.zero (‵ `ℕ)) ↑ unseal Fin.zero (‵ `ℕ)
  —→[ keep ]⟨ pure-step (conceal-reveal ($ (κℕ 7))) ⟩
    $ (κℕ 7) ∎[]

unsealed-seven-eval :
  interpretFrom (impreciseStore (core target-world)) 1 unsealed-seven
    ≡ returned (E.result 1 (keep ∷ []) ($ (κℕ 7))
        unsealed-seven-↠ ($ (κℕ 7)))
unsealed-seven-eval = refl

unsealed-seven-not-value : Value unsealed-seven → ⊥
unsealed-seven-not-value (v ↑ ())

unsealed-seven-not-related-as-value : ∀ k {Vᴾ : Term 0}
  → ValueImprecision target-world (I.ι⊑ι {ι = `ℕ}) k
      unsealed-seven Vᴾ
  → ⊥
unsealed-seven-not-related-as-value k related =
  unsealed-seven-not-value
    (imprecise-value (value-imprecision-endpoints related))

pending-seven : ∀ k
  → PendingTargetValueRelation (fresh-target-slot emptyWorld (‵ `ℕ))
      {Aᴾ = ‵ `ℕ} {Aᴵ = ＇ Fin.zero} I.ι⊑ι
      target-world future-refl k
      ($ (κℕ 7) ↓ seal Fin.zero (‵ `ℕ)) ($ (κℕ 7))
pending-seven k = fresh-target-sealed-values {W = emptyWorld} I.ι⊑ι
  (constant-values-related {W = target-world} k (κℕ 7))

unsealed-seven-related : ∀ k
  → ComputationsRelated target-world (FutureValueRelation I.ι⊑ι) k
      unsealed-seven ($ (κℕ 7))
unsealed-seven-related k = pending-target-reveal-computations
  (fresh-target-slot emptyWorld (‵ `ℕ))
  {Aᴾ = ‵ `ℕ} {Aᴵ = ＇ Fin.zero} I.ι⊑ι
  (related-values-return ($ (κℕ 7) ↓ seal) ($ (κℕ 7))
    (λ j j≤k → pending-seven j))

-- The universal producer's two binds give a paired name followed by a
-- target-only alias.  The fresh target has only the scoped reading;
-- an ordinary insertion cannot treat it as the paired target name.

paired-then-target : World 1 2 2
paired-then-target = impreciseBindWorld
  (pairedBindWorld emptyWorld (‵ `ℕ) (‵ `ℕ) I.ι⊑ι) (＇ Fin.zero)

paired-name-not-fresh-target :
  ＇ Fin.zero ⊑ᵂ⟨ core paired-then-target ⟩ ＇ Fin.zero → ⊥
paired-name-not-fresh-target (I.alias () p)

paired-name-transparent-through-fresh-target :
  TargetTransparent paired-then-target
    (fresh-target-slot
      (pairedBindWorld emptyWorld (‵ `ℕ) (‵ `ℕ) I.ι⊑ι)
      (＇ Fin.zero))
    (＇ Fin.zero) (＇ Fin.zero)
paired-name-transparent-through-fresh-target = I.X⊑X

-- The missing scope-closing lemma is not a failing evaluation.  These
-- complete applications exercise both first-peel forms and return data.

paired-world : World 1 1 1
paired-world = pairedBindWorld emptyWorld (‵ `ℕ) (‵ `ℕ) I.ι⊑ι

identity-seven : Term 1
identity-seven =
  ((Λ (ƛ (` 0))) ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ‵ `ℕ ])
    · $ (κℕ 7)

identity-seven-⊢ : ⟨ 1 , preciseStore (core paired-world) , [] ⟩
  ⊢ identity-seven ⦂ ‵ `ℕ
identity-seven-⊢ =
  ⊢· (⊢• (⊢Λ (ƛ (` 0)) (⊢ƛ (⊢` T.Z)))) (⊢$ (κℕ 7))

identity-seven-eval : ∃[ result ]
  interpretFrom (preciseStore (core paired-world)) 20 identity-seven
    ≡ returned result
  × E.term result ≡ $ (κℕ 7)
identity-seven-eval = _ , refl , refl

revealed-identity-seven : Term 1
revealed-identity-seven =
  (((Λ (ƛ (` 0)))
      ↑ 〖 Fin.zero , ‵ `ℕ ↑ `∀ (＇ Fin.zero ⇒ ＇ Fin.zero) 〗)
    ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ‵ `ℕ ]) · $ (κℕ 7)

revealed-identity-seven-⊢ :
  ⟨ 1 , impreciseStore (core paired-world) , [] ⟩
    ⊢ revealed-identity-seven ⦂ ‵ `ℕ
revealed-identity-seven-⊢ =
  ⊢· (⊢• (⊢reveal (⊢↑-∀ (⊢↑-⇒ ⊢↓-id ⊢↑-id))
    (⊢Λ (ƛ (` 0)) (⊢ƛ (⊢` T.Z))))) (⊢$ (κℕ 7))

revealed-identity-seven-eval : ∃[ result ]
  interpretFrom (impreciseStore (core paired-world)) 20
      revealed-identity-seven ≡ returned result
  × E.term result ≡ $ (κℕ 7)
revealed-identity-seven-eval = _ , refl , refl

concealed-identity-seven : Term 1
concealed-identity-seven =
  (((Λ (ƛ (` 0)))
      ↓ makeConceal Fin.zero (‵ `ℕ) (`∀ (＇ Fin.zero ⇒ ＇ Fin.zero)))
    ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ‵ `ℕ ]) · $ (κℕ 7)

concealed-identity-seven-⊢ :
  ⟨ 1 , impreciseStore (core paired-world) , [] ⟩
    ⊢ concealed-identity-seven ⦂ ‵ `ℕ
concealed-identity-seven-⊢ =
  ⊢· (⊢• (⊢conceal (⊢↓-∀ (⊢↓-⇒ ⊢↑-id ⊢↓-id))
    (⊢Λ (ƛ (` 0)) (⊢ƛ (⊢` T.Z))))) (⊢$ (κℕ 7))

concealed-identity-seven-eval : ∃[ result ]
  interpretFrom (impreciseStore (core paired-world)) 20
      concealed-identity-seven ≡ returned result
  × E.term result ≡ $ (κℕ 7)
concealed-identity-seven-eval = _ , refl , refl
