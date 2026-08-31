module proof.LR-narrow.ExistentialPayloadCounterexample where

-- File Charter:
--   * Refutes selecting an arbitrary SemanticType as a dynamic packet's
--     payload meaning, even with relatedness and both endpoint equalities.
--   * A coarse natural meaning satisfies every current SemanticType field
--     but relates 0 to 1; real tag/project computations distinguish them.
--   * This does not refute canonical natural/dataDynamic or A+B+C′. It
--     requires fixing payload interpretations, not existentially choosing
--     them from the unrestricted record of semantic invariants.

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Nat using (ℕ; zero; z≤n; s≤s)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym) renaming (subst to subst≡; subst₂ to subst₂≡)

open import Types
open import TyStore
open import CastTerms
open import Primitives using (κℕ)
open import Reduction using (keep; []; _∷_)
open import Interpreter
import Eval as E
import Consistency as C
open import LR-narrow.LogicalRelation using (SameBaseValue; groundInjection)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.IntegratedModel
open import proof.LR-narrow.IntegratedProjection using (natural-projection)
open import proof.LR-narrow.TargetEvaluation using (return-result-unique)

open Model store-empty store-empty
open Worlds

data AnyNaturals {ΔI ΔP} : Term ΔI → Term ΔP → Set where
  any-naturals : ∀ n m → AnyNaturals ($ (κℕ n)) ($ (κℕ m))

coarseNatural : SemanticType
coarseNatural = record
  { impreciseTy = ‵ `ℕ
  ; preciseTy = ‵ `ℕ
  ; related = λ W k → AnyNaturals
  ; imprecise-value = λ { (any-naturals n m) → $ (κℕ n) }
  ; precise-value = λ { (any-naturals n m) → $ (κℕ m) }
  ; imprecise-typed = λ { {S = S} (any-naturals n m) →
      subst≡ (λ A → ⟨ _ , scopeStore S , [] ⟩ ⊢ $ (κℕ n) ⦂ A)
        (sym (scope-natural S)) (⊢$ (κℕ n)) }
  ; precise-typed = λ { {T = T} (any-naturals n m) →
      subst≡ (λ A → ⟨ _ , scopeStore T , [] ⟩ ⊢ $ (κℕ m) ⦂ A)
        (sym (scope-natural T)) (⊢$ (κℕ m)) }
  ; downward = λ j≤k r → r
  ; future-closed = λ { p q ext (any-naturals n m) →
      subst₂≡ AnyNaturals
        (sym (lift-constant p (κℕ n))) (sym (lift-constant q (κℕ m)))
        (any-naturals n m) }
  }

-- This witness has an actual relatedness proof, not just payload typing.
existential-payload-witness : ∀ k
  → ∃[ A ] (impreciseTy A ≡ ‵ `ℕ) × (preciseTy A ≡ ‵ `ℕ)
      × related A (empty {S = root} {T = root}) k
          ($ (κℕ 0)) ($ (κℕ 1))
existential-payload-witness k =
  coarseNatural , refl , refl , any-naturals 0 1

tag-and-project : ℕ → Term zero
tag-and-project n =
  ($ (κℕ n) ⟨ groundInjection (‵ `ℕ) (C.ι∼★ {μ = C.idᶜ}) ⟩)
    ⟨ natural-projection {μ = C.idᶜ} ⟩

tag-and-project-⊢ : ∀ n
  → ⟨ zero , store-empty , [] ⟩ ⊢ tag-and-project n ⦂ ‵ `ℕ
tag-and-project-⊢ n =
  ⊢⟨⟩ (⊢⟨⟩ (⊢$ (κℕ n)) (groundInjection (‵ `ℕ) C.ι∼★))
    natural-projection

tag-and-project-return : ∀ n
  → ∃[ tr ] interpretFrom store-empty 1 (tag-and-project n)
      ≡ returned (E.result zero (keep ∷ []) ($ (κℕ n)) tr ($ (κℕ n)))
tag-and-project-return n = _ , refl

different-natural-values : ∀ {ΔI ΔP}
  → SameBaseValue {Δᴾ = ΔP} {Δᴵ = ΔI} `ℕ ($ (κℕ 0)) ($ (κℕ 1)) → ⊥
different-natural-values ()

tag-and-project-separates :
  Observed natural (empty {S = root} {T = root}) 2
    (tag-and-project 0) (tag-and-project 1) → ⊥
tag-and-project-separates obs
    with tag-and-project-return 0 | tag-and-project-return 1
tag-and-project-separates obs | trI , retI | trP , retP
    with Observed.backward-return obs {n = 1}
      {outP = E.result zero (keep ∷ []) ($ (κℕ 1)) trP ($ (κℕ 1))}
      (s≤s (s≤s z≤n)) retP
tag-and-project-separates obs | trI , retI | trP , retP
    | gasI , outI , retI′ , W′ , ext , r
    with return-result-unique {Σ = store-empty}
      {leftGas = gasI} {rightGas = 1} {left = outI}
      {right = E.result zero (keep ∷ []) ($ (κℕ 0)) trI ($ (κℕ 0))}
      retI′ retI
tag-and-project-separates obs | trI , retI | trP , retP
    | gasI , outI , retI′ , W′ , ext , r | refl =
  different-natural-values r

existential-payload-projection-impossible :
  ((∃[ A ] (impreciseTy A ≡ ‵ `ℕ) × (preciseTy A ≡ ‵ `ℕ)
      × related A (empty {S = root} {T = root}) 2
          ($ (κℕ 0)) ($ (κℕ 1)))
    → Observed natural (empty {S = root} {T = root}) 2
        (tag-and-project 0) (tag-and-project 1)) → ⊥
existential-payload-projection-impossible project =
  tag-and-project-separates (project (existential-payload-witness 2))
