module proof.LR-narrow.ScopedRightUniversalWrapper where

-- File Charter:
--   * Identity universal reveal wrappers preserve body-derived right-only
--     universal relations for natural/variable/arrow bodies over visible
--     old names and a fresh precise-only argument.
--   * Tests arbitrary related values at a constructed fresh argument, then
--     converts the abstract result and expands the actual allocating step.
--   * Keeps the same right-only index and all three observation clauses.
--     Does not yet handle non-identity universal conversions.

import Data.Fin as Fin
open import Data.List using ([])
open import Data.Nat using (zero; suc; _≤_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; cong₂)
  renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import Consistency using (toRenameᵗ)
open import Reduction
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopeRebase
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedTypeEquivalence
open import proof.LR-narrow.ScopedBodyInterpretation
open import proof.LR-narrow.ScopedBodyFamily
open import proof.LR-narrow.ScopedRightArguments
open import proof.LR-narrow.ScopedUniversal
open import proof.LR-narrow.ScopedStepExpansion using (observed-right-step)
open import proof.LR-narrow.ScopedConversionTransport
  using (lift-universal-id-wrapper)
open import proof.LR-narrow.UniversalReveal
  using (reveal-type-app-step-question)
open import proof.LR-narrow.VisibleEnvironment
import proof.LR-narrow.ScopedRightBodyConversion as BC
import proof.LR-narrow.ScopedRightBodyCompatibility as BK
import proof.LR-narrow.ScopedRightFreshBodyCompatibility as Fresh

module Compatibility {Δᴵ₀ Δᴾ₀ n} (Σᴵ₀ : TyStore Δᴵ₀)
    (Σᴾ₀ : TyStore Δᴾ₀) (A : Model.ScopedType Σᴵ₀ Σᴾ₀)
    (env : VisibleEnvironment Σᴵ₀ Σᴾ₀ n)
    {C : Ty (suc n)} (body : BodyFragment C) where

  module Root = Model Σᴵ₀ Σᴾ₀
  module U = Universals Σᴵ₀ Σᴾ₀
  module Args = Arguments Σᴵ₀ Σᴾ₀ A
  module F = RightBodyFamily Σᴵ₀ Σᴾ₀ body (meaning env)
    (Root.impreciseTy A) Args.Code Args.denote Args.imprecise-denote

  private
    module At {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
        {T : PhysicalScope Σᴾ₀ Δᴾ} (a : Args.Code S T) where

      module G = Fresh.Fresh (rerootEnvironment S T env)
        (Args.denote a)
      module Old = Interpretation (scopeStore S) (scopeStore T)
      module New = Interpretation (scopeStore S)
        (store-bind (scopeStore T) (Model.preciseTy (Args.denote a)))
      module EqOld = Equivalence (scopeStore S) (scopeStore T)
      module EqNew = Equivalence (scopeStore S)
        (store-bind (scopeStore T) (Model.preciseTy (Args.denote a)))
      module K = BK.Compatibility (scopeStore S)
        (store-bind (scopeStore T) (Model.preciseTy (Args.denote a)))
      module Conv = BC.Conversions (scopeStore S)
        (store-bind (scopeStore T) (Model.preciseTy (Args.denote a)))
      module Before = RebaseEquivalence S T
      module After = RebaseEquivalence
        {Σᴵ₀ = scopeStore S} {Σᴾ₀ = scopeStore T}
        root (allocate root (Model.preciseTy (Args.denote a)))

      old-fresh : ∀ X → EqNew.Equivalent
        (Rebase.rebase S (allocate T (Model.preciseTy (Args.denote a)))
          (meaning env X))
        (G.extended-meaning (Fin.suc X))
      old-fresh X = EqNew.eq-trans (Before.right-allocation (meaning env X))
        (EqNew.eq-trans
          (After.rebase-cong (reroot-meaning-equivalent S T env X))
          (reroot-meaning-equivalent root
            (allocate root (Model.preciseTy (Args.denote a)))
            (rerootEnvironment S T env) X))

      fresh-result : EqNew.Equivalent
        (U.RightFamily.result F.family (Args.fresh a))
        (New.interpret-body body G.extended-meaning)
      fresh-result = New.interpret-cong body
        (λ { Fin.zero → Args.fresh-denotation a ; (Fin.suc X) → old-fresh X })

      public-result : EqOld.Equivalent
        (Old.interpret-body body
          (Old.extend-meaning (Args.denote a)
            (meaning (rerootEnvironment S T env))))
        (U.RightFamily.result F.family a)
      public-result = Old.interpret-cong body
        (λ { Fin.zero → EqOld.eq-refl ; (Fin.suc X) →
          EqOld.eq-sym (reroot-meaning-equivalent S T env X) })

      abstract-type : ∀ {B : Ty (suc n)} (p : BodyFragment B)
        → Model.preciseTy (New.interpret-body p G.extended-meaning)
            ≡ renameᵗ
                (extᵗ (toRenameᵗ (scopeNames T (preciseNames env)))) B
      abstract-type natural-body = refl
      abstract-type (variable-body {Fin.zero}) = refl
      abstract-type (variable-body {Fin.suc X}) = refl
      abstract-type (arrow-body p q) =
        cong₂ _⇒_ (abstract-type p) (abstract-type q)

      convert-result : ∀ {k M N}
        → G.R.New.ObservedComputations
            (U.RightFamily.result F.family (Args.fresh a)) root root k M N
        → G.R.Old.ObservedComputations (U.RightFamily.result F.family a)
            root (allocate root (Model.preciseTy (Args.denote a))) k M
            ((N ↑ id↑ (scopeBody T
                (substᵗ (extsᵗ (λ X → Root.preciseTy (meaning env X))) C)))
              ↑ 〖 Fin.zero , ⇑ᵗ (Model.preciseTy (Args.denote a))
                ↑ scopeBody T
                  (substᵗ (extsᵗ (λ X → Root.preciseTy (meaning env X))) C) 〗)
      convert-result {k} {M} {N} obs =
        subst≡ (G.R.Old.ObservedComputations (U.RightFamily.result F.family a)
            root (allocate root (Model.preciseTy (Args.denote a))) k M)
          (cong (λ B → (N ↑ id↑ B)
            ↑ 〖 Fin.zero , ⇑ᵗ (Model.preciseTy (Args.denote a)) ↑ B 〗)
            (sym (scoped-body-visible T (preciseNames env) body)))
          (EqOld.observed-to public-result
            (G.R.observed-from
              (Old.interpret-body body
                (Old.extend-meaning (Args.denote a)
                  (meaning (rerootEnvironment S T env))))
              {P = root} {Q = root}
              (G.canonical-reveal-observed body {S = root} {T = root}
                (subst≡ (G.R.New.ObservedComputations
                    (New.interpret-body body G.extended-meaning) root root k M)
                  (cong (λ B → N ↑ id↑ B) (abstract-type body))
                  (K.right-reveal-observed
                    (variable-body {X = Fin.zero {zero}})
                    (λ _ → Conv.unchanged
                      (New.interpret-body body G.extended-meaning))
                    (EqNew.observed-to fresh-result obs))))))

  wrapper-related : ∀ {Δᴵ Δᴾ} {S : PhysicalScope Σᴵ₀ Δᴵ}
      {T : PhysicalScope Σᴾ₀ Δᴾ} {k M V}
    → Root.related (U.rightUniversal F.family) S T k M V
    → Root.related (U.rightUniversal F.family) S T k M
        (V ↑ `∀↑ id↑ (scopeBody T
          (substᵗ (extsᵗ (λ X → Root.preciseTy (meaning env X))) C)))
  wrapper-related {S = S} {T} {k} {M} {V} r = U.right-universal-values
    (U.RightUniversalValues.valueᴵ r) (U.RightUniversalValues.valueᴾ r ↑ all)
    (U.RightUniversalValues.typedᴵ r)
    (subst≡ (λ B → ⟨ _ , scopeStore T , [] ⟩
        ⊢ V ↑ `∀↑ id↑ (scopeBody T
          (substᵗ (extsᵗ (λ X → Root.preciseTy (meaning env X))) C)) ⦂ B)
      (sym (scope-universal T
        (substᵗ (extsᵗ (λ X → Root.preciseTy (meaning env X))) C)))
      (⊢reveal (⊢↑-∀ ⊢↑-id)
        (subst≡ (λ B → ⟨ _ , scopeStore T , [] ⟩ ⊢ V ⦂ B)
          (scope-universal T
            (substᵗ (extsᵗ (λ X → Root.preciseTy (meaning env X))) C))
          (U.RightUniversalValues.typedᴾ r)))) call
    where
    call : ∀ {Δᴵ′ Δᴾ′} {S′ : PhysicalScope Σᴵ₀ Δᴵ′}
        {T′ : PhysicalScope Σᴾ₀ Δᴾ′} {j}
      → (p : ScopeFuture S S′) → (q : ScopeFuture T T′)
      → j ≤ k → (a : Args.Code S′ T′)
      → Model.ObservedComputations (scopeStore S′) (scopeStore T′)
          (U.RightFamily.result F.family a) root root j (liftTerm p M)
          (liftTerm q
            (V ↑ `∀↑ id↑ (scopeBody T
              (substᵗ (extsᵗ (λ X → Root.preciseTy (meaning env X))) C)))
            ⦂∀ scopeBody T′
              (substᵗ (extsᵗ (λ X → Root.preciseTy (meaning env X))) C)
              [ Model.preciseTy (Args.denote a) ])
    call {S′ = S′} {T′} {j} p q j≤k a
        with reveal-type-app-step-question {Σ = scopeStore T′}
          {A = Model.preciseTy (Args.denote a)}
          (id↑ (scopeBody T′
            (substᵗ (extsᵗ (λ X → Root.preciseTy (meaning env X))) C)))
          (lift-value q (U.RightUniversalValues.valueᴾ r))
    call {S′ = S′} {T′} {j} p q j≤k a | vV′ , step =
      subst≡ (Model.ObservedComputations (scopeStore S′) (scopeStore T′)
          (U.RightFamily.result F.family a) root root j (liftTerm p M))
        (cong (λ W → W ⦂∀ scopeBody T′
            (substᵗ (extsᵗ (λ X → Root.preciseTy (meaning env X))) C)
            [ Model.preciseTy (Args.denote a) ])
          (sym (lift-universal-id-wrapper q {V = V}
            (substᵗ (extsᵗ (λ X → Root.preciseTy (meaning env X))) C))))
        (observed-right-step (λ ()) refl (β-reveal-∀ vV′) step
          (At.convert-result a
            (subst≡ (Model.ObservedComputations (scopeStore S′)
                (store-bind (scopeStore T′) (Model.preciseTy (Args.denote a)))
                (U.RightFamily.result F.family (Args.fresh a))
                root root j (liftTerm p M))
              (cong (λ W → W ⦂∀ scopeBody
                  (allocate T′ (Model.preciseTy (Args.denote a)))
                  (substᵗ (extsᵗ (λ X → Root.preciseTy (meaning env X))) C)
                  [ ＇ Fin.zero ])
                (lift-term-comp q (grow stay) V))
              (U.RightUniversalValues.instantiate r p
                (scope-trans q (grow stay)) j≤k (Args.fresh a)))))
