module proof.LR-narrow.IntegratedLocalUniversal where

-- File Charter:
--   * Universal interface over all current-scope admissible argument codes.
--   * Result families return codes, NEVER arbitrary semantic records.
--   * Quantifies over newly created future arguments and retains original
--     worlds, with proved downward/future closure of universal meanings.
--   * This is an interface over the stated code grammar, not an interpretation
--     of every Ty or a proof of arbitrary-body conversion compatibility.

open import Data.List using ([])
open import Data.Nat using (ℕ; suc; _<_)
open import Data.Nat.Properties using (≤-trans)
open import Relation.Binary.PropositionalEquality
  using (sym; cong) renaming (subst to subst≡; subst₂ to subst₂≡)

open import Types
open import TyStore
open import CastTerms
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.IntegratedLocal
open import proof.LR-narrow.IntegratedLocalCodes

module Universals {ΔI0 ΔP0} (ΣI0 : TyStore ΔI0)
    (ΣP0 : TyStore ΔP0) where

  open Local ΣI0 ΣP0
  open Worlds
  open Codes ΣI0 ΣP0

  record Family {ΔA ΔB} (S₀ : PhysicalScope ΣI0 ΔA)
      (T₀ : PhysicalScope ΣP0 ΔB)
      (CI : Ty (suc ΔA)) (CP : Ty (suc ΔB)) : Set where
    field
      result : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP}
        → (p : ScopeFuture S₀ S) → (q : ScopeFuture T₀ T)
        → ∀ {RI RP} → Code S T RI RP
        → Code S T (liftBody p CI [ RI ]ᵗ) (liftBody q CP [ RP ]ᵗ)

  record UniversalValues {ΔA ΔB} {S₀ : PhysicalScope ΣI0 ΔA}
      {T₀ : PhysicalScope ΣP0 ΔB} {CI CP} (F : Family S₀ T₀ CI CP)
      {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      (p : ScopeFuture S₀ S) (q : ScopeFuture T₀ T)
      (W : World S T) (k : ℕ) (U : Term ΔI) (V : Term ΔP) : Set where
    constructor universal-values
    field
      valueI : Value U
      valueP : Value V
      typedI : ⟨ ΔI , scopeStore S , [] ⟩ ⊢ U ⦂ liftTy p (`∀ CI)
      typedP : ⟨ ΔP , scopeStore T , [] ⟩ ⊢ V ⦂ liftTy q (`∀ CP)
      instantiate : ∀ {ΔI′ ΔP′}
          {S′ : PhysicalScope ΣI0 ΔI′} {T′ : PhysicalScope ΣP0 ΔP′}
          {W′ : World S′ T′} {j RI RP}
        → (r : ScopeFuture S S′) → (s : ScopeFuture T T′)
        → Future r s W W′ → j < k → (a : Code S′ T′ RI RP)
        → Observed
            (denote (Family.result F (scope-trans p r) (scope-trans q s) a))
            stay stay W′ j
            (liftTerm r U ⦂∀ liftBody (scope-trans p r) CI [ RI ])
            (liftTerm s V ⦂∀ liftBody (scope-trans q s) CP [ RP ])

  future-universal : ∀ {ΔA ΔB} {S₀ : PhysicalScope ΣI0 ΔA}
      {T₀ : PhysicalScope ΣP0 ΔB} {CI CP} {F : Family S₀ T₀ CI CP}
      {ΔI ΔP ΔI′ ΔP′} {S : PhysicalScope ΣI0 ΔI}
      {T : PhysicalScope ΣP0 ΔP} {S′ : PhysicalScope ΣI0 ΔI′}
      {T′ : PhysicalScope ΣP0 ΔP′}
      {p : ScopeFuture S₀ S} {q : ScopeFuture T₀ T}
      {W : World S T} {W′ : World S′ T′} {k U V}
    → (r : ScopeFuture S S′) → (s : ScopeFuture T T′)
    → Future r s W W′ → UniversalValues F p q W k U V
    → UniversalValues F (scope-trans p r) (scope-trans q s) W′ k
        (liftTerm r U) (liftTerm s V)
  future-universal {CI = CI} {CP} {F} {S′ = S′} {T′} {p} {q}
      {W′ = W′} {k} {U} {V} r s ext rel = universal-values
    (lift-value r (UniversalValues.valueI rel))
    (lift-value s (UniversalValues.valueP rel))
    (subst≡ (λ C → ⟨ _ , scopeStore S′ , [] ⟩ ⊢ liftTerm r U ⦂ C)
      (sym (lift-ty-comp p r (`∀ CI)))
      (lift-typed r (UniversalValues.typedI rel)))
    (subst≡ (λ C → ⟨ _ , scopeStore T′ , [] ⟩ ⊢ liftTerm s V ⦂ C)
      (sym (lift-ty-comp q s (`∀ CP)))
      (lift-typed s (UniversalValues.typedP rel))) call
    where
    call : ∀ {ΔI″ ΔP″} {S″ : PhysicalScope ΣI0 ΔI″}
        {T″ : PhysicalScope ΣP0 ΔP″} {W″ : World S″ T″} {j RI RP}
      → (r′ : ScopeFuture S′ S″) → (s′ : ScopeFuture T′ T″)
      → Future r′ s′ W′ W″ → j < k → (a : Code S″ T″ RI RP)
      → Observed (denote (Family.result F
          (scope-trans (scope-trans p r) r′)
          (scope-trans (scope-trans q s) s′) a)) stay stay W″ j
          (liftTerm r′ (liftTerm r U)
            ⦂∀ liftBody (scope-trans (scope-trans p r) r′) CI [ RI ])
          (liftTerm s′ (liftTerm s V)
            ⦂∀ liftBody (scope-trans (scope-trans q s) s′) CP [ RP ])
    call {RI = RI} {RP} r′ s′ ext′ j<k a
        rewrite scope-trans-assoc p r r′ | scope-trans-assoc q s s′ =
      subst₂≡ (Observed _ stay stay _ _)
        (cong (λ L → L ⦂∀ liftBody (scope-trans p (scope-trans r r′))
          CI [ RI ]) (lift-term-comp r r′ U))
        (cong (λ L → L ⦂∀ liftBody (scope-trans q (scope-trans s s′))
          CP [ RP ]) (lift-term-comp s s′ V))
        (UniversalValues.instantiate rel (scope-trans r r′)
          (scope-trans s s′) (future-trans ext ext′) j<k a)

  universal : ∀ {ΔA ΔB} {S₀ : PhysicalScope ΣI0 ΔA}
      {T₀ : PhysicalScope ΣP0 ΔB} {CI CP}
    → Family S₀ T₀ CI CP → Meaning S₀ T₀ (`∀ CI) (`∀ CP)
  universal F = record
    { related = UniversalValues F
    ; imprecise-value = UniversalValues.valueI
    ; precise-value = UniversalValues.valueP
    ; imprecise-typed = UniversalValues.typedI
    ; precise-typed = UniversalValues.typedP
    ; downward = λ j≤k rel → universal-values
        (UniversalValues.valueI rel) (UniversalValues.valueP rel)
        (UniversalValues.typedI rel) (UniversalValues.typedP rel)
        (λ r s ext n<j a →
          UniversalValues.instantiate rel r s ext (≤-trans n<j j≤k) a)
    ; future-closed = future-universal
    }
