module proof.LR-narrow.IntegratedLocalStructure where

-- File Charter:
--   * Structural constructors for scope-anchored integrated meanings.
--   * Arrows quantify over future worlds by composing anchored scope paths.
--   * Reanchoring changes only the path base; it preserves the same world and
--     does not reset or discard nominal capabilities.
--   * No live LR, CTI, operational rule, or world definition is changed.

open import Data.List using ([])
open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Properties using (≤-trans; m∸n≤m)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong)
  renaming (subst to subst≡; subst₂ to subst₂≡)

open import Types
open import TyStore
open import TermCtx using (Z)
open import CastTerms
open import Interpreter
import Eval as E
open import proof.LR-narrow.Application using (value-return-exact)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.IntegratedLocal
open import proof.LR-narrow.ScopedIdentity
  using (identity-return; lift-identity)

module LocalStructure {ΔI0 ΔP0}
    (ΣI0 : TyStore ΔI0) (ΣP0 : TyStore ΔP0) where

  module L = Local ΣI0 ΣP0
  open L
  open Worlds

  record ArrowValues {ΔAI ΔAP}
      {S₀ : PhysicalScope ΣI0 ΔAI} {T₀ : PhysicalScope ΣP0 ΔAP}
      {AI BI : Ty ΔAI} {AP BP : Ty ΔAP}
      (A : Meaning S₀ T₀ AI AP) (B : Meaning S₀ T₀ BI BP)
      {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
      {T : PhysicalScope ΣP0 ΔP}
      (p : ScopeFuture S₀ S) (q : ScopeFuture T₀ T)
      (W : World S T) (k : ℕ) (F : Term ΔI) (G : Term ΔP) : Set where
    constructor arrow-values
    field
      functionᴵ-value : Value F
      functionᴾ-value : Value G
      functionᴵ-typed : ⟨ ΔI , scopeStore S , [] ⟩
        ⊢ F ⦂ liftTy p (AI ⇒ BI)
      functionᴾ-typed : ⟨ ΔP , scopeStore T , [] ⟩
        ⊢ G ⦂ liftTy q (AP ⇒ BP)
      call : ∀ {ΔI′ ΔP′}
          {S′ : PhysicalScope ΣI0 ΔI′} {T′ : PhysicalScope ΣP0 ΔP′}
          {W′ : World S′ T′} {j U V}
        → (r : ScopeFuture S S′) → (s : ScopeFuture T T′)
        → Future r s W W′ → j < k
        → related A (scope-trans p r) (scope-trans q s) W′ j U V
        → Observed B (scope-trans p r) (scope-trans q s) W′ j
            (liftTerm r F · U) (liftTerm s G · V)

  arrow : ∀ {ΔAI ΔAP}
      {S₀ : PhysicalScope ΣI0 ΔAI} {T₀ : PhysicalScope ΣP0 ΔAP}
      {AI BI : Ty ΔAI} {AP BP : Ty ΔAP}
    → Meaning S₀ T₀ AI AP → Meaning S₀ T₀ BI BP
    → Meaning S₀ T₀ (AI ⇒ BI) (AP ⇒ BP)
  arrow A B = record
    { related = λ p q W k → ArrowValues A B p q W k
    ; imprecise-value = ArrowValues.functionᴵ-value
    ; precise-value = ArrowValues.functionᴾ-value
    ; imprecise-typed = ArrowValues.functionᴵ-typed
    ; precise-typed = ArrowValues.functionᴾ-typed
    ; downward = λ j≤k r → arrow-values
        (ArrowValues.functionᴵ-value r)
        (ArrowValues.functionᴾ-value r)
        (ArrowValues.functionᴵ-typed r)
        (ArrowValues.functionᴾ-typed r)
        (λ p q ext n<j args →
          ArrowValues.call r p q ext (≤-trans n<j j≤k) args)
    ; future-closed = λ { {p = p} {q = q} {U = F} {V = G} r s ext rel →
        arrow-values
          (lift-value r (ArrowValues.functionᴵ-value rel))
          (lift-value s (ArrowValues.functionᴾ-value rel))
          (subst≡ (λ C → ⟨ _ , _ , [] ⟩ ⊢ liftTerm r F ⦂ C)
            (sym (lift-ty-comp p r _))
            (lift-typed r (ArrowValues.functionᴵ-typed rel)))
          (subst≡ (λ C → ⟨ _ , _ , [] ⟩ ⊢ liftTerm s G ⦂ C)
            (sym (lift-ty-comp q s _))
            (lift-typed s (ArrowValues.functionᴾ-typed rel)))
          (λ { {U = U} {V = V} r′ s′ ext′ n<k args →
            subst₂≡ (Observed B _ _ _ _)
              (cong (_· U) (lift-term-comp r r′ F))
              (cong (_· V) (lift-term-comp s s′ G))
              (subst₂≡
                (λ p′ q′ → Observed B p′ q′ _ _
                  (liftTerm (scope-trans r r′) F · U)
                  (liftTerm (scope-trans s s′) G · V))
                (sym (scope-trans-assoc p r r′))
                (sym (scope-trans-assoc q s s′))
                (ArrowValues.call rel (scope-trans r r′)
                  (scope-trans s s′) (future-trans ext ext′) n<k
                  (subst₂≡ (λ p′ q′ → related A p′ q′ _ _ _ _)
                    (scope-trans-assoc p r r′)
                    (scope-trans-assoc q s s′) args))) }) }
    }

  identity-related : ∀ {ΔAI ΔAP} {S₀ : PhysicalScope ΣI0 ΔAI}
      {T₀ : PhysicalScope ΣP0 ΔAP} {AI AP}
      (A : Meaning S₀ T₀ AI AP)
      {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
      {T : PhysicalScope ΣP0 ΔP}
      (p : ScopeFuture S₀ S) (q : ScopeFuture T₀ T)
      (W : World S T) k
    → related (arrow A A) p q W k (ƛ (` 0)) (ƛ (` 0))
  identity-related {AI = AI} {AP = AP} A {S = S} {T = T} p q W k =
    arrow-values
    (ƛ (` 0))
    (ƛ (` 0))
    (subst≡ (λ C → ⟨ _ , _ , [] ⟩ ⊢ ƛ (` 0) ⦂ C)
      (sym (lift-ty-arrow p AI AI)) (⊢ƛ (⊢` Z)))
    (subst≡ (λ C → ⟨ _ , _ , [] ⟩ ⊢ ƛ (` 0) ⦂ C)
      (sym (lift-ty-arrow q AP AP)) (⊢ƛ (⊢` Z)))
    call
    where
    call : ∀ {ΔI′ ΔP′}
        {S′ : PhysicalScope ΣI0 ΔI′} {T′ : PhysicalScope ΣP0 ΔP′}
        {W′ : World S′ T′} {j U V}
      → (r : ScopeFuture S S′) → (s : ScopeFuture T T′)
      → Future r s W W′ → j < k
      → related A (scope-trans p r) (scope-trans q s) W′ j U V
      → Observed A (scope-trans p r) (scope-trans q s) W′ j
          (liftTerm r (ƛ (` 0)) · U) (liftTerm s (ƛ (` 0)) · V)
    call {S′ = S′} {T′} {W′} {j} {U} {V} r s ext j<k args
        rewrite lift-identity r | lift-identity s =
      observed-from-returns {S = S′} {T = T′} {p = scope-trans p r}
        {q = scope-trans q s} {W = W′} {gasI = 1} {gasP = 1}
        (proj₂ (identity-return (scopeStore S′) (imprecise-value A args)))
        (proj₂ (identity-return (scopeStore T′) (precise-value A args)))
        future-refl
        (subst₂≡ (λ p′ q′ → related A p′ q′ W′ j U V)
          (sym (scope-trans-right-id (scope-trans p r)))
          (sym (scope-trans-right-id (scope-trans q s)))
          args)

  reanchor : ∀ {ΔAI ΔAP ΔI ΔP} {S₀ : PhysicalScope ΣI0 ΔAI}
      {T₀ : PhysicalScope ΣP0 ΔAP}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {AI AP}
    → (p : ScopeFuture S₀ S) → (q : ScopeFuture T₀ T)
    → Meaning S₀ T₀ AI AP → Meaning S T (liftTy p AI) (liftTy q AP)
  reanchor p q A = record
    { related = λ r s → related A (scope-trans p r) (scope-trans q s)
    ; imprecise-value = imprecise-value A
    ; precise-value = precise-value A
    ; imprecise-typed = λ { {p = r} rel →
        subst≡ (λ C → ⟨ _ , _ , [] ⟩ ⊢ _ ⦂ C)
          (lift-ty-comp p r _) (imprecise-typed A rel) }
    ; precise-typed = λ { {q = s} rel →
        subst≡ (λ C → ⟨ _ , _ , [] ⟩ ⊢ _ ⦂ C)
          (lift-ty-comp q s _) (precise-typed A rel) }
    ; downward = downward A
    ; future-closed = λ { {p = r} {q = s} r′ s′ ext rel →
        subst₂≡ (λ p′ q′ → related A p′ q′ _ _ _ _)
          (scope-trans-assoc p r r′)
          (scope-trans-assoc q s s′)
          (future-closed A r′ s′ ext rel) }
    }

  reanchor-related : ∀ {ΔAI ΔAP ΔI ΔP}
      {S₀ : PhysicalScope ΣI0 ΔAI} {T₀ : PhysicalScope ΣP0 ΔAP}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {AI AP} {A : Meaning S₀ T₀ AI AP}
      {W : World S T} {k U V}
    → (p : ScopeFuture S₀ S) → (q : ScopeFuture T₀ T)
    → related A p q W k U V
    → related (reanchor p q A) stay stay W k U V
  reanchor-related {A = A} {W = W} {k = k} {U = U} {V = V} p q rel =
    subst₂≡ (λ p′ q′ → related A p′ q′ W k U V)
      (sym (scope-trans-right-id p))
      (sym (scope-trans-right-id q))
      rel

  reanchor-related-from : ∀ {ΔAI ΔAP ΔI ΔP}
      {S₀ : PhysicalScope ΣI0 ΔAI} {T₀ : PhysicalScope ΣP0 ΔAP}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {AI AP} {A : Meaning S₀ T₀ AI AP}
      {W : World S T} {k U V}
    → (p : ScopeFuture S₀ S) → (q : ScopeFuture T₀ T)
    → related (reanchor p q A) stay stay W k U V
    → related A p q W k U V
  reanchor-related-from {A = A} {W = W} {k = k} {U = U} {V = V}
      p q rel =
    subst₂≡ (λ p′ q′ → related A p′ q′ W k U V)
      (scope-trans-right-id p)
      (scope-trans-right-id q)
      rel

  reanchor-observed : ∀ {ΔAI ΔAP ΔI ΔP}
      {S₀ : PhysicalScope ΣI0 ΔAI} {T₀ : PhysicalScope ΣP0 ΔAP}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {AI AP} {A : Meaning S₀ T₀ AI AP}
      {W : World S T} {k M N}
    → (p : ScopeFuture S₀ S) → (q : ScopeFuture T₀ T)
    → Observed A p q W k M N
    → Observed (reanchor p q A) stay stay W k M N
  reanchor-observed p q obs = record
    { forward-return = Observed.forward-return obs
    ; backward-return = Observed.backward-return obs
    ; forward-blame = Observed.forward-blame obs
    }
