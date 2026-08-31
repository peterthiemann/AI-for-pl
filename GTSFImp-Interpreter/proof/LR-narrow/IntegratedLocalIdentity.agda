module proof.LR-narrow.IntegratedLocalIdentity where

-- File Charter:
--   * Identity seal/unseal adapters inhabit local arrows at every index.
--   * Tests arbitrary arguments created in any future world, not only lifts
--     of earlier arguments. Actual applications return those exact values.
--   * Private adapter names need store entries, not semantic matches or root
--     preimages. All pre-existing capabilities and payload indices persist.

open import Data.List using ([])
open import Data.Nat using (_<_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (sym) renaming (subst to subst≡; subst₂ to subst₂≡)

open import Types
open import TyStore
open import CastTerms
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.IntegratedLocal
open import proof.LR-narrow.IntegratedLocalIdentitySteps
open import proof.LR-narrow.IntegratedLocalStructure

module IdentityAdapters {ΔI0 ΔP0} (ΣI0 : TyStore ΔI0)
    (ΣP0 : TyStore ΔP0) where

  open Local ΣI0 ΣP0
  open Worlds
  open LocalStructure ΣI0 ΣP0

  identity-adapters-related : ∀ {ΔA ΔB}
      {S₀ : PhysicalScope ΣI0 ΔA} {T₀ : PhysicalScope ΣP0 ΔB}
      {AI AP} (A : Meaning S₀ T₀ AI AP)
      {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {p : ScopeFuture S₀ S} {q : ScopeFuture T₀ T}
      {W : World S T} {X Y}
    → scopeStore S ∋ X ⦂ liftTy p AI
    → scopeStore T ∋ Y ⦂ liftTy q AP
    → ∀ k → related (arrow A A) p q W k
        (identity-adapter X (liftTy p AI))
        (identity-adapter Y (liftTy q AP))
  identity-adapters-related {AI = AI} {AP} A {S = S} {T} {p} {q}
      {W} {X} {Y} entryI entryP k = arrow-values
    identity-adapter-value identity-adapter-value
    (subst≡ (λ C → ⟨ _ , scopeStore S , [] ⟩
      ⊢ identity-adapter X (liftTy p AI) ⦂ C)
      (sym (lift-ty-arrow p AI AI)) (identity-adapter-⊢ entryI))
    (subst≡ (λ C → ⟨ _ , scopeStore T , [] ⟩
      ⊢ identity-adapter Y (liftTy q AP) ⦂ C)
      (sym (lift-ty-arrow q AP AP)) (identity-adapter-⊢ entryP)) call
    where
    call : ∀ {ΔI′ ΔP′} {S′ : PhysicalScope ΣI0 ΔI′}
        {T′ : PhysicalScope ΣP0 ΔP′} {W′ : World S′ T′} {j U V}
      → (r : ScopeFuture S S′) → (s : ScopeFuture T T′)
      → Future r s W W′ → j < k
      → related A (scope-trans p r) (scope-trans q s) W′ j U V
      → Observed A (scope-trans p r) (scope-trans q s) W′ j
          (liftTerm r (identity-adapter X (liftTy p AI)) · U)
          (liftTerm s (identity-adapter Y (liftTy q AP)) · V)
    call r s ext j<k args
        with lifted-identity-adapter-return r (imprecise-value A args)
           | lifted-identity-adapter-return s (precise-value A args)
    call {S′ = S′} {T′} {W′} {j} {U} {V} r s ext j<k args
        | gasI , trI , retI | gasP , trP , retP =
      observed-from-returns {S = S′} {T = T′}
        {p = scope-trans p r} {q = scope-trans q s}
        {W = W′} {gasI = gasI} {gasP = gasP} retI retP future-refl
        (subst₂≡ (λ p′ q′ → related A p′ q′ W′ j U V)
          (sym (scope-trans-right-id (scope-trans p r)))
          (sym (scope-trans-right-id (scope-trans q s))) args)
