module proof.LR-narrow.UniversalIntroduction where

-- File Charter:
--   * Discharges symmetric universal introduction below a world insertion.
--   * Relates syntactic binder lifting to semantic paired allocation.
--   * Builds the ordinary and pending universal observations from the
--     insertion-generalized body induction hypothesis.

open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Properties using (≤-refl)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)

open import Types
open import CastTerms
open import Conversion using (〖_,_↑_〗; replaceTy)
open import Consistency using (_↪ᵗ_; keep; toRenameᵗ)
import Imprecision as I
import proof.Imprecision as PI
open import proof.ImprecisionConsistency using (ty-all-injective)
open import proof.TypeInTermSubst using (toRename-keep-eq)
open import proof.LR-narrow.TermSubstitution using (subst-cong)
import proof.DGG.CtxImp as CTI
import proof.DGG.CastTermImprecision as CTIR
open CTIR using (_∣_⊢²_⊑_∶_)
open import proof.DGG.WorldInsert
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.ClosingSubstitution
open import LR-narrow.ClosingSubstitutionProperties
open import LR-narrow.TermRelation
open import LR-narrow.Insertion
import proof.LR-narrow.ClosingSubstitution as ClosingProof
import proof.LR-narrow.Closure as Closure
open import proof.LR-narrow.AliasAvoid using (env-aliases-avoidᵖ)
open import proof.LR-narrow.ImprecisionSize using (sizeᵖ)
open import proof.LR-narrow.ReplaceImprecision using (replace-zero-open)
open import proof.LR-narrow.RevealStatements using (revealAt)
open import proof.LR-narrow.RevealStructural using
  (statements-all; revealed-computations)
open import proof.LR-narrow.UniversalReveal using (fresh-slot)
open import proof.LR-narrow.FutureInsertion using
  (insert-after-future; liftPreciseTerm-after; liftImpreciseTerm-after;
   liftPreciseBodyTerm-after; liftImpreciseBodyTerm-after;
   liftPreciseTy-after; liftImpreciseTy-after)

------------------------------------------------------------------------
-- Inserting a syntactically lifted context
------------------------------------------------------------------------

renameᵗ-keep-shift : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′) (A : Ty Δ)
  → renameᵗ (toRenameᵗ (keep ρ)) (⇑ᵗ A)
      ≡ ⇑ᵗ (renameᵗ (toRenameᵗ ρ) A)
renameᵗ-keep-shift ρ A =
  trans (renameᵗ-cong (⇑ᵗ A) (toRename-keep-eq ρ))
    (renameᵗ-shift (toRenameᵗ ρ) A)

context-imp-entry-eq : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {A A′ : Ty Δᴾ} {B B′ : Ty Δᴵ}
    (p : A ⊑ᵂ⟨ core W ⟩ B) (q : A′ ⊑ᵂ⟨ core W ⟩ B′)
  → A ≡ A′
  → B ≡ B′
  → context-imp A B p ≡ context-imp A′ B′ q
context-imp-entry-eq {W = W} p q refl refl =
  cong (context-imp {W = W} _ _) (PI.⊑-unique p q)

insert-lift-context : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {Wᶜ : CTI.World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp Wᶜ}
    {Γᵇ : CTI.CtxImp (CTI.liftWorldBoth I.X⊑X Wᶜ)}
    {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′} {π : Δᶜ ↪ᵗ Δᶜ′}
    {W : World Δᴾ′ Δᴵ′ Δᶜ′}
    (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
    (liftΓ : CTI.LiftCtx I.X⊑X Γ Γᵇ)
    (Rᴾ : Ty Δᴾ′) (Rᴵ : Ty Δᴵ′)
    (r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ)
  → compiledContext (pairedBindWorld W Rᴾ Rᴵ r)
      (insertCtx (liftBoth-insert I.X⊑X Rᴾ Rᴵ ins) Γᵇ)
    ≡ liftContextImprecision (future-paired future-refl r)
        (compiledContext W (insertCtx ins Γ))
insert-lift-context ins CTI.lift-[] Rᴾ Rᴵ r = refl
insert-lift-context {ρᴾ = ρᴾ} {ρᴵ = ρᴵ} {W = W} ins
    (CTI.lift-∷ {A = A} {B = B} {p = p} {p′ = p′} liftΓ)
    Rᴾ Rᴵ r =
  cong₂ _∷_ entry-eq (insert-lift-context ins liftΓ Rᴾ Rᴵ r)
  where
  entry-eq = context-imp-entry-eq
      {W = pairedBindWorld W Rᴾ Rᴵ r}
      (insert⊑ (liftBoth-insert I.X⊑X Rᴾ Rᴵ ins) p′)
      (liftLocalImprecision (future-paired future-refl r)
      (insert⊑ ins p))
      (renameᵗ-keep-shift ρᴾ A) (renameᵗ-keep-shift ρᴵ B)

------------------------------------------------------------------------
-- Inserting a context after a semantic future
------------------------------------------------------------------------

insert-context-after-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Δᴾ″ Δᴵ″ Δᶜ″}
    {Wᶜ : CTI.World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp Wᶜ}
    {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′} {π : Δᶜ ↪ᵗ Δᶜ′}
    {W : World Δᴾ′ Δᴵ′ Δᶜ′}
    {W′ : World Δᴾ″ Δᴵ″ Δᶜ″}
    (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
    (W≼W′ : Future W W′)
  → compiledContext W′
      (insertCtx (insert-after-future ins W≼W′) Γ)
    ≡ liftContextImprecision W≼W′
        (compiledContext W (insertCtx ins Γ))
insert-context-after-future {Γ = []} ins W≼W′ = refl
insert-context-after-future {Γ = CTI.ctx-imp A B p ∷ Γ}
    {ρᴾ = ρᴾ} {ρᴵ = ρᴵ} {W = W} ins W≼W′ =
  cong₂ _∷_ entry-eq (insert-context-after-future ins W≼W′)
  where
  entry-eq = context-imp-entry-eq {W = _}
    (insert⊑ (insert-after-future ins W≼W′) p)
    (liftLocalImprecision W≼W′ (insert⊑ ins p))
    (sym (liftPreciseTy-after W≼W′ ρᴾ A))
    (sym (liftImpreciseTy-after W≼W′ ρᴵ B))

------------------------------------------------------------------------
-- Body lifting after an inserted endpoint renaming
------------------------------------------------------------------------

liftPreciseBody-after : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Δ₀}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (ρ : Δ₀ ↪ᵗ Δᴾ) (A : Ty (suc Δ₀))
  → liftPreciseBody W≼W′
      (renameᵗ (extᵗ (toRenameᵗ ρ)) A)
    ≡ renameᵗ (extᵗ (toRenameᵗ (afterPrecise W≼W′ ρ))) A
liftPreciseBody-after W≼W′ ρ A = ty-all-injective
  (trans (sym (liftPreciseTy-universal W≼W′
      (renameᵗ (extᵗ (toRenameᵗ ρ)) A)))
    (liftPreciseTy-after W≼W′ ρ (`∀ A)))

liftImpreciseBody-after : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Δ₀}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (ρ : Δ₀ ↪ᵗ Δᴵ) (A : Ty (suc Δ₀))
  → liftImpreciseBody W≼W′
      (renameᵗ (extᵗ (toRenameᵗ ρ)) A)
    ≡ renameᵗ (extᵗ (toRenameᵗ (afterImprecise W≼W′ ρ))) A
liftImpreciseBody-after W≼W′ ρ A = ty-all-injective
  (trans (sym (liftImpreciseTy-universal W≼W′
      (renameᵗ (extᵗ (toRenameᵗ ρ)) A)))
    (liftImpreciseTy-after W≼W′ ρ (`∀ A)))

------------------------------------------------------------------------
-- Context reindexing preserves the closing environments
------------------------------------------------------------------------

related-closing-context-reindex : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ Γ′ : ContextImprecision W}
  → Γ ≡ Γ′
  → RelatedClosingSubstitutions W k Γ
  → RelatedClosingSubstitutions W k Γ′
related-closing-context-reindex refl γ = γ

precise-closing-context-reindex-lookup : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ Γ′ : ContextImprecision W}
    (eq : Γ ≡ Γ′) (γ : RelatedClosingSubstitutions W k Γ) x
  → lookupClosing (preciseClosingSubstitution
      (related-closing-context-reindex eq γ)) x
    ≡ lookupClosing (preciseClosingSubstitution γ) x
precise-closing-context-reindex-lookup refl γ x = refl

imprecise-closing-context-reindex-lookup : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {k : ℕ}
    {Γ Γ′ : ContextImprecision W}
    (eq : Γ ≡ Γ′) (γ : RelatedClosingSubstitutions W k Γ) x
  → lookupClosing (impreciseClosingSubstitution
      (related-closing-context-reindex eq γ)) x
    ≡ lookupClosing (impreciseClosingSubstitution γ) x
imprecise-closing-context-reindex-lookup refl γ x = refl
