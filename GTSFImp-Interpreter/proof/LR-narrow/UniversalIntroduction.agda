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
open import LR-narrow.TypeBetaExpansion using (paired-step)
import proof.LR-narrow.ClosingSubstitution as ClosingProof
import proof.LR-narrow.Closure as Closure
open import proof.LR-narrow.AliasAvoid using (env-aliases-avoidᵖ)
open import proof.LR-narrow.ImprecisionSize using (sizeᵖ)
open import proof.LR-narrow.ReplaceImprecision using (replace-zero-open)
open import proof.LR-narrow.RevealStatements using (revealAt)
open import proof.LR-narrow.TypeRenamingComposition using
  (pack↑; apply↑)
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
    {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′}
    {π : Δᶜ ↪ᵗ Δᶜ′}
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
      (liftLocalImprecision (future-paired (future-refl {W = W}) r)
      (insert⊑ ins p))
      (renameᵗ-keep-shift ρᴾ A) (renameᵗ-keep-shift ρᴵ B)

------------------------------------------------------------------------
-- Inserting a context after a semantic future
------------------------------------------------------------------------

insert-context-after-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Δᴾ″ Δᴵ″ Δᶜ″}
    {Wᶜ : CTI.World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp Wᶜ}
    {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′}
    {π : Δᶜ ↪ᵗ Δᶜ′}
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

lift-context-imprecision-refl : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} (Γ : ContextImprecision W)
  → liftContextImprecision (future-refl {W = W}) Γ ≡ Γ
lift-context-imprecision-refl [] = refl
lift-context-imprecision-refl {W = W} (context-imp Aᴾ Aᴵ p ∷ Γ) =
  cong₂ _∷_ entry-eq (lift-context-imprecision-refl {W = W} Γ)
  where
  entry-eq = context-imp-entry-eq
    (liftLocalImprecision (future-refl {W = W}) p) p refl refl

------------------------------------------------------------------------
-- The inserted body after semantic paired allocation
------------------------------------------------------------------------

inserted-universal-body-contract : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ Aᴵ}
    {Wᶜ : CTI.World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp Wᶜ}
    {Γᵇ : CTI.CtxImp (CTI.liftWorldBoth I.X⊑X Wᶜ)}
    {p : Aᴾ CTI.⊑ᵂ⟨ CTI.liftWorldBoth I.X⊑X Wᶜ ⟩ Aᴵ}
    {Vᴾ : Term (suc Δᴾ)} {Vᴵ : Term (suc Δᴵ)}
    (liftΓ : CTI.LiftCtx I.X⊑X Γ Γᵇ)
    (body : CTI.liftWorldBoth I.X⊑X Wᶜ ∣ Γᵇ ⊢² Vᴾ ⊑ Vᴵ ∶ p)
    {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′}
    {π : Δᶜ ↪ᵗ Δᶜ′}
    {W : World Δᴾ′ Δᴵ′ Δᶜ′}
    (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
  → InsertedFundamentalProperty body
  → ∀ k {Δᴾ″ Δᴵ″ Δᶜ″}
      (W′ : World Δᴾ″ Δᴵ″ Δᶜ″)
      (W≼W′ : Future W W′)
      (γ : RelatedClosingSubstitutions W′ k
        (liftContextImprecision W≼W′
          (compiledContext W (insertCtx ins Γ))))
      (Rᴾ : Ty Δᴾ″) (Rᴵ : Ty Δᴵ″)
      (r : Rᴾ ⊑ᵂ⟨ core W′ ⟩ Rᴵ)
  → let tested = pairedBindWorld W′ Rᴾ Rᴵ r
        ins′ = insert-after-future ins W≼W′
        body-ins = liftBoth-insert I.X⊑X Rᴾ Rᴵ ins′
    in ComputationsRelated tested
        (FutureValueRelation (insert⊑ body-ins p)) k
        (closeTypeBody (impreciseClosingSubstitution γ)
          (liftImpreciseBodyTerm W≼W′
            (renameᵗᵐ (keep ρᴵ) Vᴵ)))
        (closeTypeBody (preciseClosingSubstitution γ)
          (liftPreciseBodyTerm W≼W′
            (renameᵗᵐ (keep ρᴾ) Vᴾ)))
inserted-universal-body-contract
    {Γᵇ = Γᵇ} {p = p} {Vᴾ = Vᴾ} {Vᴵ = Vᴵ}
    liftΓ body {ρᴾ = ρᴾ} {ρᴵ = ρᴵ} {π = π} {W = W}
    ins ih k W′ W≼W′ γ Rᴾ Rᴵ r =
  Closure.computations-related-reindex source source refl refl
    imprecise-close-eq precise-close-eq raw
  where
  step = paired-step W′ r
  tested = pairedBindWorld W′ Rᴾ Rᴵ r
  ins′ = insert-after-future ins W≼W′
  body-ins = liftBoth-insert I.X⊑X Rᴾ Rᴵ ins′

  ctx-eq = trans (insert-lift-context ins′ liftΓ Rᴾ Rᴵ r)
    (cong (liftContextImprecision step)
      (insert-context-after-future ins W≼W′))

  γ-step = related-closing-future step γ
  γ-body = related-closing-context-reindex (sym ctx-eq) γ-step
  body-context = compiledContext tested (insertCtx body-ins Γᵇ)
  γ-raw = related-closing-context-reindex
    (sym (lift-context-imprecision-refl body-context)) γ-body

  source = insert⊑ body-ins p
  raw = inserted-relation ih tested body-ins k tested future-refl γ-raw

  precise-env-eq : ∀ x → lookupClosing
      (preciseClosingSubstitution γ-raw) x
    ≡ liftˢ (closingSubstitution (preciseClosingSubstitution γ)) x
  precise-env-eq x = trans
    (precise-closing-context-reindex-lookup
      (sym (lift-context-imprecision-refl body-context)) γ-body x)
    (trans
      (precise-closing-context-reindex-lookup (sym ctx-eq) γ-step x)
      (ClosingProof.precise-related-future-lookup step γ x))

  imprecise-env-eq : ∀ x → lookupClosing
      (impreciseClosingSubstitution γ-raw) x
    ≡ liftˢ (closingSubstitution (impreciseClosingSubstitution γ)) x
  imprecise-env-eq x = trans
    (imprecise-closing-context-reindex-lookup
      (sym (lift-context-imprecision-refl body-context)) γ-body x)
    (trans
      (imprecise-closing-context-reindex-lookup (sym ctx-eq) γ-step x)
      (ClosingProof.imprecise-related-future-lookup step γ x))

  precise-close-eq = trans
    (subst-cong precise-env-eq
      (renameᵗᵐ (keep (afterPrecise W≼W′ ρᴾ)) Vᴾ))
    (cong (closeTypeBody (preciseClosingSubstitution γ))
      (sym (liftPreciseBodyTerm-after W≼W′ ρᴾ Vᴾ)))

  imprecise-close-eq = trans
    (subst-cong imprecise-env-eq
      (renameᵗᵐ (keep (afterImprecise W≼W′ ρᴵ)) Vᴵ))
    (cong (closeTypeBody (impreciseClosingSubstitution γ))
      (sym (liftImpreciseBodyTerm-after W≼W′ ρᴵ Vᴵ)))

------------------------------------------------------------------------
-- The inserted body supplies every paired universal test
------------------------------------------------------------------------

inserted-universal-body-relation : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ Aᴵ}
    {Wᶜ : CTI.World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp Wᶜ}
    {Γᵇ : CTI.CtxImp (CTI.liftWorldBoth I.X⊑X Wᶜ)}
    {p : Aᴾ CTI.⊑ᵂ⟨ CTI.liftWorldBoth I.X⊑X Wᶜ ⟩ Aᴵ}
    {Vᴾ : Term (suc Δᴾ)} {Vᴵ : Term (suc Δᴵ)}
    (liftΓ : CTI.LiftCtx I.X⊑X Γ Γᵇ)
    (body : CTI.liftWorldBoth I.X⊑X Wᶜ ∣ Γᵇ ⊢² Vᴾ ⊑ Vᴵ ∶ p)
    {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′}
    {π : Δᶜ ↪ᵗ Δᶜ′}
    {W : World Δᴾ′ Δᴵ′ Δᶜ′}
    (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
  → InsertedFundamentalProperty body
  → (pᵇ : I.extᵐ (impEnv (core W)) I.⊢
      renameᵗ (extᵗ (toRenameᵗ (preciseEmbedding (core W))))
        (renameᵗ (extᵗ (toRenameᵗ ρᴾ)) Aᴾ)
      ⊑ renameᵗ (extᵗ (toRenameᵗ (impreciseEmbedding (core W))))
        (renameᵗ (extᵗ (toRenameᵗ ρᴵ)) Aᴵ))
  → ∀ k → CompiledUniversalBodyRelation {W = W} pᵇ
      (renameᵗ (extᵗ (toRenameᵗ ρᴾ)) Aᴾ)
      (renameᵗ (extᵗ (toRenameᵗ ρᴵ)) Aᴵ) k
      (insertCtx ins Γ) (renameᵗᵐ (keep ρᴾ) Vᴾ)
      (renameᵗᵐ (keep ρᴵ) Vᴵ)
inserted-universal-body-relation
    {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} {Γᵇ = Γᵇ} {p = p}
    {Vᴾ = Vᴾ} {Vᴵ = Vᴵ}
    liftΓ body {ρᴾ = ρᴾ} {ρᴵ = ρᴵ} {π = π} {W = W}
    ins ih pᵇ k W′ W≼W′ γ Rᴾ Rᴵ r s =
  Closure.computations-related-reindex
    (liftCenterImprecision step s) (liftCenterImprecision step s)
    refl refl imprecise-reveal-eq precise-reveal-eq revealed
  where
  step = paired-step W′ r
  tested = pairedBindWorld W′ Rᴾ Rᴵ r
  ins′ = insert-after-future ins W≼W′
  body-ins = liftBoth-insert I.X⊑X Rᴾ Rᴵ ins′
  source = insert⊑ body-ins p
  contract = inserted-universal-body-contract liftΓ body ins ih k
    W′ W≼W′ γ Rᴾ Rᴵ r

  precise-body-eq : liftPreciseBody W≼W′
      (renameᵗ (extᵗ (toRenameᵗ ρᴾ)) Aᴾ)
    ≡ renameᵗ (toRenameᵗ (keep (afterPrecise W≼W′ ρᴾ))) Aᴾ
  precise-body-eq = trans (liftPreciseBody-after W≼W′ ρᴾ Aᴾ)
    (renameᵗ-cong Aᴾ (λ X → sym (toRename-keep-eq
      (afterPrecise W≼W′ ρᴾ) X)))

  imprecise-body-eq : liftImpreciseBody W≼W′
      (renameᵗ (extᵗ (toRenameᵗ ρᴵ)) Aᴵ)
    ≡ renameᵗ (toRenameᵗ (keep (afterImprecise W≼W′ ρᴵ))) Aᴵ
  imprecise-body-eq = trans (liftImpreciseBody-after W≼W′ ρᴵ Aᴵ)
    (renameᵗ-cong Aᴵ (λ X → sym (toRename-keep-eq
      (afterImprecise W≼W′ ρᴵ) X)))

  target-P = trans
    (cong (embedPrecise (core tested))
      (replace-zero-open Rᴾ
        (renameᵗ (toRenameᵗ (keep (afterPrecise W≼W′ ρᴾ))) Aᴾ)))
    (trans
      (embedPrecise-paired-shift (core W′) Rᴾ Rᴵ
        (renameᵗ (toRenameᵗ (keep (afterPrecise W≼W′ ρᴾ))) Aᴾ
          [ Rᴾ ]ᵗ))
      (cong (λ T → ⇑ᵗ (embedPrecise (core W′) (T [ Rᴾ ]ᵗ)))
        (sym precise-body-eq)))

  target-I = trans
    (cong (embedImprecise (core tested))
      (replace-zero-open Rᴵ
        (renameᵗ (toRenameᵗ (keep (afterImprecise W≼W′ ρᴵ))) Aᴵ)))
    (trans
      (embedImprecise-paired-shift (core W′) Rᴾ Rᴵ
        (renameᵗ (toRenameᵗ (keep (afterImprecise W≼W′ ρᴵ))) Aᴵ
          [ Rᴵ ]ᵗ))
      (cong (λ T → ⇑ᵗ (embedImprecise (core W′) (T [ Rᴵ ]ᵗ)))
        (sym imprecise-body-eq)))

  revealed = revealed-computations tested (fresh-slot W′ Rᴾ Rᴵ r)
    source
    (env-aliases-avoidᵖ
      (PI.ext-aliases-avoid-zero (impEnv (core W′))) source)
    refl refl (liftCenterImprecision step s) target-P target-I ≤-refl
    (λ j j≤ → revealAt (statements-all j (sizeᵖ source))) contract

  precise-reveal-eq =
    cong (apply↑ (closeTypeBody (preciseClosingSubstitution γ)
      (liftPreciseBodyTerm W≼W′ (renameᵗᵐ (keep ρᴾ) Vᴾ))))
      (cong (λ B → pack↑ 〖 Fin.zero , ⇑ᵗ Rᴾ ↑ B 〗)
        (sym precise-body-eq))

  imprecise-reveal-eq =
    cong (apply↑ (closeTypeBody (impreciseClosingSubstitution γ)
      (liftImpreciseBodyTerm W≼W′ (renameᵗᵐ (keep ρᴵ) Vᴵ))))
      (cong (λ B → pack↑ 〖 Fin.zero , ⇑ᵗ Rᴵ ↑ B 〗)
        (sym imprecise-body-eq))

------------------------------------------------------------------------
-- The inserted body after the surplus target allocation
------------------------------------------------------------------------

inserted-universal-body-contract-imprecise-bind : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′ Aᴾ Aᴵ}
    {Wᶜ : CTI.World Δᴾ Δᴵ Δᶜ}
    {Γ : CTI.CtxImp Wᶜ}
    {Γᵇ : CTI.CtxImp (CTI.liftWorldBoth I.X⊑X Wᶜ)}
    {p : Aᴾ CTI.⊑ᵂ⟨ CTI.liftWorldBoth I.X⊑X Wᶜ ⟩ Aᴵ}
    {Vᴾ : Term (suc Δᴾ)} {Vᴵ : Term (suc Δᴵ)}
    (liftΓ : CTI.LiftCtx I.X⊑X Γ Γᵇ)
    (body : CTI.liftWorldBoth I.X⊑X Wᶜ ∣ Γᵇ ⊢² Vᴾ ⊑ Vᴵ ∶ p)
    {ρᴾ : Δᴾ ↪ᵗ Δᴾ′} {ρᴵ : Δᴵ ↪ᵗ Δᴵ′}
    {π : Δᶜ ↪ᵗ Δᶜ′}
    {W : World Δᴾ′ Δᴵ′ Δᶜ′}
    (ins : WorldInsert ρᴾ ρᴵ π Wᶜ (forgetWorld W))
  → InsertedFundamentalProperty body
  → ∀ k {Δᴾ″ Δᴵ″ Δᶜ″}
      (W′ : World Δᴾ″ Δᴵ″ Δᶜ″)
      (W≼W′ : Future W W′)
      (γ : RelatedClosingSubstitutions W′ k
        (liftContextImprecision W≼W′
          (compiledContext W (insertCtx ins Γ))))
      (Rᴾ : Ty Δᴾ″) (Rᴵ : Ty Δᴵ″)
      (r : Rᴾ ⊑ᵂ⟨ core W′ ⟩ Rᴵ)
  → let tested = pairedBindWorld W′ Rᴾ Rᴵ r
        target-bound = impreciseBindWorld tested (＇ Fin.zero)
        step = paired-step W′ r
        target-step = future-imprecise {Aᴵ = ＇ Fin.zero}
          (future-refl {W = tested})
        ins′ = insert-after-future ins W≼W′
        body-ins = liftBoth-insert I.X⊑X Rᴾ Rᴵ ins′
        source = insert⊑ body-ins p
    in ComputationsRelated target-bound
        (FutureValueRelation (liftCenterImprecision target-step source)) k
        (liftImpreciseTerm target-step
          (closeTypeBody (impreciseClosingSubstitution γ)
            (liftImpreciseBodyTerm W≼W′
              (renameᵗᵐ (keep ρᴵ) Vᴵ))))
        (liftPreciseTerm target-step
          (closeTypeBody (preciseClosingSubstitution γ)
            (liftPreciseBodyTerm W≼W′
              (renameᵗᵐ (keep ρᴾ) Vᴾ))))
inserted-universal-body-contract-imprecise-bind
    {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} {Γᵇ = Γᵇ} {p = p}
    {Vᴾ = Vᴾ} {Vᴵ = Vᴵ}
    liftΓ body {ρᴾ = ρᴾ} {ρᴵ = ρᴵ} ins ih k
    W′ W≼W′ γ Rᴾ Rᴵ r =
  Closure.computations-related-reindex source′
    (liftCenterImprecision target-step source)
    precise-type-eq imprecise-type-eq
    imprecise-close-eq precise-close-eq raw
  where
  tested = pairedBindWorld W′ Rᴾ Rᴵ r
  target-bound = impreciseBindWorld tested (＇ Fin.zero)
  step : Future W′ tested
  step = paired-step W′ r
  target-step : Future tested target-bound
  target-step = future-imprecise {Aᴵ = ＇ Fin.zero}
    (future-refl {W = tested})
  ins′ = insert-after-future ins W≼W′
  body-ins = liftBoth-insert I.X⊑X Rᴾ Rᴵ ins′
  body-ins′ = insert-after-future body-ins target-step
  source = insert⊑ body-ins p
  source′ = insert⊑ body-ins′ p

  ctx-eq = trans (insert-lift-context ins′ liftΓ Rᴾ Rᴵ r)
    (cong (liftContextImprecision step)
      (insert-context-after-future ins W≼W′))

  γ-step = related-closing-future step γ
  γ-body = related-closing-context-reindex (sym ctx-eq) γ-step
  body-context = compiledContext tested (insertCtx body-ins Γᵇ)

  ctx-after = insert-context-after-future body-ins target-step
  γ-future = related-closing-future target-step γ-body
  γ-inserted = related-closing-context-reindex (sym ctx-after) γ-future
  final-context = compiledContext target-bound (insertCtx body-ins′ Γᵇ)
  γ-raw = related-closing-context-reindex
    (sym (lift-context-imprecision-refl final-context)) γ-inserted

  raw = inserted-relation ih target-bound body-ins′ k
    target-bound future-refl γ-raw

  precise-type-eq = trans
    (cong (embedPrecise (core target-bound))
      (sym (liftPreciseTy-after target-step
        (keep (afterPrecise W≼W′ ρᴾ)) Aᴾ)))
    (embedPrecise-lift target-step
      (renameᵗ (toRenameᵗ (keep (afterPrecise W≼W′ ρᴾ))) Aᴾ))

  imprecise-type-eq = trans
    (cong (embedImprecise (core target-bound))
      (sym (liftImpreciseTy-after target-step
        (keep (afterImprecise W≼W′ ρᴵ)) Aᴵ)))
    (embedImprecise-lift target-step
      (renameᵗ (toRenameᵗ (keep (afterImprecise W≼W′ ρᴵ))) Aᴵ))

  precise-base-env-eq : ∀ x → lookupClosing
      (preciseClosingSubstitution γ-body) x
    ≡ liftˢ (closingSubstitution (preciseClosingSubstitution γ)) x
  precise-base-env-eq x = trans
    (precise-closing-context-reindex-lookup (sym ctx-eq) γ-step x)
    (ClosingProof.precise-related-future-lookup step γ x)

  imprecise-base-env-eq : ∀ x → lookupClosing
      (impreciseClosingSubstitution γ-body) x
    ≡ liftˢ (closingSubstitution (impreciseClosingSubstitution γ)) x
  imprecise-base-env-eq x = trans
    (imprecise-closing-context-reindex-lookup (sym ctx-eq) γ-step x)
    (ClosingProof.imprecise-related-future-lookup step γ x)

  precise-base-close-eq = trans
    (subst-cong precise-base-env-eq
      (renameᵗᵐ (keep (afterPrecise W≼W′ ρᴾ)) Vᴾ))
    (cong (closeTypeBody (preciseClosingSubstitution γ))
      (sym (liftPreciseBodyTerm-after W≼W′ ρᴾ Vᴾ)))

  imprecise-base-close-eq = trans
    (subst-cong imprecise-base-env-eq
      (renameᵗᵐ (keep (afterImprecise W≼W′ ρᴵ)) Vᴵ))
    (cong (closeTypeBody (impreciseClosingSubstitution γ))
      (sym (liftImpreciseBodyTerm-after W≼W′ ρᴵ Vᴵ)))

  precise-final-env-eq : ∀ x → lookupClosing
      (preciseClosingSubstitution γ-raw) x
    ≡ lookupClosing (preciseClosingSubstitution γ-future) x
  precise-final-env-eq x = trans
    (precise-closing-context-reindex-lookup
      (sym (lift-context-imprecision-refl final-context)) γ-inserted x)
    (precise-closing-context-reindex-lookup
      (sym ctx-after) γ-future x)

  imprecise-final-env-eq : ∀ x → lookupClosing
      (impreciseClosingSubstitution γ-raw) x
    ≡ lookupClosing (impreciseClosingSubstitution γ-future) x
  imprecise-final-env-eq x = trans
    (imprecise-closing-context-reindex-lookup
      (sym (lift-context-imprecision-refl final-context)) γ-inserted x)
    (imprecise-closing-context-reindex-lookup
      (sym ctx-after) γ-future x)

  precise-future-env-eq : ∀ x → lookupClosing
      (preciseClosingSubstitution γ-future) x
    ≡ lookupClosing
        (ClosingProof.precise-closing-future target-step
          (preciseClosingSubstitution γ-body)) x
  precise-future-env-eq x = trans
    (ClosingProof.precise-related-future-lookup target-step γ-body x)
    (sym (ClosingProof.precise-closing-future-lookup target-step
      (preciseClosingSubstitution γ-body) x))

  imprecise-future-env-eq : ∀ x → lookupClosing
      (impreciseClosingSubstitution γ-future) x
    ≡ lookupClosing
        (ClosingProof.imprecise-closing-future target-step
          (impreciseClosingSubstitution γ-body)) x
  imprecise-future-env-eq x = trans
    (ClosingProof.imprecise-related-future-lookup target-step γ-body x)
    (sym (ClosingProof.imprecise-closing-future-lookup target-step
      (impreciseClosingSubstitution γ-body) x))

  precise-close-eq = trans
    (subst-cong precise-final-env-eq
      (renameᵗᵐ
        (afterPrecise target-step
          (keep (afterPrecise W≼W′ ρᴾ))) Vᴾ))
    (trans
      (cong (close (preciseClosingSubstitution γ-future))
        (sym (liftPreciseTerm-after target-step
          (keep (afterPrecise W≼W′ ρᴾ)) Vᴾ)))
      (trans
        (subst-cong precise-future-env-eq
          (liftPreciseTerm target-step
            (renameᵗᵐ (keep (afterPrecise W≼W′ ρᴾ)) Vᴾ)))
        (trans
          (sym (precise-close-future target-step
            (preciseClosingSubstitution γ-body)
            (renameᵗᵐ (keep (afterPrecise W≼W′ ρᴾ)) Vᴾ)))
          (cong (liftPreciseTerm target-step) precise-base-close-eq))))

  imprecise-close-eq = trans
    (subst-cong imprecise-final-env-eq
      (renameᵗᵐ
        (afterImprecise target-step
          (keep (afterImprecise W≼W′ ρᴵ))) Vᴵ))
    (trans
      (cong (close (impreciseClosingSubstitution γ-future))
        (sym (liftImpreciseTerm-after target-step
          (keep (afterImprecise W≼W′ ρᴵ)) Vᴵ)))
      (trans
        (subst-cong imprecise-future-env-eq
          (liftImpreciseTerm target-step
            (renameᵗᵐ (keep (afterImprecise W≼W′ ρᴵ)) Vᴵ)))
        (trans
          (sym (imprecise-close-future target-step
            (impreciseClosingSubstitution γ-body)
            (renameᵗᵐ
              (keep (afterImprecise W≼W′ ρᴵ)) Vᴵ)))
          (cong (liftImpreciseTerm target-step)
            imprecise-base-close-eq))))
