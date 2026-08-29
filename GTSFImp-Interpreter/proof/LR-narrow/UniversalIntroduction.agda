module proof.LR-narrow.UniversalIntroduction where

-- File Charter:
--   * Discharges symmetric universal introduction below a world insertion.
--   * Relates syntactic binder lifting to semantic paired allocation.
--   * Builds the ordinary and pending universal observations from the
--     insertion-generalized body induction hypothesis.

open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

open import Types
open import Consistency using (_↪ᵗ_; keep; toRenameᵗ)
import Imprecision as I
import proof.Imprecision as PI
open import proof.TypeInTermSubst using (toRename-keep-eq)
import proof.DGG.CtxImp as CTI
open import proof.DGG.WorldInsert
open import LR-narrow.World
open import LR-narrow.ClosingSubstitution
open import LR-narrow.TermRelation
open import proof.LR-narrow.FutureInsertion using
  (insert-after-future; liftPreciseTy-after; liftImpreciseTy-after)

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
