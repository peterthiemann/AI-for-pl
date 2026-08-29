open import proof.LR-narrow.RevealStatements

module proof.LR-narrow.AliasReveal where

-- File Charter:
--   * The one-sided structural reveal and conceal at an alias slot:
--     the precise endpoint's wrapper unseals (respectively seals) the
--     occurrences of the slot's center variable, exchanging them for
--     the recorded representative's alias premise; the imprecise
--     endpoint carries no conversion.
--   * The seal case consumes (respectively produces) the alias
--     atom's payload at the same step index, which the reindexed
--     alias clause supplies.
--   * Universal types cons alias wrappers into their stored families.

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using
  (n≤1+n; ≤-trans; ≤-refl; m≤m+n; m≤n+m; <-irrefl)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no; False)
open import Data.Fin.Properties using (_≟_)

open import Types
open import TyStore
open import CastTerms
open import Conversion using
  (Conv↑; Conv↓; id↑; id↓; unseal; seal; _↦↑_; _↦↓_; replaceTy;
   〖_,_↑_〗; makeConceal; ⊢↓-seal)
open import Consistency using (toRenameᵗ)
import Imprecision as I
import proof.Imprecision as PI
open import Reduction
import Eval as E
open import Interpreter
open import proof.ImprecisionConsistency using
  (toRenameᵗ-injective; renameᵗ-injective; ext-injective;
   fin-suc-injective; ty-all-injective)
open import proof.TypeSafety.Preservation using
  (structural-reveal-typing; structural-conceal-typing)
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.Closure using (value-imprecision-downward-to)
import proof.LR-narrow.Closure as ClosureProof
open import proof.LR-narrow.ImmediateReturn using
  (related-values-return)
open import proof.LR-narrow.KeepStepExpansion using
  (related-precise-keep-step-expand)
open import proof.LR-narrow.RevealSteps
open import proof.LR-narrow.RevealLifting using
  (renameᵗ-replaceTy; liftPreciseTy-replace;
   liftPreciseTerm-reveal; liftPreciseTerm-conceal)
open import proof.LR-narrow.CastComposition using
  (computations-related-future-compose)
open import proof.LR-narrow.FramePhases using (Frame)
open import proof.LR-narrow.FrameComposition
open import proof.LR-narrow.RevealFrames using
  (revealFrame; concealFrame; RevealFrm; reveal-frm; ConcealFrm;
   conceal-frm)
open import proof.LR-narrow.ArgumentFrame using
  (related-application-computation)
open import proof.LR-narrow.SlotLifting using
  (transported-reveal-eq; transported-conceal-eq;
   liftPreciseTy-arrow; rename-universal-inversion;
   ArrowImprecision; arrow-imprecision; arrow-imprecision-view)
open import proof.LR-narrow.ReplaceImprecision using
  (replace-left-alias-eq-⊑; star-or-not;
   rename-not-in-image;
   conceal-shape-∀★; conceal-shape-⇒; conceal-shape-ι;
   replaceTy-nonvar; replaceTy-occurs; shift-no-zero)
open import proof.LR-narrow.StarNoOccurrence using
  (renameᵗ-∉ᵗ; ⊑-var-right-nonvar)
open import proof.LR-narrow.UniversalReveal using
  (liftPreciseBody-replace)
open import proof.TypeSafety.Progress using (no-bot-value)
open import LR-narrow.Atoms using (shift-⊑)
open import proof.LR-narrow.TypeRenamingComposition using
  (pack↑; pack↓; apply↑; apply↓)
import proof.LR-narrow.PreciseReveal
open module PreciseRevealModule = proof.LR-narrow.PreciseReveal
  using (precise-endpoint-type; precise-endpoint-type-of;
         identity-reveal; identity-conceal;
         ArrowSource; arrow-arrow; arrow-star; arrow-source-view;
         sizeᵗ; renameᵗ-sizeᵗ; lift-sizeᵗ;
         size-bound-left; size-bound-right;
         no-precise-bottom-value)


open PreciseComposition revealFrame using () renaming
  (precise-frame-computations-related to reveal-precise-composition;
   PrecisePlugValues to RevealPrecisePlugValues)
open PreciseComposition concealFrame using () renaming
  (precise-frame-computations-related to conceal-precise-composition;
   PrecisePlugValues to ConcealPrecisePlugValues)

------------------------------------------------------------------------
-- Consuming and producing the entry view
------------------------------------------------------------------------

alias-holds-of : ∀ {Δᴾ Δᴵ Δᶜ} {W : CoreWorld Δᴾ Δᴵ Δᶜ}
    {Z : TyVar Δᶜ} {T B : Ty Δᶜ}
    {a : AliasSemanticAtom W Z T} {mode}
    {e : SemanticEntry W Z mode} {ℛ : PayloadRelation W}
    {p : impEnv W I.⊢ T ⊑ B}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → IsAliasSlotEntry a e
  → (eqm : mode ≡ I.X⊑ᵗ T)
  → AliasAtomHolds ℛ e eqm p Vᴵ Vᴾ
  → AliasHolds ℛ a p Vᴵ Vᴾ
alias-holds-of is-alias-slot refl h = h

alias-holds-to : ∀ {Δᴾ Δᴵ Δᶜ} {W : CoreWorld Δᴾ Δᴵ Δᶜ}
    {Z : TyVar Δᶜ} {T B : Ty Δᶜ}
    {a : AliasSemanticAtom W Z T} {mode}
    {e : SemanticEntry W Z mode} {ℛ : PayloadRelation W}
    {p : impEnv W I.⊢ T ⊑ B}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → IsAliasSlotEntry a e
  → (eqm : mode ≡ I.X⊑ᵗ T)
  → AliasHolds ℛ a p Vᴵ Vᴾ
  → AliasAtomHolds ℛ e eqm p Vᴵ Vᴾ
alias-holds-to is-alias-slot refl h = h

alias-no-paired : ∀ {Δᴾ Δᴵ Δᶜ} {W : CoreWorld Δᴾ Δᴵ Δᶜ}
    {Z : TyVar Δᶜ} {T : Ty Δᶜ}
    {a : AliasSemanticAtom W Z T} {mode}
    {e : SemanticEntry W Z mode} {ℛ : PayloadRelation W}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → IsAliasSlotEntry a e
  → PairedAtomHolds ℛ e Vᴵ Vᴾ
  → ⊥
alias-no-paired is-alias-slot ()

alias-slot-consume : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    (d : AliasSlot W) {Z : TyVar Δᶜ} (Z-eq : Z ≡ acenter d)
    {B : Ty Δᶜ} {ℛ : PayloadRelation (core W)}
    (eqm : impEnv (core W) Z ≡ I.X⊑ᵗ (arepresentative d))
    (p : impEnv (core W) I.⊢ arepresentative d ⊑ B)
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → AliasAtomHolds ℛ (semanticEntry W Z) eqm p Vᴵ Vᴾ
  → AliasHolds ℛ (aatom d) p Vᴵ Vᴾ
alias-slot-consume d refl eqm p h =
  alias-holds-of (aentry-is d) eqm h

alias-slot-produce : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    (d : AliasSlot W) {Z : TyVar Δᶜ} (Z-eq : Z ≡ acenter d)
    {B : Ty Δᶜ} {ℛ : PayloadRelation (core W)}
    (eqm : impEnv (core W) Z ≡ I.X⊑ᵗ (arepresentative d))
    (p : impEnv (core W) I.⊢ arepresentative d ⊑ B)
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → AliasHolds ℛ (aatom d) p Vᴵ Vᴾ
  → AliasAtomHolds ℛ (semanticEntry W Z) eqm p Vᴵ Vᴾ
alias-slot-produce d refl eqm p h =
  alias-holds-to (aentry-is d) eqm h

alias-slot-refute-paired : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    (d : AliasSlot W) {Z : TyVar Δᶜ} (Z-eq : Z ≡ acenter d)
    {ℛ : PayloadRelation (core W)}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → PairedAtomHolds ℛ (semanticEntry W Z) Vᴵ Vᴾ
  → ⊥
alias-slot-refute-paired d refl h = alias-no-paired (aentry-is d) h

------------------------------------------------------------------------
-- Alias slots transport along futures
------------------------------------------------------------------------

record AliasEntryLift {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {Z : TyVar Δᶜ} {T : Ty Δᶜ}
    (a : AliasSemanticAtom (core W) Z T) {mode′}
    (e′ : SemanticEntry (core W′) (liftCenterVariable W≼W′ Z) mode′)
    : Set where
  constructor alias-entry-lift
  field
    alifted-representative : Ty Δᶜ′
    alifted-atom :
      AliasSemanticAtom (core W′) (liftCenterVariable W≼W′ Z)
        alifted-representative
    alifted-entry-is : IsAliasSlotEntry alifted-atom e′
    alifted-precise-variable : aliasPreciseVariable alifted-atom
      ≡ liftPreciseVariable W≼W′ (aliasPreciseVariable a)
    alifted-rep : aliasRep alifted-atom
      ≡ liftPreciseTy W≼W′ (aliasRep a)

open AliasEntryLift public

alias-entry-lift-view : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {Z : TyVar Δᶜ} {T : Ty Δᶜ}
    (a : AliasSemanticAtom (core W) Z T) {mode′}
    {e′ : SemanticEntry (core W′) (liftCenterVariable W≼W′ Z) mode′}
  → EntryLift W≼W′ (alias-entry a) e′
  → AliasEntryLift W≼W′ a e′
alias-entry-lift-view W≼W′ a (lift-alias {T′ = T′} eqX eqR) =
  alias-entry-lift T′ _ is-alias-slot eqX eqR

view-entry-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {W≼W′ : Future W W′} {Z : TyVar Δᶜ}
    {T : Ty Δᶜ} {a : AliasSemanticAtom (core W) Z T} {mode mode′}
    {e : SemanticEntry (core W) Z mode}
    {e′ : SemanticEntry (core W′) (liftCenterVariable W≼W′ Z) mode′}
  → IsAliasSlotEntry a e
  → EntryLift W≼W′ e e′
  → EntryLift W≼W′ (alias-entry a) e′
view-entry-lift is-alias-slot l = l

alias-slot-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (d : AliasSlot W) (W≼W′ : Future W W′)
  → AliasEntryLift W≼W′ (aatom d)
      (semanticEntry W′ (liftCenterVariable W≼W′ (acenter d)))
alias-slot-lift d W≼W′ = alias-entry-lift-view W≼W′ (aatom d)
  (view-entry-lift (aentry-is d) (entry-future W≼W′ (acenter d)))

alias-slot-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → AliasSlot W → (W≼W′ : Future W W′) → AliasSlot W′
alias-slot-future d W≼W′ = alias-slot
  (liftCenterVariable W≼W′ (acenter d))
  (alifted-representative (alias-slot-lift d W≼W′))
  (alifted-atom (alias-slot-lift d W≼W′))
  (alifted-entry-is (alias-slot-lift d W≼W′))

alias-slot-precise-variable-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (d : AliasSlot W) (W≼W′ : Future W W′)
  → aslotXᴾ (alias-slot-future d W≼W′)
      ≡ liftPreciseVariable W≼W′ (aslotXᴾ d)
alias-slot-precise-variable-lift d W≼W′ =
  alifted-precise-variable (alias-slot-lift d W≼W′)

alias-slot-precise-rep-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (d : AliasSlot W) (W≼W′ : Future W W′)
  → aslotRᴾ (alias-slot-future d W≼W′)
      ≡ liftPreciseTy W≼W′ (aslotRᴾ d)
alias-slot-precise-rep-lift d W≼W′ =
  alifted-rep (alias-slot-lift d W≼W′)

alias-replace-precise-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (d : AliasSlot W) (W≼W′ : Future W W′) (B : Ty Δᴾ)
  → replaceTy (aslotXᴾ (alias-slot-future d W≼W′))
      (aslotRᴾ (alias-slot-future d W≼W′)) (liftPreciseTy W≼W′ B)
    ≡ liftPreciseTy W≼W′ (replaceTy (aslotXᴾ d) (aslotRᴾ d) B)
alias-replace-precise-lift d W≼W′ B =
  trans (cong₂ (λ X R → replaceTy X R (liftPreciseTy W≼W′ B))
    (alias-slot-precise-variable-lift d W≼W′)
    (alias-slot-precise-rep-lift d W≼W′))
    (sym (liftPreciseTy-replace W≼W′ (aslotXᴾ d) (aslotRᴾ d) B))

------------------------------------------------------------------------
-- Endpoint typings of an alias wrapper
------------------------------------------------------------------------

alias-reveal-endpoints : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (d : AliasSlot W) {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → ∀ {Cᴾ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Aᴵ)
  → embedPrecise (core W) (replaceTy (aslotXᴾ d) (aslotRᴾ d) Bᴾ) ≡ Cᴾ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → TypedEndpoints W p Vᴵ Vᴾ
  → Value (Vᴾ ↑ 〖 aslotXᴾ d , aslotRᴾ d ↑ Bᴾ 〗)
  → TypedEndpoints W q Vᴵ (Vᴾ ↑ 〖 aslotXᴾ d , aslotRᴾ d ↑ Bᴾ 〗)
alias-reveal-endpoints W d {Bᴾ = Bᴾ} p sourceᴾ q targetᴾ
    {Vᴾ = Vᴾ} endpoints vᴾ =
  typed-endpoints (impreciseType endpoints)
    (replaceTy (aslotXᴾ d) (aslotRᴾ d) Bᴾ)
    (impreciseEmbedded endpoints) targetᴾ
    (imprecise-value endpoints) vᴾ (imprecise-typed endpoints)
    (⊢reveal (structural-reveal-typing Bᴾ (aliasBound (aatom d)))
      (precise-endpoint-type-of W sourceᴾ endpoints))

alias-conceal-endpoints : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (d : AliasSlot W) {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → embedPrecise (core W) Bᴾ ≡ Aᴾ
  → ∀ {Cᴾ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Aᴵ)
  → embedPrecise (core W) (replaceTy (aslotXᴾ d) (aslotRᴾ d) Bᴾ) ≡ Cᴾ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → TypedEndpoints W q Vᴵ Vᴾ
  → Value (Vᴾ ↓ makeConceal (aslotXᴾ d) (aslotRᴾ d) Bᴾ)
  → TypedEndpoints W p Vᴵ
      (Vᴾ ↓ makeConceal (aslotXᴾ d) (aslotRᴾ d) Bᴾ)
alias-conceal-endpoints W d {Bᴾ = Bᴾ} p sourceᴾ q targetᴾ
    {Vᴾ = Vᴾ} endpoints vᴾ =
  typed-endpoints (impreciseType endpoints) Bᴾ
    (impreciseEmbedded endpoints) sourceᴾ
    (imprecise-value endpoints) vᴾ (imprecise-typed endpoints)
    (⊢conceal (structural-conceal-typing Bᴾ (aliasBound (aatom d)))
      (precise-endpoint-type-of W targetᴾ endpoints))

------------------------------------------------------------------------
-- Small helpers
------------------------------------------------------------------------

var-injective : ∀ {Δ} {X Y : TyVar Δ}
  → _≡_ {A = Ty Δ} (＇ X) (＇ Y) → X ≡ Y
var-injective refl = refl

conceal-value-inversion : ∀ {Δ} {U : Term Δ} {A B : Ty Δ}
    {c : Conv↓ Δ A B}
  → Value (U ↓ c) → Value U
conceal-value-inversion (vU ↓ _) = vU

replaceTy-hit : ∀ {Δ} (X : TyVar Δ) (R : Ty Δ)
  → replaceTy X R (＇ X) ≡ R
replaceTy-hit X R with X ≟ X
replaceTy-hit X R | yes refl = refl
replaceTy-hit X R | no X≢X = ⊥-elim (X≢X refl)

replaceTy-miss : ∀ {Δ} (X : TyVar Δ) (R : Ty Δ) (Y : TyVar Δ)
  → (X ≡ Y → ⊥)
  → replaceTy X R (＇ Y) ≡ ＇ Y
replaceTy-miss X R Y X≢Y with X ≟ Y
replaceTy-miss X R Y X≢Y | yes eq = ⊥-elim (X≢Y eq)
replaceTy-miss X R Y X≢Y | no _ = refl

reindex-center-imprecision : ∀ {Δ} {μ : I.ImpEnv Δ}
    {A B A′ B′ : Ty Δ}
  → μ I.⊢ A ⊑ B
  → A ≡ A′
  → B ≡ B′
  → μ I.⊢ A′ ⊑ B′
reindex-center-imprecision p refl refl = p

alias-not-star : ∀ {Δ} {T : Ty Δ}
  → I.X⊑ᵗ T ≡ I.X⊑★
  → ⊥
alias-not-star ()

-- No imprecise endpoint type embeds to the dynamic slot's center
-- variable.

alias-no-imprecise-embed : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    (d : AliasSlot W) {B : Ty Δᴵ}
  → embedImprecise (core W) B ≡ ＇ (acenter d)
  → ⊥
alias-no-imprecise-embed d {B = ＇ Y} eq =
  aliasNoTargetOccupant (aatom d) (Y , var-injective eq)
alias-no-imprecise-embed d {B = ‵ ι} ()
alias-no-imprecise-embed d {B = ★} ()
alias-no-imprecise-embed d {B = A ⇒ B} ()
alias-no-imprecise-embed d {B = `∀ A} ()

-- Refute a source imprecision whose imprecise center is the slot's
-- variable, through the endpoints of any related pair.

alias-refute-center-right : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    (d : AliasSlot W) {Z : TyVar Δᶜ} (Z-eq : Z ≡ acenter d)
    {Aᴾ : Ty Δᶜ} {p : impEnv (core W) I.⊢ Aᴾ ⊑ ＇ Z}
    {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ⊥
alias-refute-center-right {W = W} d {Z = Z} Z-eq {p = p} related =
  alias-no-imprecise-embed d
    (subst≡
      (λ X → embedImprecise (core W)
        (impreciseType
          (ClosureProof.value-imprecision-endpoints related)) ≡ ＇ X)
      Z-eq
      (impreciseEmbedded
        (ClosureProof.value-imprecision-endpoints related)))

-- The lifted dynamic reveal and conceal are the wrappers at the
-- lifted slot and type.

alias-lifted-reveal-precise : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (d : AliasSlot W) (W≼W′ : Future W W′) (V : Term Δᴾ) (B : Ty Δᴾ)
  → liftPreciseTerm W≼W′ (V ↑ 〖 aslotXᴾ d , aslotRᴾ d ↑ B 〗)
      ≡ liftPreciseTerm W≼W′ V
          ↑ 〖 aslotXᴾ (alias-slot-future d W≼W′)
              , aslotRᴾ (alias-slot-future d W≼W′)
              ↑ liftPreciseTy W≼W′ B 〗
alias-lifted-reveal-precise d W≼W′ V B =
  trans (liftPreciseTerm-reveal W≼W′ V (aslotXᴾ d) (aslotRᴾ d) B)
    (cong (apply↑ (liftPreciseTerm W≼W′ V))
      (cong₂ (λ X R → pack↑ 〖 X , R ↑ liftPreciseTy W≼W′ B 〗)
        (sym (alias-slot-precise-variable-lift d W≼W′))
        (sym (alias-slot-precise-rep-lift d W≼W′))))

alias-lifted-conceal-precise : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (d : AliasSlot W) (W≼W′ : Future W W′) (V : Term Δᴾ) (B : Ty Δᴾ)
  → liftPreciseTerm W≼W′ (V ↓ makeConceal (aslotXᴾ d) (aslotRᴾ d) B)
      ≡ liftPreciseTerm W≼W′ V
          ↓ makeConceal (aslotXᴾ (alias-slot-future d W≼W′))
              (aslotRᴾ (alias-slot-future d W≼W′))
              (liftPreciseTy W≼W′ B)
alias-lifted-conceal-precise d W≼W′ V B =
  trans (liftPreciseTerm-conceal W≼W′ V (aslotXᴾ d) (aslotRᴾ d) B)
    (cong (apply↓ (liftPreciseTerm W≼W′ V))
      (cong₂ (λ X R →
          pack↓ (makeConceal X R (liftPreciseTy W≼W′ B)))
        (sym (alias-slot-precise-variable-lift d W≼W′))
        (sym (alias-slot-precise-rep-lift d W≼W′))))

------------------------------------------------------------------------
-- The dynamic reveal and conceal
------------------------------------------------------------------------

-- Lexicographic recursion: the type size decreases at a function type,
-- and the index decreases when a dynamic tag is unfolded.

------------------------------------------------------------------------
-- The universal wrapper at the value level
------------------------------------------------------------------------

-- Shared pieces for the universal cases: the embedded replacement
-- commutes with the slot's center, and the slot's center avoids
-- every imprecisely embedded type.

alias-embed-replace : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    (d : AliasSlot W) (T : Ty Δᴾ)
  → embedPrecise (core W) (replaceTy (aslotXᴾ d) (aslotRᴾ d) T)
      ≡ replaceTy (acenter d)
          (embedPrecise (core W) (aslotRᴾ d))
          (embedPrecise (core W) T)
alias-embed-replace {W = W} d T = trans
  (renameᵗ-replaceTy (toRenameᵗ (preciseEmbedding (core W)))
    (toRenameᵗ-injective (preciseEmbedding (core W)))
    (aslotXᴾ d) (aslotRᴾ d) T)
  (cong
    (λ Z → replaceTy Z (embedPrecise (core W) (aslotRᴾ d))
      (embedPrecise (core W) T))
    (aliasPreciseAligned (aatom d)))

alias-embed-∉ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    (d : AliasSlot W) (B : Ty Δᴵ)
  → acenter d ∉ᵗ embedImprecise (core W) B
alias-embed-∉ {W = W} d B = rename-not-in-image
  (toRenameᵗ (impreciseEmbedding (core W))) (acenter d)
  (λ Y eq → aliasNoTargetOccupant (aatom d) (Y , eq)) B

-- Wrapping a universally typed value at a dynamic slot, at the value
-- level.  The right-universal source projects the dynamic entry of
-- the stored replacement-closed family; the star-universal sources
-- recurse into the dynamic payload at the smaller index, with the
-- shape's derivation replaced by `replace-left-⊑`; the bottom
-- sources are refuted; only the paired universal source remains an
-- obligation.

∉-all-inv : ∀ {Δ} {X : TyVar Δ} {A : Ty (suc Δ)}
  → X ∉ᵗ `∀ A → Fin.suc X ∉ᵗ A
∉-all-inv (∉-all h) = h

alias-universal-value : ∀ (j sz : ℕ) (below : Below j sz)
    {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (d : AliasSlot W)
    {B₁ : Ty (suc Δᴾ)} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → embedPrecise (core W) (`∀ B₁) ≡ Aᴾ
  → ∀ {Cᴾ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Aᴵ)
  → embedPrecise (core W)
      (replaceTy (aslotXᴾ d) (aslotRᴾ d) (`∀ B₁)) ≡ Cᴾ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p j Vᴵ Vᴾ
  → ValueImprecision W q j
      Vᴵ (Vᴾ ↑ 〖 aslotXᴾ d , aslotRᴾ d ↑ `∀ B₁ 〗)
alias-universal-value zero sz below W d p sourceᴾ q targetᴾ related =
  alias-reveal-endpoints W d p sourceᴾ q targetᴾ related
    (precise-value related ↑ all)
alias-universal-value (suc k) sz below W d {B₁ = B₁}
    I.★⊑★ () q targetᴾ related
alias-universal-value (suc k) sz below W d {B₁ = B₁}
    I.ι⊑ι () q targetᴾ related
alias-universal-value (suc k) sz below W d {B₁ = B₁}
    I.X⊑X () q targetᴾ related
alias-universal-value (suc k) sz below W d {B₁ = B₁}
    (I.⇒⊑⇒ p₁ p₂) () q targetᴾ related
alias-universal-value (suc k) sz below W d {B₁ = B₁}
    (I.⇒⊑★ p₁ p₂) () q targetᴾ related
alias-universal-value (suc k) sz below W d {B₁ = B₁}
    I.ι⊑★ () q targetᴾ related
alias-universal-value (suc k) sz below W d {B₁ = B₁}
    (I.X⊑★ eq) () q targetᴾ related
alias-universal-value (suc k) sz below W d {B₁ = B₁}
    (I.∀⊑∀ {A = Aᴾc} {B = Aᴵc} p₀) sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    related@(endpoints , Bᴾ* , Bᴵ* , embP* , embI* , fam)
    with ty-all-injective
           (renameᵗ-injective
             (toRenameᵗ-injective (preciseEmbedding (core W)))
             (trans embP* (sym sourceᴾ)))
alias-universal-value (suc k) sz below W d {B₁ = B₁}
    (I.∀⊑∀ {A = Aᴾc} {B = Aᴵc} p₀) sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    related@(endpoints , .B₁ , Bᴵ* , embP* , embI* , fam)
    | refl =
  ClosureProof.value-imprecision-reindex q alt₀ {k = suc k}
    (trans (sym targetᴾ) chain) refl
    (alias-reveal-endpoints W d (I.∀⊑∀ p₀) sourceᴾ
      alt₀ chain endpoints
      (precise-value endpoints ↑ all) ,
    replaceTy (Fin.suc (aslotXᴾ d)) (⇑ᵗ (aslotRᴾ d)) B₁ ,
    Bᴵ* , chain , embI* ,
    (λ W≼W′ σ → fam₀ W≼W′ σ))
  where
  chain : embedPrecise (core W)
      (replaceTy (aslotXᴾ d) (aslotRᴾ d) (`∀ B₁))
      ≡ replaceTy (acenter d)
          (embedPrecise (core W) (aslotRᴾ d)) (`∀ Aᴾc)
  chain = trans (alias-embed-replace d (`∀ B₁))
    (cong
      (replaceTy (acenter d)
        (embedPrecise (core W) (aslotRᴾ d)))
      sourceᴾ)

  avoidᴵᵇ : Fin.suc (acenter d) ∉ᵗ Aᴵc
  avoidᴵᵇ = ∉-all-inv
    (subst≡ (acenter d ∉ᵗ_) (impreciseEmbedded endpoints)
      (alias-embed-∉ d (impreciseType endpoints)))

  inner : I.extᵐ (impEnv (core W)) I.⊢
      replaceTy (Fin.suc (acenter d))
        (⇑ᵗ (embedPrecise (core W) (aslotRᴾ d))) Aᴾc ⊑ Aᴵc
  inner = replace-left-alias-eq-⊑ (Fin.suc (acenter d))
    (cong I.⇑ᵛ (amode-eq d))
    (cong ⇑ᵗ (aliasRep-eq (aatom d))) avoidᴵᵇ p₀

  alt₀ = I.∀⊑∀ inner

  fam₀ : UniversalFamily W inner
      (replaceTy (Fin.suc (aslotXᴾ d)) (⇑ᵗ (aslotRᴾ d)) B₁)
      Bᴵ* (suc k) Vᴵ
      (Vᴾ ↑ 〖 aslotXᴾ d , aslotRᴾ d ↑ `∀ B₁ 〗)
  fam₀ {W′ = W′} W≼W′ {Bᴾ′ = Bᴾ′} {Bᴵ′ = Bᴵ′} σ =
    ClosureProof.universals-phantom
      (liftCenterBodyImprecision W≼W′ p₀)
      (liftCenterBodyImprecision W≼W′ inner)
      (ClosureProof.universals-related-transport
        {W = W′}
        {p = liftCenterBodyImprecision W≼W′ p₀}
        {Bᴾ = Bᴾ′} {k = suc k}
        termᴵ-eq
        term-eq
        (proj₁ (fam W≼W′ (w† ∷ σ†)))) ,
    ClosureProof.pending-target-universals-related-transport
      termᴵ-eq term-eq (proj₂ (fam W≼W′ (w† ∷ σ†)))
    where
    d′ = alias-slot-future d W≼W′

    σ-eq : liftPreciseBody W≼W′
        (replaceTy (Fin.suc (aslotXᴾ d)) (⇑ᵗ (aslotRᴾ d)) B₁)
        ≡ replaceTy (Fin.suc (aslotXᴾ d′)) (⇑ᵗ (aslotRᴾ d′))
            (liftPreciseBody W≼W′ B₁)
    σ-eq = trans
      (liftPreciseBody-replace W≼W′ (aslotXᴾ d) (aslotRᴾ d) B₁)
      (cong₂
        (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R)
          (liftPreciseBody W≼W′ B₁))
        (sym (alias-slot-precise-variable-lift d W≼W′))
        (sym (alias-slot-precise-rep-lift d W≼W′)))

    base-impᵇ : BodyImprecisionᵇ W
        (replaceTy (Fin.suc (aslotXᴾ d)) (⇑ᵗ (aslotRᴾ d)) B₁)
        Bᴵ*
    base-impᵇ = body-imprecisionᵇ-of inner chain embI*

    w† = reveal-aliasᵇ d′ (liftPreciseBody W≼W′ B₁)
      (liftImpreciseBody W≼W′ Bᴵ*)
      (body-imprecisionᵇ-subst σ-eq
        (body-imprecisionᵇ-future W≼W′ base-impᵇ))

    σ† : UniWrapsᵇ W′
        (replaceTy (Fin.suc (aslotXᴾ d′)) (⇑ᵗ (aslotRᴾ d′))
          (liftPreciseBody W≼W′ B₁))
        (liftImpreciseBody W≼W′ Bᴵ*) Bᴾ′ Bᴵ′
    σ† = subst≡
      (λ B → UniWrapsᵇ W′ B (liftImpreciseBody W≼W′ Bᴵ*)
        Bᴾ′ Bᴵ′) σ-eq σ

    termᴵ-eq : wrapTermᴵᵇ (w† ∷ σ†) (liftImpreciseTerm W≼W′ Vᴵ)
        ≡ wrapTermᴵᵇ σ (liftImpreciseTerm W≼W′ Vᴵ)
    termᴵ-eq = wrapTermᴵᵇ-subst σ-eq σ
      (liftImpreciseTerm W≼W′ Vᴵ)

    term-eq : wrapTermᴾᵇ (w† ∷ σ†) (liftPreciseTerm W≼W′ Vᴾ)
        ≡ wrapTermᴾᵇ σ (liftPreciseTerm W≼W′
            (Vᴾ ↑ 〖 aslotXᴾ d , aslotRᴾ d ↑ `∀ B₁ 〗))
    term-eq = trans
      (wrapTermᴾᵇ-subst σ-eq σ
        (liftPreciseTerm W≼W′ Vᴾ
          ↑ 〖 aslotXᴾ d′ , aslotRᴾ d′
              ↑ `∀ (liftPreciseBody W≼W′ B₁) 〗))
      (cong (wrapTermᴾᵇ σ)
        (trans
          (cong
            (λ T → liftPreciseTerm W≼W′ Vᴾ
              ↑ 〖 aslotXᴾ d′ , aslotRᴾ d′ ↑ T 〗)
            (sym (liftPreciseTy-universal W≼W′ B₁)))
          (sym (alias-lifted-reveal-precise d W≼W′ Vᴾ (`∀ B₁)))))
alias-universal-value (suc k) sz below W d {B₁ = B₁}
    I.bot-elim sourceᴾ q targetᴾ related =
  ⊥-elim (no-precise-bottom-value {p = I.bot-elim} {k = suc k}
    related)
alias-universal-value (suc k) sz below W d {B₁ = B₁}
    I.bot⊑★ sourceᴾ q targetᴾ related =
  ⊥-elim (no-precise-bottom-value {p = I.bot⊑★} {k = suc k}
    related)
alias-universal-value (suc k) sz below W d {B₁ = B₁}
    I.∀★⊑★ sourceᴾ q targetᴾ
    related@(endpoints , shape , payload) =
  ClosureProof.value-imprecision-reindex q I.∀★⊑★ {k = suc k}
    (trans (sym targetᴾ)
      (trans (alias-embed-replace d (`∀ B₁))
        (cong
          (replaceTy (acenter d)
            (embedPrecise (core W) (aslotRᴾ d)))
          sourceᴾ)))
    refl
    (alias-reveal-endpoints W d I.∀★⊑★ sourceᴾ I.∀★⊑★
      (trans (alias-embed-replace d (`∀ B₁))
        (cong
          (replaceTy (acenter d)
            (embedPrecise (core W) (aslotRᴾ d)))
          sourceᴾ))
      endpoints
      (precise-value endpoints ↑ all) ,
    shape ,
    alias-universal-value k sz
      (below-restrict (n≤1+n k) ≤-refl below) W d
      (right-payload-imprecision shape) sourceᴾ
      (right-payload-imprecision shape)
      (trans (alias-embed-replace d (`∀ B₁))
        (cong
          (replaceTy (acenter d)
            (embedPrecise (core W) (aslotRᴾ d)))
          sourceᴾ))
      payload)

alias-universal-value (suc k) sz below W d {B₁ = B₁}
    (I.∀⊑★ {A = Ac} nonstar p₀) sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    related@(endpoints , shape , payload)
    with star-or-not
      (replaceTy (Fin.suc (acenter d))
        (⇑ᵗ (embedPrecise (core W) (aslotRᴾ d))) Ac)
alias-universal-value (suc k) sz below W d {B₁ = B₁}
    (I.∀⊑★ {A = Ac} nonstar p₀) sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    related@(endpoints , shape , payload)
    | inj₂ nonstar′ =
  ClosureProof.value-imprecision-reindex q
    (I.∀⊑★ nonstar′
      (replace-left-alias-eq-⊑ (Fin.suc (acenter d))
        (cong I.⇑ᵛ (amode-eq d))
        (cong ⇑ᵗ (aliasRep-eq (aatom d))) ∉-star p₀))
    {k = suc k}
    (trans (sym targetᴾ) chain) refl
    (alias-reveal-endpoints W d (I.∀⊑★ nonstar p₀) sourceᴾ
      (I.∀⊑★ nonstar′
        (replace-left-alias-eq-⊑ (Fin.suc (acenter d))
          (cong I.⇑ᵛ (amode-eq d))
          (cong ⇑ᵗ (aliasRep-eq (aatom d))) ∉-star p₀))
      chain endpoints
      (precise-value endpoints ↑ all) ,
    shape′ ,
    payload′)
  where
  chain : embedPrecise (core W)
      (replaceTy (aslotXᴾ d) (aslotRᴾ d) (`∀ B₁))
      ≡ replaceTy (acenter d)
          (embedPrecise (core W) (aslotRᴾ d)) (`∀ Ac)
  chain = trans (alias-embed-replace d (`∀ B₁))
    (cong
      (replaceTy (acenter d)
        (embedPrecise (core W) (aslotRᴾ d)))
      sourceᴾ)

  shape′ : RightDynamicPayloadShape W
      (replaceTy (acenter d)
        (embedPrecise (core W) (aslotRᴾ d)) (`∀ Ac)) Vᴵ
  shape′ = right-dynamic-payload-shape
    (right-imprecise-ground shape)
    (right-imprecise-ground-proof shape)
    (right-imprecise-consistency-env shape)
    (right-imprecise-ground-to-star shape)
    (right-dynamic-imprecise-payload shape)
    (right-dynamic-imprecise-shape shape)
    (replace-left-alias-eq-⊑ (acenter d) (amode-eq d)
      (aliasRep-eq (aatom d))
      (alias-embed-∉ d (right-imprecise-ground shape))
      (right-payload-imprecision shape))

  payload′ = alias-universal-value k sz
    (below-restrict (n≤1+n k) ≤-refl below) W d
    (right-payload-imprecision shape) sourceᴾ
    (right-payload-imprecision shape′) chain payload
alias-universal-value (suc k) sz below W d {B₁ = B₁}
    (I.∀⊑★ {A = Ac} nonstar p₀) sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    related@(endpoints , shape , payload)
    | inj₁ star-eq =
  ClosureProof.value-imprecision-reindex q I.∀★⊑★ {k = suc k}
    (trans (sym targetᴾ) (trans chain (cong (λ T → `∀ T) star-eq))) refl
    (alias-reveal-endpoints W d (I.∀⊑★ nonstar p₀) sourceᴾ
      I.∀★⊑★ (trans chain (cong (λ T → `∀ T) star-eq))
      endpoints
      (precise-value endpoints ↑ all) ,
    subst≡
      (λ T → RightDynamicPayloadRelated W (`∀ T) k Vᴵ
        (Vᴾ ↑ 〖 aslotXᴾ d , aslotRᴾ d ↑ `∀ B₁ 〗))
      star-eq
      (shape′ , payload′))
  where
  chain : embedPrecise (core W)
      (replaceTy (aslotXᴾ d) (aslotRᴾ d) (`∀ B₁))
      ≡ replaceTy (acenter d)
          (embedPrecise (core W) (aslotRᴾ d)) (`∀ Ac)
  chain = trans (alias-embed-replace d (`∀ B₁))
    (cong
      (replaceTy (acenter d)
        (embedPrecise (core W) (aslotRᴾ d)))
      sourceᴾ)

  shape′ : RightDynamicPayloadShape W
      (replaceTy (acenter d)
        (embedPrecise (core W) (aslotRᴾ d)) (`∀ Ac)) Vᴵ
  shape′ = right-dynamic-payload-shape
    (right-imprecise-ground shape)
    (right-imprecise-ground-proof shape)
    (right-imprecise-consistency-env shape)
    (right-imprecise-ground-to-star shape)
    (right-dynamic-imprecise-payload shape)
    (right-dynamic-imprecise-shape shape)
    (replace-left-alias-eq-⊑ (acenter d) (amode-eq d)
      (aliasRep-eq (aatom d))
      (alias-embed-∉ d (right-imprecise-ground shape))
      (right-payload-imprecision shape))

  payload′ = alias-universal-value k sz
    (below-restrict (n≤1+n k) ≤-refl below) W d
    (right-payload-imprecision shape) sourceᴾ
    (right-payload-imprecision shape′) chain payload
alias-universal-value (suc k) sz below W d {B₁ = B₁}
    (I.∀⊑ {A = Ac} {B = Aᴵc} nonvar occurs p₀) sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    related@(endpoints , Bᴾ* , Bᴵ* , embP* , embI* , fam)
    with ty-all-injective
           (renameᵗ-injective
             (toRenameᵗ-injective (preciseEmbedding (core W)))
             (trans embP* (sym sourceᴾ)))
alias-universal-value (suc k) sz below W d {B₁ = B₁}
    (I.∀⊑ {A = Ac} {B = Aᴵc} nonvar occurs p₀) sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    related@(endpoints , .B₁ , Bᴵ* , embP* , embI* , fam)
    | refl =
  ClosureProof.value-imprecision-reindex q alt₀ {k = suc k}
    (trans (sym targetᴾ) chain) refl
    (alias-reveal-endpoints W d (I.∀⊑ nonvar occurs p₀) sourceᴾ
      alt₀ chain endpoints
      (precise-value endpoints ↑ all) ,
    replaceTy (Fin.suc (aslotXᴾ d)) (⇑ᵗ (aslotRᴾ d)) B₁ ,
    Bᴵ* , chain , embI* ,
    (λ W≼W′ σ → fam₀ W≼W′ σ))
  where
  chain : embedPrecise (core W)
      (replaceTy (aslotXᴾ d) (aslotRᴾ d) (`∀ B₁))
      ≡ replaceTy (acenter d)
          (embedPrecise (core W) (aslotRᴾ d)) (`∀ Ac)
  chain = trans (alias-embed-replace d (`∀ B₁))
    (cong
      (replaceTy (acenter d)
        (embedPrecise (core W) (aslotRᴾ d)))
      sourceᴾ)

  avoidᴵ : acenter d ∉ᵗ Aᴵc
  avoidᴵ = subst≡ (acenter d ∉ᵗ_) (impreciseEmbedded endpoints)
    (alias-embed-∉ d (impreciseType endpoints))

  nonvar′ = replaceTy-nonvar (Fin.suc (acenter d))
    (⇑ᵗ (embedPrecise (core W) (aslotRᴾ d))) nonvar

  occurs′ = replaceTy-occurs (Fin.suc (acenter d))
    (⇑ᵗ (embedPrecise (core W) (aslotRᴾ d))) (λ ())
    (shift-no-zero (embedPrecise (core W) (aslotRᴾ d))) occurs

  inner = replace-left-alias-eq-⊑ (Fin.suc (acenter d))
    (cong I.⇑ᵛ (amode-eq d))
    (cong ⇑ᵗ (aliasRep-eq (aatom d)))
    (renameᵗ-∉ᵗ Fin.suc fin-suc-injective avoidᴵ) p₀

  alt₀ = I.∀⊑ nonvar′ occurs′ inner

  fam₀ : RightUniversalFamily W
      inner
      (replaceTy (Fin.suc (aslotXᴾ d)) (⇑ᵗ (aslotRᴾ d)) B₁)
      Bᴵ* (suc k) Vᴵ
      (Vᴾ ↑ 〖 aslotXᴾ d , aslotRᴾ d ↑ `∀ B₁ 〗)
  fam₀ {W′ = W′} W≼W′ {Bᴾ′ = Bᴾ′} {Bᴵ′ = Bᴵ′} σ =
    ClosureProof.right-universals-phantom
      (liftCenterDynamicBodyImprecision W≼W′ p₀)
      (liftCenterDynamicBodyImprecision W≼W′ inner)
      (ClosureProof.right-universals-related-transport
        {W = W′}
        {p = liftCenterDynamicBodyImprecision W≼W′ p₀}
        {Bᴾ = Bᴾ′} {k = suc k}
        refl
        (wrapTermᴵ-subst σ-eq σ (liftImpreciseTerm W≼W′ Vᴵ))
        term-eq
        (fam W≼W′ (w† ∷ σ†)))
    where
    d′ = alias-slot-future d W≼W′

    σ-eq : liftPreciseBody W≼W′
        (replaceTy (Fin.suc (aslotXᴾ d)) (⇑ᵗ (aslotRᴾ d)) B₁)
        ≡ replaceTy (Fin.suc (aslotXᴾ d′)) (⇑ᵗ (aslotRᴾ d′))
            (liftPreciseBody W≼W′ B₁)
    σ-eq = trans
      (liftPreciseBody-replace W≼W′ (aslotXᴾ d) (aslotRᴾ d) B₁)
      (cong₂
        (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R)
          (liftPreciseBody W≼W′ B₁))
        (sym (alias-slot-precise-variable-lift d W≼W′))
        (sym (alias-slot-precise-rep-lift d W≼W′)))

    base-imp : BodyImprecision W
        (replaceTy (Fin.suc (aslotXᴾ d)) (⇑ᵗ (aslotRᴾ d)) B₁) Bᴵ*
    base-imp = body-imprecision-of
      nonvar′ occurs′ inner
      chain embI*

    w† = reveal-alias-slot d′ (liftPreciseBody W≼W′ B₁)
      (liftImpreciseTy W≼W′ Bᴵ*)
      (body-imprecision-subst σ-eq
        (body-imprecision-future W≼W′ base-imp))

    σ† : UniWraps W′
        (replaceTy (Fin.suc (aslotXᴾ d′)) (⇑ᵗ (aslotRᴾ d′))
          (liftPreciseBody W≼W′ B₁))
        (liftImpreciseTy W≼W′ Bᴵ*) Bᴾ′ Bᴵ′
    σ† = subst≡ (λ B → UniWraps W′ B (liftImpreciseTy W≼W′ Bᴵ*)
      Bᴾ′ Bᴵ′) σ-eq σ

    term-eq : wrapTermᴾ (w† ∷ σ†) (liftPreciseTerm W≼W′ Vᴾ)
        ≡ wrapTermᴾ σ (liftPreciseTerm W≼W′
            (Vᴾ ↑ 〖 aslotXᴾ d , aslotRᴾ d ↑ `∀ B₁ 〗))
    term-eq = trans
      (wrapTermᴾ-subst σ-eq σ
        (liftPreciseTerm W≼W′ Vᴾ
          ↑ 〖 aslotXᴾ d′ , aslotRᴾ d′
              ↑ `∀ (liftPreciseBody W≼W′ B₁) 〗))
      (cong (wrapTermᴾ σ)
        (trans
          (cong
            (λ T → liftPreciseTerm W≼W′ Vᴾ
              ↑ 〖 aslotXᴾ d′ , aslotRᴾ d′ ↑ T 〗)
            (sym (liftPreciseTy-universal W≼W′ B₁)))
          (sym (alias-lifted-reveal-precise d W≼W′ Vᴾ (`∀ B₁)))))

-- The conceal dual: the given value sits at the replaced type; the
-- concealed value is related at the source.  The star-universal
-- payload shapes transfer backwards through the ground analysis: the
-- paired-mode star premise of the source refutes every ground
-- derivation whose bound variable occurs, and what survives is
-- rebuilt from the source premise.

alias-universal-conceal-value : ∀ (j sz : ℕ) (below : Below j sz)
    {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (d : AliasSlot W)
    {B₁ : Ty (suc Δᴾ)} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → embedPrecise (core W) (`∀ B₁) ≡ Aᴾ
  → ∀ {Cᴾ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Aᴵ)
  → embedPrecise (core W)
      (replaceTy (aslotXᴾ d) (aslotRᴾ d) (`∀ B₁)) ≡ Cᴾ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W q j Vᴵ Vᴾ
  → ValueImprecision W p j
      Vᴵ (Vᴾ ↓ makeConceal (aslotXᴾ d) (aslotRᴾ d) (`∀ B₁))
alias-universal-conceal-value zero sz below W d p sourceᴾ q targetᴾ
    related =
  alias-conceal-endpoints W d p sourceᴾ q targetᴾ related
    (precise-value related ↓ all)
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    I.★⊑★ () q targetᴾ related
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    I.ι⊑ι () q targetᴾ related
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    I.X⊑X () q targetᴾ related
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    (I.⇒⊑⇒ p₁ p₂) () q targetᴾ related
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    (I.⇒⊑★ p₁ p₂) () q targetᴾ related
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    I.ι⊑★ () q targetᴾ related
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    (I.X⊑★ eq) () q targetᴾ related
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    (I.∀⊑∀ {A = Aᴾc} {B = Aᴵc} p₀) sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related = conceal-universal-case
  where
  chain : embedPrecise (core W)
      (replaceTy (aslotXᴾ d) (aslotRᴾ d) (`∀ B₁))
      ≡ replaceTy (acenter d)
          (embedPrecise (core W) (aslotRᴾ d)) (`∀ Aᴾc)
  chain = trans (alias-embed-replace d (`∀ B₁))
    (cong
      (replaceTy (acenter d)
        (embedPrecise (core W) (aslotRᴾ d)))
      sourceᴾ)

  related-endpoints =
    ClosureProof.value-imprecision-endpoints related

  avoidᴵᵇ : Fin.suc (acenter d) ∉ᵗ Aᴵc
  avoidᴵᵇ = ∉-all-inv
    (subst≡ (acenter d ∉ᵗ_)
      (impreciseEmbedded related-endpoints)
      (alias-embed-∉ d (impreciseType related-endpoints)))

  inner : I.extᵐ (impEnv (core W)) I.⊢
      replaceTy (Fin.suc (acenter d))
        (⇑ᵗ (embedPrecise (core W) (aslotRᴾ d))) Aᴾc ⊑ Aᴵc
  inner = replace-left-alias-eq-⊑ (Fin.suc (acenter d))
    (cong I.⇑ᵛ (amode-eq d))
    (cong ⇑ᵗ (aliasRep-eq (aatom d))) avoidᴵᵇ p₀

  alt : impEnv (core W) I.⊢
      replaceTy (acenter d)
        (embedPrecise (core W) (aslotRᴾ d)) (`∀ Aᴾc)
      ⊑ `∀ Aᴵc
  alt = I.∀⊑∀ inner

  conceal-universal-case : ValueImprecision W
      (I.∀⊑∀ p₀) (suc k)
      Vᴵ (Vᴾ ↓ makeConceal (aslotXᴾ d) (aslotRᴾ d) (`∀ B₁))
  conceal-universal-case
      with ClosureProof.value-imprecision-reindex alt q
        {k = suc k} (trans (sym chain) targetᴾ) refl related
  conceal-universal-case
      | endpointsq , Bᴾ* , Bᴵ* , embP* , embI* , famq
      with ty-all-injective
        (renameᵗ-injective
          (toRenameᵗ-injective (preciseEmbedding (core W)))
          (trans embP* (sym chain)))
  conceal-universal-case
      | endpointsq
      , .(replaceTy (Fin.suc (aslotXᴾ d)) (⇑ᵗ (aslotRᴾ d)) B₁)
      , Bᴵ* , embP* , embI* , famq
      | refl =
    alias-conceal-endpoints W d (I.∀⊑∀ p₀) sourceᴾ q
      targetᴾ related-endpoints
      (precise-value related-endpoints ↓ all) ,
    B₁ , Bᴵ* , sourceᴾ , embI* ,
    (λ W≼W′ σ → fam-out W≼W′ σ)
    where
    fam-out : UniversalFamily W p₀ B₁ Bᴵ* (suc k)
        Vᴵ (Vᴾ ↓ makeConceal (aslotXᴾ d) (aslotRᴾ d) (`∀ B₁))
    fam-out {W′ = W′} W≼W′ {Bᴾ′ = Bᴾ′} {Bᴵ′ = Bᴵ′} σ =
      ClosureProof.universals-phantom
        (liftCenterBodyImprecision W≼W′ inner)
        (liftCenterBodyImprecision W≼W′ p₀)
        (ClosureProof.universals-related-transport
          {W = W′}
          {p = liftCenterBodyImprecision W≼W′ inner}
          {Bᴾ = Bᴾ′} {k = suc k}
          termᴵ-eq
          term-eq
          (proj₁ (famq W≼W′ σ‡))) ,
      ClosureProof.pending-target-universals-related-transport
        termᴵ-eq term-eq (proj₂ (famq W≼W′ σ‡))
      where
      d′ = alias-slot-future d W≼W′

      σ-eq : liftPreciseBody W≼W′
          (replaceTy (Fin.suc (aslotXᴾ d)) (⇑ᵗ (aslotRᴾ d)) B₁)
          ≡ replaceTy (Fin.suc (aslotXᴾ d′)) (⇑ᵗ (aslotRᴾ d′))
              (liftPreciseBody W≼W′ B₁)
      σ-eq = trans
        (liftPreciseBody-replace W≼W′ (aslotXᴾ d) (aslotRᴾ d) B₁)
        (cong₂
          (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R)
            (liftPreciseBody W≼W′ B₁))
          (sym (alias-slot-precise-variable-lift d W≼W′))
          (sym (alias-slot-precise-rep-lift d W≼W′)))

      w† = conceal-aliasᵇ d′ (liftPreciseBody W≼W′ B₁)
        (liftImpreciseBody W≼W′ Bᴵ*)
        (body-imprecisionᵇ-future W≼W′
          (body-imprecisionᵇ-of p₀ sourceᴾ embI*))

      σ‡ : UniWrapsᵇ W′
          (liftPreciseBody W≼W′
            (replaceTy (Fin.suc (aslotXᴾ d)) (⇑ᵗ (aslotRᴾ d))
              B₁))
          (liftImpreciseBody W≼W′ Bᴵ*) Bᴾ′ Bᴵ′
      σ‡ = subst≡
        (λ B → UniWrapsᵇ W′ B (liftImpreciseBody W≼W′ Bᴵ*)
          Bᴾ′ Bᴵ′) (sym σ-eq) (w† ∷ σ)

      termᴵ-eq : wrapTermᴵᵇ σ‡ (liftImpreciseTerm W≼W′ Vᴵ)
          ≡ wrapTermᴵᵇ σ (liftImpreciseTerm W≼W′ Vᴵ)
      termᴵ-eq = wrapTermᴵᵇ-subst (sym σ-eq) (w† ∷ σ)
        (liftImpreciseTerm W≼W′ Vᴵ)

      term-eq : wrapTermᴾᵇ σ‡ (liftPreciseTerm W≼W′ Vᴾ)
          ≡ wrapTermᴾᵇ σ (liftPreciseTerm W≼W′
              (Vᴾ ↓ makeConceal (aslotXᴾ d) (aslotRᴾ d)
                (`∀ B₁)))
      term-eq = trans
        (wrapTermᴾᵇ-subst (sym σ-eq) (w† ∷ σ)
          (liftPreciseTerm W≼W′ Vᴾ))
        (cong (wrapTermᴾᵇ σ)
          (trans
            (cong
              (λ T → liftPreciseTerm W≼W′ Vᴾ
                ↓ makeConceal (aslotXᴾ d′) (aslotRᴾ d′) T)
              (sym (liftPreciseTy-universal W≼W′ B₁)))
            (sym (alias-lifted-conceal-precise d W≼W′ Vᴾ
              (`∀ B₁)))))
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    I.bot-elim sourceᴾ q targetᴾ related =
  ⊥-elim (no-precise-bottom-value {p = I.bot-elim} {k = suc k}
    (ClosureProof.value-imprecision-reindex I.bot-elim q
      {k = suc k}
      (trans
        (sym (trans (alias-embed-replace d (`∀ B₁))
          (cong
            (replaceTy (acenter d)
              (embedPrecise (core W) (aslotRᴾ d)))
            sourceᴾ)))
        targetᴾ)
      refl related))
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    I.bot⊑★ sourceᴾ q targetᴾ related =
  ⊥-elim (no-precise-bottom-value {p = I.bot⊑★} {k = suc k}
    (ClosureProof.value-imprecision-reindex I.bot⊑★ q
      {k = suc k}
      (trans
        (sym (trans (alias-embed-replace d (`∀ B₁))
          (cong
            (replaceTy (acenter d)
              (embedPrecise (core W) (aslotRᴾ d)))
            sourceᴾ)))
        targetᴾ)
      refl related))
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    I.∀★⊑★ sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    with ClosureProof.value-imprecision-reindex I.∀★⊑★ q
      {k = suc k}
      (trans
        (sym (trans (alias-embed-replace d (`∀ B₁))
          (cong
            (replaceTy (acenter d)
              (embedPrecise (core W) (aslotRᴾ d)))
            sourceᴾ)))
        targetᴾ)
      refl related
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    I.∀★⊑★ sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    | endpointsq , shapeq , payloadq =
  alias-conceal-endpoints W d I.∀★⊑★ sourceᴾ q targetᴾ
    (ClosureProof.value-imprecision-endpoints related)
    (precise-value (ClosureProof.value-imprecision-endpoints related)
      ↓ all) ,
  shapeq ,
  alias-universal-conceal-value k sz
    (below-restrict (n≤1+n k) ≤-refl below) W d
    (right-payload-imprecision shapeq) sourceᴾ
    (right-payload-imprecision shapeq)
    (trans (alias-embed-replace d (`∀ B₁))
      (cong
        (replaceTy (acenter d)
          (embedPrecise (core W) (aslotRᴾ d)))
        sourceᴾ))
    payloadq

alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    (I.∀⊑★ {A = Ac} nonstar p₀) sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    with star-or-not
      (replaceTy (Fin.suc (acenter d))
        (⇑ᵗ (embedPrecise (core W) (aslotRᴾ d))) Ac)
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    (I.∀⊑★ {A = Ac} nonstar p₀) sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    | inj₂ nonstar′
    with ClosureProof.value-imprecision-reindex
      (I.∀⊑★ nonstar′
        (replace-left-alias-eq-⊑ (Fin.suc (acenter d))
          (cong I.⇑ᵛ (amode-eq d))
          (cong ⇑ᵗ (aliasRep-eq (aatom d))) ∉-star p₀))
      q {k = suc k}
      (trans
        (sym (trans (alias-embed-replace d (`∀ B₁))
          (cong
            (replaceTy (acenter d)
              (embedPrecise (core W) (aslotRᴾ d)))
            sourceᴾ)))
        targetᴾ)
      refl related
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    (I.∀⊑★ {A = Ac} nonstar p₀) sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    | inj₂ nonstar′
    | endpointsq ,
      right-dynamic-payload-shape g gp genv gts
        payload-term payload-tag payload-der ,
      payloadq
    with gp
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    (I.∀⊑★ {A = Ac} nonstar p₀) sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    | inj₂ nonstar′
    | endpointsq ,
      right-dynamic-payload-shape g gp genv gts
        payload-term payload-tag payload-der ,
      payloadq
    | ＇ X =
  ⊥-elim (⊑-var-right-nonvar payload-der nonvar-all)
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    (I.∀⊑★ {A = Ac} nonstar p₀) sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    | inj₂ nonstar′
    | endpointsq ,
      right-dynamic-payload-shape g gp genv gts
        payload-term payload-tag payload-der ,
      payloadq
    | ‵ ι =
  ⊥-elim (conceal-shape-ι payload-der)
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    (I.∀⊑★ {A = Ac} nonstar p₀) sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    | inj₂ nonstar′
    | endpointsq ,
      right-dynamic-payload-shape g gp genv gts
        payload-term payload-tag payload-der ,
      payloadq
    | ★⇒★ =
  ⊥-elim (conceal-shape-⇒ (acenter d) refl p₀ payload-der)
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    (I.∀⊑★ {A = Ac} nonstar p₀) sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    | inj₂ nonstar′
    | endpointsq ,
      right-dynamic-payload-shape g gp genv gts
        payload-term payload-tag payload-der ,
      payloadq
    | ∀★ =
  alias-conceal-endpoints W d (I.∀⊑★ nonstar p₀) sourceᴾ q targetᴾ
    (ClosureProof.value-imprecision-endpoints related)
    (precise-value
      (ClosureProof.value-imprecision-endpoints related) ↓ all) ,
  right-dynamic-payload-shape (`∀ ★) ∀★ genv gts
    payload-term payload-tag out-der ,
  alias-universal-conceal-value k sz
    (below-restrict (n≤1+n k) ≤-refl below) W d
    out-der sourceᴾ payload-der
    (trans (alias-embed-replace d (`∀ B₁))
      (cong
        (replaceTy (acenter d)
          (embedPrecise (core W) (aslotRᴾ d)))
        sourceᴾ))
    payloadq
  where
  out-der : impEnv (core W) I.⊢ `∀ Ac
      ⊑ embedImprecise (core W) (`∀ ★)
  out-der = conceal-shape-∀★ (acenter d) refl p₀ payload-der

alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    (I.∀⊑★ {A = Ac} nonstar p₀) sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    | inj₁ star-eq
    with ClosureProof.value-imprecision-reindex I.∀★⊑★
      q {k = suc k}
      (trans
        (sym (trans
          (trans (alias-embed-replace d (`∀ B₁))
            (cong
              (replaceTy (acenter d)
                (embedPrecise (core W) (aslotRᴾ d)))
              sourceᴾ))
          (cong (λ T → `∀ T) star-eq)))
        targetᴾ)
      refl related
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    (I.∀⊑★ {A = Ac} nonstar p₀) sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    | inj₁ star-eq
    | endpointsq ,
      right-dynamic-payload-shape g gp genv gts
        payload-term payload-tag payload-der ,
      payloadq
    with gp
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    (I.∀⊑★ {A = Ac} nonstar p₀) sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    | inj₁ star-eq
    | endpointsq ,
      right-dynamic-payload-shape g gp genv gts
        payload-term payload-tag payload-der ,
      payloadq
    | ＇ X =
  ⊥-elim (⊑-var-right-nonvar payload-der nonvar-all)
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    (I.∀⊑★ {A = Ac} nonstar p₀) sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    | inj₁ star-eq
    | endpointsq ,
      right-dynamic-payload-shape g gp genv gts
        payload-term payload-tag payload-der ,
      payloadq
    | ‵ ι =
  ⊥-elim (conceal-shape-ι payload-der)
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    (I.∀⊑★ {A = Ac} nonstar p₀) sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    | inj₁ star-eq
    | endpointsq ,
      right-dynamic-payload-shape g gp genv gts
        payload-term payload-tag payload-der ,
      payloadq
    | ★⇒★ =
  ⊥-elim (conceal-shape-⇒ (acenter d) (sym star-eq) p₀
    payload-der)
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    (I.∀⊑★ {A = Ac} nonstar p₀) sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    | inj₁ star-eq
    | endpointsq ,
      right-dynamic-payload-shape g gp genv gts
        payload-term payload-tag payload-der ,
      payloadq
    | ∀★ =
  alias-conceal-endpoints W d (I.∀⊑★ nonstar p₀) sourceᴾ q targetᴾ
    (ClosureProof.value-imprecision-endpoints related)
    (precise-value
      (ClosureProof.value-imprecision-endpoints related) ↓ all) ,
  right-dynamic-payload-shape (`∀ ★) ∀★ genv gts
    payload-term payload-tag out-der ,
  alias-universal-conceal-value k sz
    (below-restrict (n≤1+n k) ≤-refl below) W d
    out-der sourceᴾ payload-der
    (trans
      (trans (alias-embed-replace d (`∀ B₁))
        (cong
          (replaceTy (acenter d)
            (embedPrecise (core W) (aslotRᴾ d)))
          sourceᴾ))
      (cong (λ T → `∀ T) star-eq))
    payloadq
  where
  out-der : impEnv (core W) I.⊢ `∀ Ac
      ⊑ embedImprecise (core W) (`∀ ★)
  out-der = conceal-shape-∀★ (acenter d) (sym star-eq) p₀
    payload-der
alias-universal-conceal-value (suc k) sz below W d {B₁ = B₁}
    (I.∀⊑ {A = Ac} {B = Aᴵc} nonvar occurs p₀) sourceᴾ q targetᴾ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related = conceal-right-universal-case
  where
  endpoints = ClosureProof.value-imprecision-endpoints related

  chain : embedPrecise (core W)
      (replaceTy (aslotXᴾ d) (aslotRᴾ d) (`∀ B₁))
      ≡ replaceTy (acenter d)
          (embedPrecise (core W) (aslotRᴾ d)) (`∀ Ac)
  chain = trans (alias-embed-replace d (`∀ B₁))
    (cong
      (replaceTy (acenter d)
        (embedPrecise (core W) (aslotRᴾ d)))
      sourceᴾ)

  avoidᴵ : acenter d ∉ᵗ Aᴵc
  avoidᴵ = subst≡ (acenter d ∉ᵗ_) (impreciseEmbedded endpoints)
    (alias-embed-∉ d (impreciseType endpoints))

  q₀ᵃ = replace-left-alias-eq-⊑ (Fin.suc (acenter d))
    (cong I.⇑ᵛ (amode-eq d))
    (cong ⇑ᵗ (aliasRep-eq (aatom d)))
    (renameᵗ-∉ᵗ Fin.suc fin-suc-injective avoidᴵ) p₀

  nonvar′ = replaceTy-nonvar (Fin.suc (acenter d))
    (⇑ᵗ (embedPrecise (core W) (aslotRᴾ d))) nonvar

  occurs′ = replaceTy-occurs (Fin.suc (acenter d))
    (⇑ᵗ (embedPrecise (core W) (aslotRᴾ d))) (λ ())
    (shift-no-zero (embedPrecise (core W) (aslotRᴾ d))) occurs

  alt = I.∀⊑ nonvar′ occurs′ q₀ᵃ

  conceal-right-universal-case : ValueImprecision W
      (I.∀⊑ nonvar occurs p₀) (suc k)
      Vᴵ (Vᴾ ↓ makeConceal (aslotXᴾ d) (aslotRᴾ d) (`∀ B₁))
  conceal-right-universal-case
      with ClosureProof.value-imprecision-reindex alt q
        {k = suc k} (trans (sym chain) targetᴾ) refl related
  conceal-right-universal-case
      | endpointsq , Bᴾ* , Bᴵ* , embP* , embI* , famq
      with ty-all-injective
        (renameᵗ-injective
          (toRenameᵗ-injective (preciseEmbedding (core W)))
          (trans embP* (sym chain)))
  conceal-right-universal-case
      | endpointsq
      , .(replaceTy (Fin.suc (aslotXᴾ d)) (⇑ᵗ (aslotRᴾ d)) B₁)
      , Bᴵ* , embP* , embI* , famq
      | refl =
    alias-conceal-endpoints W d (I.∀⊑ nonvar occurs p₀) sourceᴾ q
      targetᴾ (ClosureProof.value-imprecision-endpoints related)
      (precise-value
        (ClosureProof.value-imprecision-endpoints related) ↓ all) ,
    B₁ , Bᴵ* , sourceᴾ , embI* ,
    (λ W≼W′ σ → fam-out W≼W′ σ)
    where
    fam-out : RightUniversalFamily W p₀ B₁ Bᴵ* (suc k)
        Vᴵ (Vᴾ ↓ makeConceal (aslotXᴾ d) (aslotRᴾ d) (`∀ B₁))
    fam-out {W′ = W′} W≼W′ {Bᴾ′ = Bᴾ′} {Bᴵ′ = Bᴵ′} σ =
      ClosureProof.right-universals-phantom
        (liftCenterDynamicBodyImprecision W≼W′ q₀ᵃ)
        (liftCenterDynamicBodyImprecision W≼W′ p₀)
        (ClosureProof.right-universals-related-transport
          {W = W′}
          {p = liftCenterDynamicBodyImprecision W≼W′ q₀ᵃ}
          {Bᴾ = Bᴾ′} {k = suc k}
          refl
          (wrapTermᴵ-subst (sym σ-eq) (w† ∷ σ)
            (liftImpreciseTerm W≼W′ Vᴵ))
          term-eq
          (famq W≼W′ σ‡))
      where
      d′ = alias-slot-future d W≼W′

      σ-eq : liftPreciseBody W≼W′
          (replaceTy (Fin.suc (aslotXᴾ d)) (⇑ᵗ (aslotRᴾ d)) B₁)
          ≡ replaceTy (Fin.suc (aslotXᴾ d′)) (⇑ᵗ (aslotRᴾ d′))
              (liftPreciseBody W≼W′ B₁)
      σ-eq = trans
        (liftPreciseBody-replace W≼W′ (aslotXᴾ d) (aslotRᴾ d) B₁)
        (cong₂
          (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R)
            (liftPreciseBody W≼W′ B₁))
          (sym (alias-slot-precise-variable-lift d W≼W′))
          (sym (alias-slot-precise-rep-lift d W≼W′)))

      w† = conceal-alias-slot d′ (liftPreciseBody W≼W′ B₁)
        (liftImpreciseTy W≼W′ Bᴵ*)
        (body-imprecision-future W≼W′
          (body-imprecision-of nonvar occurs p₀ sourceᴾ embI*))

      σ‡ : UniWraps W′
          (liftPreciseBody W≼W′
            (replaceTy (Fin.suc (aslotXᴾ d)) (⇑ᵗ (aslotRᴾ d)) B₁))
          (liftImpreciseTy W≼W′ Bᴵ*) Bᴾ′ Bᴵ′
      σ‡ = subst≡ (λ B → UniWraps W′ B (liftImpreciseTy W≼W′ Bᴵ*)
        Bᴾ′ Bᴵ′) (sym σ-eq) (w† ∷ σ)

      term-eq : wrapTermᴾ σ‡ (liftPreciseTerm W≼W′ Vᴾ)
          ≡ wrapTermᴾ σ (liftPreciseTerm W≼W′
              (Vᴾ ↓ makeConceal (aslotXᴾ d) (aslotRᴾ d)
                (`∀ B₁)))
      term-eq = trans
        (wrapTermᴾ-subst (sym σ-eq) (w† ∷ σ)
          (liftPreciseTerm W≼W′ Vᴾ))
        (cong (wrapTermᴾ σ)
          (trans
            (cong
              (λ T → liftPreciseTerm W≼W′ Vᴾ
                ↓ makeConceal (aslotXᴾ d′) (aslotRᴾ d′) T)
              (sym (liftPreciseTy-universal W≼W′ B₁)))
            (sym (alias-lifted-conceal-precise d W≼W′ Vᴾ
              (`∀ B₁)))))

mutual
  alias-reveal-go : ∀ (fuel j sz : ℕ) (below : Below j sz)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (d : AliasSlot W)
      {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → sizeᵗ Bᴾ ≤ fuel
    → embedPrecise (core W) Bᴾ ≡ Aᴾ
    → ∀ {Cᴾ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Aᴵ)
    → embedPrecise (core W) (replaceTy (aslotXᴾ d) (aslotRᴾ d) Bᴾ)
        ≡ Cᴾ
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W p j Vᴵ Vᴾ
    → ComputationsRelated W (FutureValueRelation q) j
        Vᴵ (Vᴾ ↑ 〖 aslotXᴾ d , aslotRᴾ d ↑ Bᴾ 〗)
  alias-reveal-go fuel j sz below W d {Bᴾ = ＇ Y} p size sourceᴾ q
      targetᴾ related with aslotXᴾ d ≟ Y
  alias-reveal-go fuel j sz below W d {Bᴾ = ＇ Y} p size
      sourceᴾ q targetᴾ related | no X≢Y =
    ClosureProof.computations-related-reindex p q
      (trans (sym sourceᴾ) targetᴾ) refl refl refl
      (identity-reveal W p (＇ Y) related)
  alias-reveal-go fuel j sz below W d {Bᴾ = ＇ Y} I.X⊑X size sourceᴾ q
      targetᴾ related | yes refl =
    ⊥-elim (alias-refute-center-right d
      (trans (sym (var-injective sourceᴾ))
        (aliasPreciseAligned (aatom d)))
      related)
  alias-reveal-go fuel zero sz below W d {Bᴾ = ＇ Y} (I.alias eqm p)
      size sourceᴾ q targetᴾ related | yes refl =
    ClosureProof.computations-related-zero
  alias-reveal-go fuel (suc j′) sz below W d {Bᴾ = ＇ Y}
      (I.alias {X = X} {B = B} eqm {notSelf = notSelf} p)
      size sourceᴾ q targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related@(endpoints , holds) | yes refl =
    ClosureProof.computations-related-reindex q q refl refl refl
      (sym (cong (_↑ unseal (aslotXᴾ d) (aslotRᴾ d)) shape-eq))
      stepped
    where
    Z-eq : X ≡ acenter d
    Z-eq = trans (sym (var-injective sourceᴾ))
      (aliasPreciseAligned (aatom d))

    premise : impEnv (core W) I.⊢ arepresentative d ⊑ B
    premise = reindex-center-imprecision q
      (trans (sym targetᴾ) (aliasRep-eq (aatom d))) refl

    canonical-not-self : False (isVar? (acenter d) B)
    canonical-not-self = subst≡ (λ Z → False (isVar? Z B)) Z-eq notSelf

    canonical : impEnv (core W) I.⊢ ＇ acenter d ⊑ B
    canonical = I.alias (amode-eq d) {notSelf = canonical-not-self} premise

    canonical-related : ValueImprecision W canonical (suc j′) Vᴵ Vᴾ
    canonical-related = ClosureProof.value-imprecision-reindex
      canonical (I.alias eqm p) {k = suc j′}
      (cong ＇_ (sym Z-eq)) refl related

    ah : AliasHolds (ValueImprecisionᵏ (suc j′) W) (aatom d)
        premise Vᴵ Vᴾ
    ah = alias-slot-consume d refl (amode-eq d) premise
      (proj₂ canonical-related)

    Uᴾ = aliasSealed ah

    shape-eq : Vᴾ ≡ Uᴾ ↓ seal (aslotXᴾ d) (aslotRᴾ d)
    shape-eq = alias-sealed-shape ah

    payload-q : ValueImprecision W q (suc j′) Vᴵ Uᴾ
    payload-q = ClosureProof.value-imprecision-reindex q premise {k = suc j′}
      (trans (sym targetᴾ) (aliasRep-eq (aatom d))) refl
      (alias-payload-related ah)

    vUᴾ : Value Uᴾ
    vUᴾ = conceal-value-inversion
      (subst≡ Value shape-eq (precise-value endpoints))

    inner : ComputationsRelated W (FutureValueRelation q) (suc j′)
        Vᴵ Uᴾ
    inner = related-values-return (imprecise-value endpoints) vUᴾ
      (λ i i≤j → value-imprecision-downward-to i≤j payload-q)

    stepped : ComputationsRelated W (FutureValueRelation q) (suc j′)
        Vᴵ ((Uᴾ ↓ seal (aslotXᴾ d) (aslotRᴾ d))
          ↑ unseal (aslotXᴾ d) (aslotRᴾ d))
    stepped
        with unseal-step-question {Σ = preciseStore (core W)}
          (aslotXᴾ d) (aslotRᴾ d) vUᴾ
    stepped | vUᴾ′ , step-eq =
      related-precise-keep-step-expand (λ ())
        (unseal-value-none (aslotXᴾ d) (aslotRᴾ d) vUᴾ′)
        (pure-step (conceal-reveal vUᴾ′)) step-eq inner

  alias-reveal-go fuel j sz below W d {Bᴾ = ＇ Y} (I.X⊑★ eqm) size
      sourceᴾ q targetᴾ related | yes refl =
    ⊥-elim (alias-not-star (trans (sym (amode-eq d))
      (trans (cong (impEnv (core W))
        (trans (sym (aliasPreciseAligned (aatom d)))
          (var-injective sourceᴾ))) eqm)))
  alias-reveal-go fuel j sz below W d {Bᴾ = ‵ ι} p size sourceᴾ q
      targetᴾ related =
    ClosureProof.computations-related-reindex p q
      (trans (sym sourceᴾ) targetᴾ) refl refl refl
      (identity-reveal W p (‵ ι) related)
  alias-reveal-go fuel j sz below W d {Bᴾ = ★} p size sourceᴾ q
      targetᴾ related =
    ClosureProof.computations-related-reindex p q
      (trans (sym sourceᴾ) targetᴾ) refl refl refl
      (identity-reveal W p ★ related)
  alias-reveal-go zero j sz below W d {Bᴾ = A₀ ⇒ B₀} p () sourceᴾ q
      targetᴾ related
  alias-reveal-go (suc fuel) j sz below W d {Bᴾ = A₀ ⇒ B₀} p size
      sourceᴾ q targetᴾ related =
    related-values-return
      (imprecise-value endpoints) (precise-value endpoints ↑ fun)
      (λ i i≤j → alias-reveal-arrow fuel i sz
        (below-restrict i≤j ≤-refl below) W d p
        (size-bound-left size) (size-bound-right size) sourceᴾ
        q targetᴾ
        (value-imprecision-downward-to i≤j related))
    where
    endpoints = ClosureProof.value-imprecision-endpoints related
  alias-reveal-go fuel j sz below W d {Bᴾ = `∀ B₁} p size sourceᴾ q
      targetᴾ related =
    related-values-return
      (imprecise-value endpoints) (precise-value endpoints ↑ all)
      (λ i i≤j → alias-universal-value i sz
        (below-restrict i≤j ≤-refl below) W d p sourceᴾ q targetᴾ
        (value-imprecision-downward-to i≤j related))
    where
    endpoints = ClosureProof.value-imprecision-endpoints related

  alias-conceal-go : ∀ (fuel j sz : ℕ) (below : Below j sz)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (d : AliasSlot W)
      {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → sizeᵗ Bᴾ ≤ fuel
    → embedPrecise (core W) Bᴾ ≡ Aᴾ
    → ∀ {Cᴾ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Aᴵ)
    → embedPrecise (core W) (replaceTy (aslotXᴾ d) (aslotRᴾ d) Bᴾ)
        ≡ Cᴾ
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W q j Vᴵ Vᴾ
    → ComputationsRelated W (FutureValueRelation p) j
        Vᴵ (Vᴾ ↓ makeConceal (aslotXᴾ d) (aslotRᴾ d) Bᴾ)
  alias-conceal-go fuel j sz below W d {Bᴾ = ＇ Y} p size sourceᴾ q
      targetᴾ related with aslotXᴾ d ≟ Y
  alias-conceal-go fuel j sz below W d {Bᴾ = ＇ Y} p size sourceᴾ q
      targetᴾ related | no X≢Y =
    ClosureProof.computations-related-reindex q p
      (trans (sym targetᴾ) sourceᴾ) refl refl refl
      (identity-conceal W q (＇ Y) related)
  alias-conceal-go fuel j sz below W d {Bᴾ = ＇ Y} I.X⊑X size sourceᴾ
      q targetᴾ related | yes refl =
    ⊥-elim (alias-refute-center-right d
      (trans (sym (var-injective sourceᴾ))
        (aliasPreciseAligned (aatom d)))
      related)
  alias-conceal-go fuel zero sz below W d {Bᴾ = ＇ Y}
      (I.alias eqm p) size
      sourceᴾ q targetᴾ related | yes refl =
    ClosureProof.computations-related-zero
  alias-conceal-go fuel (suc j′) sz below W d {Bᴾ = ＇ Y}
      (I.alias {X = X} {B = B} eqm {notSelf = notSelf} p)
      size sourceᴾ q targetᴾ {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
      | yes refl =
    related-values-return (imprecise-value endpoints)
      (precise-value endpoints ↓ seal)
      at-every-index
    where
    endpoints = ClosureProof.value-imprecision-endpoints related

    premise : impEnv (core W) I.⊢ arepresentative d ⊑ B
    premise = reindex-center-imprecision q
      (trans (sym targetᴾ) (aliasRep-eq (aatom d))) refl

    payload-rep : ValueImprecision W premise
        (suc j′) Vᴵ Vᴾ
    payload-rep = ClosureProof.value-imprecision-reindex
      premise q {k = suc j′}
      (trans (sym (aliasRep-eq (aatom d))) targetᴾ) refl related

    Z-eq : X ≡ acenter d
    Z-eq = trans (sym (var-injective sourceᴾ))
      (aliasPreciseAligned (aatom d))

    canonical-not-self : False (isVar? (acenter d) B)
    canonical-not-self = subst≡ (λ Z → False (isVar? Z B)) Z-eq notSelf

    canonical : impEnv (core W) I.⊢ ＇ acenter d ⊑ B
    canonical = I.alias (amode-eq d) {notSelf = canonical-not-self} premise

    canonical-source : embedPrecise (core W) (＇ aslotXᴾ d)
        ≡ ＇ acenter d
    canonical-source = cong ＇_ (aliasPreciseAligned (aatom d))

    conceal-endpoints : TypedEndpoints W canonical Vᴵ
        (Vᴾ ↓ seal (aslotXᴾ d) (aslotRᴾ d))
    conceal-endpoints = typed-endpoints
      (impreciseType endpoints) (＇ aslotXᴾ d)
      (impreciseEmbedded endpoints) canonical-source
      (imprecise-value endpoints) (precise-value endpoints ↓ seal)
      (imprecise-typed endpoints)
      (⊢conceal (⊢↓-seal (aliasBound (aatom d)))
        (precise-endpoint-type W targetᴾ related))

    at-every-index : ∀ (i : ℕ) → i ≤ suc j′
      → FutureValueRelation (I.alias eqm p) W future-refl i Vᴵ
          (Vᴾ ↓ seal (aslotXᴾ d) (aslotRᴾ d))
    at-every-index zero i≤j = ClosureProof.value-imprecision-reindex
      (I.alias eqm p) canonical {k = zero} (cong ＇_ Z-eq) refl
      conceal-endpoints
    at-every-index (suc i′) si≤j =
      ClosureProof.value-imprecision-reindex
        (I.alias eqm p) canonical {k = suc i′} (cong ＇_ Z-eq) refl
        (conceal-endpoints , produced i′ si≤j)
      where
      produced : ∀ i′ → suc i′ ≤ suc j′
        → AliasAtomHolds (ValueImprecisionᵏ (suc i′) W)
            (semanticEntry W (acenter d)) (amode-eq d) premise Vᴵ
            (Vᴾ ↓ seal (aslotXᴾ d) (aslotRᴾ d))
      produced i′ si≤j = alias-slot-produce d refl (amode-eq d) premise
        (alias-holds Vᴾ refl
          (value-imprecision-downward-to si≤j payload-rep))
  alias-conceal-go fuel j sz below W d {Bᴾ = ＇ Y} (I.X⊑★ eqm)
      size sourceᴾ q targetᴾ related | yes refl =
    ⊥-elim (alias-not-star (trans (sym (amode-eq d))
      (trans (cong (impEnv (core W))
        (trans (sym (aliasPreciseAligned (aatom d)))
          (var-injective sourceᴾ))) eqm)))
  alias-conceal-go fuel j sz below W d {Bᴾ = ‵ ι} p size sourceᴾ q
      targetᴾ related =
    ClosureProof.computations-related-reindex q p
      (trans (sym targetᴾ) sourceᴾ) refl refl refl
      (identity-conceal W q (‵ ι) related)
  alias-conceal-go fuel j sz below W d {Bᴾ = ★} p size sourceᴾ q
      targetᴾ related =
    ClosureProof.computations-related-reindex q p
      (trans (sym targetᴾ) sourceᴾ) refl refl refl
      (identity-conceal W q ★ related)
  alias-conceal-go zero j sz below W d {Bᴾ = A₀ ⇒ B₀} p () sourceᴾ q
      targetᴾ related
  alias-conceal-go (suc fuel) j sz below W d {Bᴾ = A₀ ⇒ B₀} p size
      sourceᴾ q targetᴾ related =
    related-values-return
      (imprecise-value endpoints) (precise-value endpoints ↓ fun)
      (λ i i≤j → alias-conceal-arrow fuel i sz
        (below-restrict i≤j ≤-refl below) W d p
        (size-bound-left size) (size-bound-right size) sourceᴾ
        q targetᴾ
        (value-imprecision-downward-to i≤j related))
    where
    endpoints = ClosureProof.value-imprecision-endpoints related
  alias-conceal-go fuel j sz below W d {Bᴾ = `∀ B₁} p size sourceᴾ q
      targetᴾ related =
    related-values-return
      (imprecise-value endpoints) (precise-value endpoints ↓ all)
      (λ i i≤j → alias-universal-conceal-value i sz
        (below-restrict i≤j ≤-refl below) W d p sourceᴾ q targetᴾ
        (value-imprecision-downward-to i≤j related))
    where
    endpoints = ClosureProof.value-imprecision-endpoints related

  -- Wrapping a related computation on the precise endpoint.

  alias-revealed-computations : ∀ (fuel j sz : ℕ) (below : Below j sz)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (d : AliasSlot W)
      {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → sizeᵗ Bᴾ ≤ fuel
    → embedPrecise (core W) Bᴾ ≡ Aᴾ
    → ∀ {Cᴾ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Aᴵ)
    → embedPrecise (core W) (replaceTy (aslotXᴾ d) (aslotRᴾ d) Bᴾ)
        ≡ Cᴾ
    → ∀ {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
    → ComputationsRelated W (FutureValueRelation p) j Mᴵ Mᴾ
    → ComputationsRelated W (FutureValueRelation q) j
        Mᴵ (Mᴾ ↑ 〖 aslotXᴾ d , aslotRᴾ d ↑ Bᴾ 〗)
  alias-revealed-computations fuel j sz below W d {Bᴾ = Bᴾ} p size
      sourceᴾ q targetᴾ {Mᴵ = Mᴵ} {Mᴾ = Mᴾ} related =
    reveal-precise-composition
      {R = FutureValueRelation p} {S = FutureValueRelation q}
      (reveal-frm 〖 aslotXᴾ d , aslotRᴾ d ↑ Bᴾ 〗) j Mᴵ Mᴾ
      plug-values related
    where
    plug-values : RevealPrecisePlugValues W (FutureValueRelation p)
        (FutureValueRelation q) j
        (reveal-frm 〖 aslotXᴾ d , aslotRᴾ d ↑ Bᴾ 〗)
    plug-values {W′ = W′} W≼W′ {χsᴾ = χsᴾ} {χsᴵ = χsᴵ}
        storeᴵ storeᴾ termsᴵ termsᴾ {j = i} i≤j {Vᴵ = Uᴵ} {Vᴾ = Uᴾ}
        value-related =
      computations-related-future-compose W≼W′ q
        (ClosureProof.computations-related-reindex
          (liftCenterImprecision W≼W′ q) (liftCenterImprecision W≼W′ q)
          refl refl refl
          (sym (transported-reveal-eq χsᴾ Mᴾ (aslotXᴾ d) (aslotRᴾ d) Bᴾ
            (trans (termsᴾ (Mᴾ ↑ 〖 aslotXᴾ d , aslotRᴾ d ↑ Bᴾ 〗))
              (trans (alias-lifted-reveal-precise d W≼W′ Mᴾ Bᴾ)
                (cong (λ M → M ↑ _) (sym (termsᴾ Mᴾ))))) Uᴾ))
          (alias-reveal-go fuel i sz (below-restrict i≤j ≤-refl below)
            W′ (alias-slot-future d W≼W′)
            (liftCenterImprecision W≼W′ p)
            (subst≡ (_≤ fuel) (sym (lift-sizeᵗ W≼W′ Bᴾ)) size)
            (trans (embedPrecise-lift W≼W′ Bᴾ)
              (cong (liftCenterTy W≼W′) sourceᴾ))
            (liftCenterImprecision W≼W′ q)
            (trans (cong (embedPrecise (core W′))
              (alias-replace-precise-lift d W≼W′ Bᴾ))
              (trans (embedPrecise-lift W≼W′ _)
                (cong (liftCenterTy W≼W′) targetᴾ)))
            value-related))

  alias-concealed-computations : ∀ (fuel j sz : ℕ)
      (below : Below j sz)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (d : AliasSlot W)
      {Bᴾ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → sizeᵗ Bᴾ ≤ fuel
    → embedPrecise (core W) Bᴾ ≡ Aᴾ
    → ∀ {Cᴾ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Aᴵ)
    → embedPrecise (core W) (replaceTy (aslotXᴾ d) (aslotRᴾ d) Bᴾ)
        ≡ Cᴾ
    → ∀ {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
    → ComputationsRelated W (FutureValueRelation q) j Mᴵ Mᴾ
    → ComputationsRelated W (FutureValueRelation p) j
        Mᴵ (Mᴾ ↓ makeConceal (aslotXᴾ d) (aslotRᴾ d) Bᴾ)
  alias-concealed-computations fuel j sz below W d {Bᴾ = Bᴾ} p size
      sourceᴾ q targetᴾ {Mᴵ = Mᴵ} {Mᴾ = Mᴾ} related =
    conceal-precise-composition
      {R = FutureValueRelation q} {S = FutureValueRelation p}
      (conceal-frm (makeConceal (aslotXᴾ d) (aslotRᴾ d) Bᴾ)) j Mᴵ Mᴾ
      plug-values related
    where
    plug-values : ConcealPrecisePlugValues W (FutureValueRelation q)
        (FutureValueRelation p) j
        (conceal-frm (makeConceal (aslotXᴾ d) (aslotRᴾ d) Bᴾ))
    plug-values {W′ = W′} W≼W′ {χsᴾ = χsᴾ} {χsᴵ = χsᴵ}
        storeᴵ storeᴾ termsᴵ termsᴾ {j = i} i≤j {Vᴵ = Uᴵ} {Vᴾ = Uᴾ}
        value-related =
      computations-related-future-compose W≼W′ p
        (ClosureProof.computations-related-reindex
          (liftCenterImprecision W≼W′ p) (liftCenterImprecision W≼W′ p)
          refl refl refl
          (sym (transported-conceal-eq χsᴾ Mᴾ (aslotXᴾ d) (aslotRᴾ d)
            Bᴾ
            (trans
              (termsᴾ (Mᴾ ↓ makeConceal (aslotXᴾ d) (aslotRᴾ d) Bᴾ))
              (trans (alias-lifted-conceal-precise d W≼W′ Mᴾ Bᴾ)
                (cong (λ M → M ↓ _) (sym (termsᴾ Mᴾ))))) Uᴾ))
          (alias-conceal-go fuel i sz (below-restrict i≤j ≤-refl below)
            W′ (alias-slot-future d W≼W′)
            (liftCenterImprecision W≼W′ p)
            (subst≡ (_≤ fuel) (sym (lift-sizeᵗ W≼W′ Bᴾ)) size)
            (trans (embedPrecise-lift W≼W′ Bᴾ)
              (cong (liftCenterTy W≼W′) sourceᴾ))
            (liftCenterImprecision W≼W′ q)
            (trans (cong (embedPrecise (core W′))
              (alias-replace-precise-lift d W≼W′ Bᴾ))
              (trans (embedPrecise-lift W≼W′ _)
                (cong (liftCenterTy W≼W′) targetᴾ)))
            value-related))

  -- One head of the wrapped function value: the precise endpoint
  -- redistributes the wrapper over the application.

  alias-reveal-arrow-head : ∀ (fuel m sz : ℕ)
      (below : Below (suc m) sz)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (d : AliasSlot W)
      {A₀ B₀ : Ty Δᴾ} {Pᴵ Qᴵ : Ty Δᶜ}
      (p₁ : impEnv (core W) I.⊢ embedPrecise (core W) A₀ ⊑ Pᴵ)
      (p₂ : impEnv (core W) I.⊢ embedPrecise (core W) B₀ ⊑ Qᴵ)
      (q₁ : impEnv (core W) I.⊢ embedPrecise (core W)
        (replaceTy (aslotXᴾ d) (aslotRᴾ d) A₀) ⊑ Pᴵ)
      (q₂ : impEnv (core W) I.⊢ embedPrecise (core W)
        (replaceTy (aslotXᴾ d) (aslotRᴾ d) B₀) ⊑ Qᴵ)
    → sizeᵗ A₀ ≤ fuel → sizeᵗ B₀ ≤ fuel
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W (I.⇒⊑⇒ p₁ p₂) (suc m) Vᴵ Vᴾ
    → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′) (W≼W′ : Future W W′)
        {Uᴵ : Term Δᴵ′} {Uᴾ : Term Δᴾ′}
    → ValueImprecisionᵏ (suc m) W′ (liftCenterImprecision W≼W′ q₁)
        Uᴵ Uᴾ
    → ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) (suc m)
        (liftImpreciseTerm W≼W′ Vᴵ · Uᴵ)
        (liftPreciseTerm W≼W′
          (Vᴾ ↑ 〖 aslotXᴾ d , aslotRᴾ d ↑ A₀ ⇒ B₀ 〗) · Uᴾ)
  alias-reveal-arrow-head fuel m sz below W d {A₀ = A₀} {B₀ = B₀}
      p₁ p₂ q₁ q₂ sizeA sizeB {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} function-related
      W′ W≼W′ {Uᴵ = Uᴵ} {Uᴾ = Uᴾ} argument-related =
    ClosureProof.computations-related-reindex
      (liftCenterImprecision W≼W′ q₂) (liftCenterImprecision W≼W′ q₂)
      refl refl refl (sym precise-redex-eq) expanded
    where
    d′ = alias-slot-future d W≼W′
    A′ = liftPreciseTy W≼W′ A₀
    B′ = liftPreciseTy W≼W′ B₀
    cᴾ = makeConceal (aslotXᴾ d′) (aslotRᴾ d′) A′
    dᴾ = 〖 aslotXᴾ d′ , aslotRᴾ d′ ↑ B′ 〗
    Vᴾ′ = liftPreciseTerm W≼W′ Vᴾ
    Vᴵ′ = liftImpreciseTerm W≼W′ Vᴵ

    precise-redex-eq :
        liftPreciseTerm W≼W′
          (Vᴾ ↑ 〖 aslotXᴾ d , aslotRᴾ d ↑ A₀ ⇒ B₀ 〗) · Uᴾ
        ≡ (Vᴾ′ ↑ (cᴾ ↦↑ dᴾ)) · Uᴾ
    precise-redex-eq
        rewrite alias-lifted-reveal-precise d W≼W′ Vᴾ (A₀ ⇒ B₀)
              | liftPreciseTy-arrow W≼W′ A₀ B₀ = refl

    argument-endpoints =
      ClosureProof.value-imprecision-endpoints argument-related

    lifted-function : ValueImprecision W′
        (I.⇒⊑⇒ (liftCenterImprecision W≼W′ p₁)
          (liftCenterImprecision W≼W′ p₂)) (suc m) Vᴵ′ Vᴾ′
    lifted-function = ClosureProof.value-imprecision-reindex
      (I.⇒⊑⇒ (liftCenterImprecision W≼W′ p₁)
        (liftCenterImprecision W≼W′ p₂))
      (liftCenterImprecision W≼W′ (I.⇒⊑⇒ p₁ p₂))
      (sym (liftCenterTy-arrow W≼W′ _ _))
      (sym (liftCenterTy-arrow W≼W′ _ _))
      (ClosureProof.value-imprecision-future
        {W = W} {p = I.⇒⊑⇒ p₁ p₂} {k = suc m} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
        W≼W′ function-related)

    concealed : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ p₁)) (suc m)
        Uᴵ (Uᴾ ↓ cᴾ)
    concealed = alias-conceal-go fuel (suc m) sz below W′ d′
      (liftCenterImprecision W≼W′ p₁)
      (subst≡ (_≤ fuel) (sym (lift-sizeᵗ W≼W′ A₀)) sizeA)
      (embedPrecise-lift W≼W′ A₀)
      (liftCenterImprecision W≼W′ q₁)
      (trans (cong (embedPrecise (core W′))
        (alias-replace-precise-lift d W≼W′ A₀))
        (embedPrecise-lift W≼W′ _))
      argument-related

    applied : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ p₂)) (suc m)
        (Vᴵ′ · Uᴵ) (Vᴾ′ · (Uᴾ ↓ cᴾ))
    applied = related-application-computation lifted-function concealed

    contracted : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) (suc m)
        (Vᴵ′ · Uᴵ) ((Vᴾ′ · (Uᴾ ↓ cᴾ)) ↑ dᴾ)
    contracted = alias-revealed-computations fuel (suc m) sz below W′ d′
      (liftCenterImprecision W≼W′ p₂)
      (subst≡ (_≤ fuel) (sym (lift-sizeᵗ W≼W′ B₀)) sizeB)
      (embedPrecise-lift W≼W′ B₀)
      (liftCenterImprecision W≼W′ q₂)
      (trans (cong (embedPrecise (core W′))
        (alias-replace-precise-lift d W≼W′ B₀))
        (embedPrecise-lift W≼W′ _))
      applied

    expanded : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) (suc m)
        (Vᴵ′ · Uᴵ) ((Vᴾ′ ↑ (cᴾ ↦↑ dᴾ)) · Uᴾ)
    expanded
        with reveal-fun-app-step-question
               {Σ = preciseStore (core W′)} cᴾ dᴾ
               (precise-value function-endpoints)
               (precise-value argument-endpoints)
      where
      function-endpoints = ClosureProof.value-imprecision-endpoints
        {W = W′}
        {p = I.⇒⊑⇒ (liftCenterImprecision W≼W′ p₁)
          (liftCenterImprecision W≼W′ p₂)}
        {k = suc m} {Vᴵ = Vᴵ′} {Vᴾ = Vᴾ′} lifted-function
    expanded | vVᴾ , vUᴾ , step-eqᴾ =
      related-precise-keep-step-expand (λ ())
        (reveal-fun-app-value-none cᴾ dᴾ)
        (pure-step (β-reveal-⇒ vVᴾ vUᴾ)) step-eqᴾ contracted

  alias-conceal-arrow-head : ∀ (fuel m sz : ℕ)
      (below : Below (suc m) sz)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (d : AliasSlot W)
      {A₀ B₀ : Ty Δᴾ} {Pᴵ Qᴵ : Ty Δᶜ}
      (p₁ : impEnv (core W) I.⊢ embedPrecise (core W) A₀ ⊑ Pᴵ)
      (p₂ : impEnv (core W) I.⊢ embedPrecise (core W) B₀ ⊑ Qᴵ)
      (q₁ : impEnv (core W) I.⊢ embedPrecise (core W)
        (replaceTy (aslotXᴾ d) (aslotRᴾ d) A₀) ⊑ Pᴵ)
      (q₂ : impEnv (core W) I.⊢ embedPrecise (core W)
        (replaceTy (aslotXᴾ d) (aslotRᴾ d) B₀) ⊑ Qᴵ)
    → sizeᵗ A₀ ≤ fuel → sizeᵗ B₀ ≤ fuel
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W (I.⇒⊑⇒ q₁ q₂) (suc m) Vᴵ Vᴾ
    → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′) (W≼W′ : Future W W′)
        {Uᴵ : Term Δᴵ′} {Uᴾ : Term Δᴾ′}
    → ValueImprecisionᵏ (suc m) W′ (liftCenterImprecision W≼W′ p₁)
        Uᴵ Uᴾ
    → ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ p₂)) (suc m)
        (liftImpreciseTerm W≼W′ Vᴵ · Uᴵ)
        (liftPreciseTerm W≼W′
          (Vᴾ ↓ makeConceal (aslotXᴾ d) (aslotRᴾ d) (A₀ ⇒ B₀)) · Uᴾ)
  alias-conceal-arrow-head fuel m sz below W d {A₀ = A₀} {B₀ = B₀}
      p₁ p₂ q₁ q₂ sizeA sizeB {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} function-related
      W′ W≼W′ {Uᴵ = Uᴵ} {Uᴾ = Uᴾ} argument-related =
    ClosureProof.computations-related-reindex
      (liftCenterImprecision W≼W′ p₂) (liftCenterImprecision W≼W′ p₂)
      refl refl refl (sym precise-redex-eq) expanded
    where
    d′ = alias-slot-future d W≼W′
    A′ = liftPreciseTy W≼W′ A₀
    B′ = liftPreciseTy W≼W′ B₀
    cᴾ = 〖 aslotXᴾ d′ , aslotRᴾ d′ ↑ A′ 〗
    dᴾ = makeConceal (aslotXᴾ d′) (aslotRᴾ d′) B′
    Vᴾ′ = liftPreciseTerm W≼W′ Vᴾ
    Vᴵ′ = liftImpreciseTerm W≼W′ Vᴵ

    precise-redex-eq :
        liftPreciseTerm W≼W′
          (Vᴾ ↓ makeConceal (aslotXᴾ d) (aslotRᴾ d) (A₀ ⇒ B₀)) · Uᴾ
        ≡ (Vᴾ′ ↓ (cᴾ ↦↓ dᴾ)) · Uᴾ
    precise-redex-eq
        rewrite alias-lifted-conceal-precise d W≼W′ Vᴾ (A₀ ⇒ B₀)
              | liftPreciseTy-arrow W≼W′ A₀ B₀ = refl

    argument-endpoints =
      ClosureProof.value-imprecision-endpoints argument-related

    lifted-function : ValueImprecision W′
        (I.⇒⊑⇒ (liftCenterImprecision W≼W′ q₁)
          (liftCenterImprecision W≼W′ q₂)) (suc m) Vᴵ′ Vᴾ′
    lifted-function = ClosureProof.value-imprecision-reindex
      (I.⇒⊑⇒ (liftCenterImprecision W≼W′ q₁)
        (liftCenterImprecision W≼W′ q₂))
      (liftCenterImprecision W≼W′ (I.⇒⊑⇒ q₁ q₂))
      (sym (liftCenterTy-arrow W≼W′ _ _))
      (sym (liftCenterTy-arrow W≼W′ _ _))
      (ClosureProof.value-imprecision-future
        {W = W} {p = I.⇒⊑⇒ q₁ q₂} {k = suc m} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
        W≼W′ function-related)

    revealed : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₁)) (suc m)
        Uᴵ (Uᴾ ↑ cᴾ)
    revealed = alias-reveal-go fuel (suc m) sz below W′ d′
      (liftCenterImprecision W≼W′ p₁)
      (subst≡ (_≤ fuel) (sym (lift-sizeᵗ W≼W′ A₀)) sizeA)
      (embedPrecise-lift W≼W′ A₀)
      (liftCenterImprecision W≼W′ q₁)
      (trans (cong (embedPrecise (core W′))
        (alias-replace-precise-lift d W≼W′ A₀))
        (embedPrecise-lift W≼W′ _))
      argument-related

    applied : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₂)) (suc m)
        (Vᴵ′ · Uᴵ) (Vᴾ′ · (Uᴾ ↑ cᴾ))
    applied = related-application-computation lifted-function revealed

    contracted : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ p₂)) (suc m)
        (Vᴵ′ · Uᴵ) ((Vᴾ′ · (Uᴾ ↑ cᴾ)) ↓ dᴾ)
    contracted = alias-concealed-computations fuel (suc m) sz below
      W′ d′
      (liftCenterImprecision W≼W′ p₂)
      (subst≡ (_≤ fuel) (sym (lift-sizeᵗ W≼W′ B₀)) sizeB)
      (embedPrecise-lift W≼W′ B₀)
      (liftCenterImprecision W≼W′ q₂)
      (trans (cong (embedPrecise (core W′))
        (alias-replace-precise-lift d W≼W′ B₀))
        (embedPrecise-lift W≼W′ _))
      applied

    expanded : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ p₂)) (suc m)
        (Vᴵ′ · Uᴵ) ((Vᴾ′ ↓ (cᴾ ↦↓ dᴾ)) · Uᴾ)
    expanded
        with conceal-fun-app-step-question
               {Σ = preciseStore (core W′)} cᴾ dᴾ
               (precise-value function-endpoints)
               (precise-value argument-endpoints)
      where
      function-endpoints = ClosureProof.value-imprecision-endpoints
        {W = W′}
        {p = I.⇒⊑⇒ (liftCenterImprecision W≼W′ q₁)
          (liftCenterImprecision W≼W′ q₂)}
        {k = suc m} {Vᴵ = Vᴵ′} {Vᴾ = Vᴾ′} lifted-function
    expanded | vVᴾ , vUᴾ , step-eqᴾ =
      related-precise-keep-step-expand (λ ())
        (conceal-fun-app-value-none cᴾ dᴾ)
        (pure-step (β-conceal-⇒ vVᴾ vUᴾ)) step-eqᴾ contracted

  -- The value relation of a wrapped function value.

  alias-reveal-arrow : ∀ (fuel j sz : ℕ) (below : Below j sz)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (d : AliasSlot W)
      {A₀ B₀ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → sizeᵗ A₀ ≤ fuel → sizeᵗ B₀ ≤ fuel
    → embedPrecise (core W) (A₀ ⇒ B₀) ≡ Aᴾ
    → ∀ {Cᴾ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Aᴵ)
    → embedPrecise (core W)
        (replaceTy (aslotXᴾ d) (aslotRᴾ d) (A₀ ⇒ B₀)) ≡ Cᴾ
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W p j Vᴵ Vᴾ
    → ValueImprecision W q j
        Vᴵ (Vᴾ ↑ 〖 aslotXᴾ d , aslotRᴾ d ↑ A₀ ⇒ B₀ 〗)
  alias-reveal-arrow fuel zero sz below W d p sizeA sizeB sourceᴾ q
      targetᴾ related =
    alias-reveal-endpoints W d p sourceᴾ q targetᴾ endpoints
      (precise-value endpoints ↑ fun)
    where
    endpoints = ClosureProof.value-imprecision-endpoints
      {k = zero} related
  alias-reveal-arrow fuel (suc i) sz below W d p sizeA sizeB sourceᴾ q
      targetᴾ related with sourceᴾ
  alias-reveal-arrow fuel (suc i) sz below W d p sizeA sizeB sourceᴾ q
      targetᴾ related | refl with arrow-source-view p
  alias-reveal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑⇒ p₁ p₂) sizeA sizeB sourceᴾ q targetᴾ related
      | refl | arrow-arrow p₁ p₂ with targetᴾ
  alias-reveal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑⇒ p₁ p₂) sizeA sizeB sourceᴾ q targetᴾ related
      | refl | arrow-arrow p₁ p₂ | refl
      with arrow-imprecision-view q
  alias-reveal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑⇒ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑⇒ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
      | refl | arrow-arrow p₁ p₂ | refl
      | arrow-imprecision q₁ q₂ =
    alias-reveal-endpoints W d (I.⇒⊑⇒ p₁ p₂) sourceᴾ (I.⇒⊑⇒ q₁ q₂)
      targetᴾ endpoints
      (precise-value endpoints ↑ fun) ,
    functions (suc i) ≤-refl related
    where
    endpoints = ClosureProof.value-imprecision-endpoints
      {W = W} {p = I.⇒⊑⇒ p₁ p₂} {k = suc i} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
      related

    functions : ∀ (m : ℕ) → m ≤ suc i
      → ValueImprecision W (I.⇒⊑⇒ p₁ p₂) m Vᴵ Vᴾ
      → FunctionsRelated W q₁ q₂ m Vᴵ
          (Vᴾ ↑ 〖 aslotXᴾ d , aslotRᴾ d ↑ A₀ ⇒ B₀ 〗)
    functions zero m≤ rel = tt
    functions (suc m) sm≤ rel =
      (λ W′ W≼W′ argument-related →
        alias-reveal-arrow-head fuel m sz
          (below-restrict sm≤ ≤-refl below) W d p₁ p₂ q₁ q₂
          sizeA sizeB rel W′ W≼W′ argument-related) ,
      functions m (≤-trans (n≤1+n m) sm≤)
        (value-imprecision-downward-to
          {W = W} {p = I.⇒⊑⇒ p₁ p₂} {j = m} {k = suc m}
          {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (n≤1+n m) rel)
  alias-reveal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ q targetᴾ related
      | refl | arrow-star p₁ p₂ with targetᴾ
  alias-reveal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ q targetᴾ related
      | refl | arrow-star p₁ p₂ | refl
      with arrow-source-view q
  alias-reveal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑★ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (endpoints , shape , payload)
      | refl | arrow-star p₁ p₂ | refl
      | arrow-star q₁ q₂
      with right-imprecise-ground shape in g-eq
         | right-imprecise-ground-proof shape
         | right-payload-imprecision shape
  alias-reveal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑★ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (endpoints , shape , payload)
      | refl | arrow-star p₁ p₂ | refl
      | arrow-star q₁ q₂
      | _ | ＇ X | ()
  alias-reveal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑★ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (endpoints , shape , payload)
      | refl | arrow-star p₁ p₂ | refl
      | arrow-star q₁ q₂
      | _ | ‵ ι | ()
  alias-reveal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑★ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (endpoints , shape , payload)
      | refl | arrow-star p₁ p₂ | refl
      | arrow-star q₁ q₂
      | _ | ∀★ | ()
  alias-reveal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑★ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (endpoints , shape , payload)
      | refl | arrow-star p₁ p₂ | refl
      | arrow-star q₁ q₂
      | _ | ★⇒★ | w =
    alias-reveal-endpoints W d (I.⇒⊑★ p₁ p₂) sourceᴾ (I.⇒⊑★ q₁ q₂)
      targetᴾ endpoints
      (precise-value endpoints ↑ fun) ,
    shape′ ,
    payload′
    where
    payload-back : ValueImprecision W
        (right-payload-imprecision shape) i
        (right-dynamic-imprecise-payload shape) Vᴾ
    payload-back = ClosureProof.value-imprecision-reindex
      (right-payload-imprecision shape) w refl
      (cong (embedImprecise (core W)) g-eq) payload

    new-imprecision : impEnv (core W) I.⊢
        embedPrecise (core W)
          (replaceTy (aslotXᴾ d) (aslotRᴾ d) A₀)
        ⇒ embedPrecise (core W)
          (replaceTy (aslotXᴾ d) (aslotRᴾ d) B₀)
        ⊑ embedImprecise (core W) (right-imprecise-ground shape)
    new-imprecision = subst≡
      (λ G → impEnv (core W) I.⊢
        embedPrecise (core W)
          (replaceTy (aslotXᴾ d) (aslotRᴾ d) A₀)
        ⇒ embedPrecise (core W)
          (replaceTy (aslotXᴾ d) (aslotRᴾ d) B₀)
        ⊑ embedImprecise (core W) G)
      (sym g-eq) (I.⇒⊑⇒ q₁ q₂)

    shape′ : RightDynamicPayloadShape W
        (embedPrecise (core W)
          (replaceTy (aslotXᴾ d) (aslotRᴾ d) A₀)
        ⇒ embedPrecise (core W)
          (replaceTy (aslotXᴾ d) (aslotRᴾ d) B₀)) Vᴵ
    shape′ = right-dynamic-payload-shape
      (right-imprecise-ground shape)
      (right-imprecise-ground-proof shape)
      (right-imprecise-consistency-env shape)
      (right-imprecise-ground-to-star shape)
      (right-dynamic-imprecise-payload shape)
      (right-dynamic-imprecise-shape shape)
      new-imprecision

    recursive : ValueImprecision W (I.⇒⊑⇒ q₁ q₂) i
        (right-dynamic-imprecise-payload shape)
        (Vᴾ ↑ 〖 aslotXᴾ d , aslotRᴾ d ↑ A₀ ⇒ B₀ 〗)
    recursive = alias-reveal-arrow fuel i sz
      (below-restrict (n≤1+n i) ≤-refl below) W d w
      sizeA sizeB refl (I.⇒⊑⇒ q₁ q₂) refl payload

    payload′ : ValueImprecision W
        (right-payload-imprecision shape′) i
        (right-dynamic-imprecise-payload shape)
        (Vᴾ ↑ 〖 aslotXᴾ d , aslotRᴾ d ↑ A₀ ⇒ B₀ 〗)
    payload′ = ClosureProof.value-imprecision-reindex
      new-imprecision (I.⇒⊑⇒ q₁ q₂) refl
      (cong (embedImprecise (core W)) g-eq) recursive

  alias-conceal-arrow : ∀ (fuel j sz : ℕ) (below : Below j sz)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (d : AliasSlot W)
      {A₀ B₀ : Ty Δᴾ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → sizeᵗ A₀ ≤ fuel → sizeᵗ B₀ ≤ fuel
    → embedPrecise (core W) (A₀ ⇒ B₀) ≡ Aᴾ
    → ∀ {Cᴾ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Cᴾ ⊑ Aᴵ)
    → embedPrecise (core W)
        (replaceTy (aslotXᴾ d) (aslotRᴾ d) (A₀ ⇒ B₀)) ≡ Cᴾ
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W q j Vᴵ Vᴾ
    → ValueImprecision W p j
        Vᴵ (Vᴾ ↓ makeConceal (aslotXᴾ d) (aslotRᴾ d) (A₀ ⇒ B₀))
  alias-conceal-arrow fuel zero sz below W d p sizeA sizeB sourceᴾ q
      targetᴾ related =
    alias-conceal-endpoints W d p sourceᴾ q targetᴾ endpoints
      (precise-value endpoints ↓ fun)
    where
    endpoints = ClosureProof.value-imprecision-endpoints
      {k = zero} related
  alias-conceal-arrow fuel (suc i) sz below W d p sizeA sizeB sourceᴾ q
      targetᴾ related with sourceᴾ
  alias-conceal-arrow fuel (suc i) sz below W d p sizeA sizeB sourceᴾ q
      targetᴾ related | refl with arrow-source-view p
  alias-conceal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑⇒ p₁ p₂) sizeA sizeB sourceᴾ q targetᴾ related
      | refl | arrow-arrow p₁ p₂ with targetᴾ
  alias-conceal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑⇒ p₁ p₂) sizeA sizeB sourceᴾ q targetᴾ related
      | refl | arrow-arrow p₁ p₂ | refl
      with arrow-imprecision-view q
  alias-conceal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑⇒ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑⇒ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
      | refl | arrow-arrow p₁ p₂ | refl
      | arrow-imprecision q₁ q₂ =
    alias-conceal-endpoints W d (I.⇒⊑⇒ p₁ p₂) sourceᴾ (I.⇒⊑⇒ q₁ q₂)
      targetᴾ endpoints
      (precise-value endpoints ↓ fun) ,
    functions (suc i) ≤-refl related
    where
    endpoints = ClosureProof.value-imprecision-endpoints
      {W = W} {p = I.⇒⊑⇒ q₁ q₂} {k = suc i} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
      related

    functions : ∀ (m : ℕ) → m ≤ suc i
      → ValueImprecision W (I.⇒⊑⇒ q₁ q₂) m Vᴵ Vᴾ
      → FunctionsRelated W p₁ p₂ m Vᴵ
          (Vᴾ ↓ makeConceal (aslotXᴾ d) (aslotRᴾ d) (A₀ ⇒ B₀))
    functions zero m≤ rel = tt
    functions (suc m) sm≤ rel =
      (λ W′ W≼W′ argument-related →
        alias-conceal-arrow-head fuel m sz
          (below-restrict sm≤ ≤-refl below) W d p₁ p₂ q₁ q₂
          sizeA sizeB rel W′ W≼W′ argument-related) ,
      functions m (≤-trans (n≤1+n m) sm≤)
        (value-imprecision-downward-to
          {W = W} {p = I.⇒⊑⇒ q₁ q₂} {j = m} {k = suc m}
          {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (n≤1+n m) rel)
  alias-conceal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ q targetᴾ related
      | refl | arrow-star p₁ p₂ with targetᴾ
  alias-conceal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ q targetᴾ related
      | refl | arrow-star p₁ p₂ | refl
      with arrow-source-view q
  alias-conceal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑★ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (endpoints , shape , payload)
      | refl | arrow-star p₁ p₂ | refl
      | arrow-star q₁ q₂
      with right-imprecise-ground shape in g-eq
         | right-imprecise-ground-proof shape
         | right-payload-imprecision shape
  alias-conceal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑★ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (endpoints , shape , payload)
      | refl | arrow-star p₁ p₂ | refl
      | arrow-star q₁ q₂
      | _ | ＇ X | ()
  alias-conceal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑★ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (endpoints , shape , payload)
      | refl | arrow-star p₁ p₂ | refl
      | arrow-star q₁ q₂
      | _ | ‵ ι | ()
  alias-conceal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑★ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (endpoints , shape , payload)
      | refl | arrow-star p₁ p₂ | refl
      | arrow-star q₁ q₂
      | _ | ∀★ | ()
  alias-conceal-arrow fuel (suc i) sz below W d {A₀ = A₀} {B₀ = B₀}
      .(I.⇒⊑★ p₁ p₂) sizeA sizeB sourceᴾ .(I.⇒⊑★ q₁ q₂) targetᴾ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (endpoints , shape , payload)
      | refl | arrow-star p₁ p₂ | refl
      | arrow-star q₁ q₂
      | _ | ★⇒★ | w =
    alias-conceal-endpoints W d (I.⇒⊑★ p₁ p₂) sourceᴾ (I.⇒⊑★ q₁ q₂)
      targetᴾ endpoints
      (precise-value endpoints ↓ fun) ,
    shape′ ,
    payload′
    where
    payload-back : ValueImprecision W
        (right-payload-imprecision shape) i
        (right-dynamic-imprecise-payload shape) Vᴾ
    payload-back = ClosureProof.value-imprecision-reindex
      (right-payload-imprecision shape) w refl
      (cong (embedImprecise (core W)) g-eq) payload

    new-imprecision : impEnv (core W) I.⊢
        embedPrecise (core W) A₀ ⇒ embedPrecise (core W) B₀
        ⊑ embedImprecise (core W) (right-imprecise-ground shape)
    new-imprecision = subst≡
      (λ G → impEnv (core W) I.⊢
        embedPrecise (core W) A₀ ⇒ embedPrecise (core W) B₀
        ⊑ embedImprecise (core W) G)
      (sym g-eq) (I.⇒⊑⇒ p₁ p₂)

    shape′ : RightDynamicPayloadShape W
        (embedPrecise (core W) A₀ ⇒ embedPrecise (core W) B₀) Vᴵ
    shape′ = right-dynamic-payload-shape
      (right-imprecise-ground shape)
      (right-imprecise-ground-proof shape)
      (right-imprecise-consistency-env shape)
      (right-imprecise-ground-to-star shape)
      (right-dynamic-imprecise-payload shape)
      (right-dynamic-imprecise-shape shape)
      new-imprecision

    recursive : ValueImprecision W (I.⇒⊑⇒ p₁ p₂) i
        (right-dynamic-imprecise-payload shape)
        (Vᴾ ↓ makeConceal (aslotXᴾ d) (aslotRᴾ d) (A₀ ⇒ B₀))
    recursive = alias-conceal-arrow fuel i sz
      (below-restrict (n≤1+n i) ≤-refl below) W d
      (I.⇒⊑⇒ p₁ p₂)
      sizeA sizeB refl w refl payload

    payload′ : ValueImprecision W
        (right-payload-imprecision shape′) i
        (right-dynamic-imprecise-payload shape)
        (Vᴾ ↓ makeConceal (aslotXᴾ d) (aslotRᴾ d) (A₀ ⇒ B₀))
    payload′ = ClosureProof.value-imprecision-reindex
      new-imprecision (I.⇒⊑⇒ p₁ p₂) refl
      (cong (embedImprecise (core W)) g-eq) recursive

------------------------------------------------------------------------
-- The alias reveal and conceal, with the fuel instantiated
------------------------------------------------------------------------

alias-reveal : ∀ {k sz : ℕ} → Below k sz → AliasRevealAt k
alias-reveal {k = k} below W d {Bᴾ = Bᴾ} p sourceᴾ q targetᴾ related =
  alias-reveal-go (sizeᵗ Bᴾ) k _ below W d p ≤-refl sourceᴾ q targetᴾ
    related

alias-conceal : ∀ {k sz : ℕ} → Below k sz → AliasConcealAt k
alias-conceal {k = k} below W d {Bᴾ = Bᴾ} p sourceᴾ q targetᴾ related =
  alias-conceal-go (sizeᵗ Bᴾ) k _ below W d p ≤-refl sourceᴾ q targetᴾ
    related
