module proof.LR-narrow.TargetSlot where

-- File Charter:
--   * Lifts target-only slots through arbitrary future worlds.
--   * Tracks the target variable and runtime representative retained by the
--     semantic atom, without adding a right-alias clause to ordinary type
--     imprecision.
--   * Supplies the scoped target-slot infrastructure for pending-bind proofs.

open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; cong₂; sym; trans)

open import Types
open import CastTerms using (Term; _↑_)
open import Conversion using (replaceTy; 〖_,_↑_〗)
open import LR-narrow.World
open import LR-narrow.SlotSequence
open import proof.LR-narrow.RevealLifting using
  (liftImpreciseTy-replace; liftImpreciseTerm-reveal)
open import proof.LR-narrow.TypeRenamingComposition using (pack↑; apply↑)

record TargetEntryLift {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {Z : TyVar Δᶜ}
    (a : TargetSemanticAtom (core W) Z) {mode′}
    (e′ : SemanticEntry (core W′) (liftCenterVariable W≼W′ Z) mode′)
    : Set where
  constructor target-entry-lift
  field
    tlifted-atom :
      TargetSemanticAtom (core W′) (liftCenterVariable W≼W′ Z)
    tlifted-entry-is : IsTargetEntry tlifted-atom e′
    tlifted-imprecise-variable : targetImpreciseVariable tlifted-atom
      ≡ liftImpreciseVariable W≼W′ (targetImpreciseVariable a)
    tlifted-rep : targetRep tlifted-atom
      ≡ liftImpreciseTy W≼W′ (targetRep a)

open TargetEntryLift public

target-entry-lift-view : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {Z : TyVar Δᶜ}
    (a : TargetSemanticAtom (core W) Z) {mode′}
    {e′ : SemanticEntry (core W′) (liftCenterVariable W≼W′ Z) mode′}
  → EntryLift W≼W′ (target-entry a) e′
  → TargetEntryLift W≼W′ a e′
target-entry-lift-view W≼W′ a (lift-target eqX eqR) =
  target-entry-lift _ is-target eqX eqR

target-view-entry-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {W≼W′ : Future W W′} {Z : TyVar Δᶜ}
    {a : TargetSemanticAtom (core W) Z} {mode mode′}
    {e : SemanticEntry (core W) Z mode}
    {e′ : SemanticEntry (core W′) (liftCenterVariable W≼W′ Z) mode′}
  → IsTargetEntry a e
  → EntryLift W≼W′ e e′
  → EntryLift W≼W′ (target-entry a) e′
target-view-entry-lift is-target lifted = lifted

target-slot-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (t : TargetSlot W) (W≼W′ : Future W W′)
  → TargetEntryLift W≼W′ (tatom t)
      (semanticEntry W′ (liftCenterVariable W≼W′ (tcenter t)))
target-slot-lift t W≼W′ = target-entry-lift-view W≼W′ (tatom t)
  (target-view-entry-lift (tentry-is t)
    (entry-future W≼W′ (tcenter t)))

target-slot-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → TargetSlot W → (W≼W′ : Future W W′) → TargetSlot W′
target-slot-future t W≼W′ = target-slot
  (liftCenterVariable W≼W′ (tcenter t))
  (tlifted-atom (target-slot-lift t W≼W′))
  (tlifted-entry-is (target-slot-lift t W≼W′))

target-slot-imprecise-variable-lift : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (t : TargetSlot W) (W≼W′ : Future W W′)
  → tslotXᴵ (target-slot-future t W≼W′)
      ≡ liftImpreciseVariable W≼W′ (tslotXᴵ t)
target-slot-imprecise-variable-lift t W≼W′ =
  tlifted-imprecise-variable (target-slot-lift t W≼W′)

target-slot-imprecise-rep-lift : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (t : TargetSlot W) (W≼W′ : Future W W′)
  → tslotRᴵ (target-slot-future t W≼W′)
      ≡ liftImpreciseTy W≼W′ (tslotRᴵ t)
target-slot-imprecise-rep-lift t W≼W′ =
  tlifted-rep (target-slot-lift t W≼W′)

target-replace-imprecise-lift : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (t : TargetSlot W) (W≼W′ : Future W W′) (B : Ty Δᴵ)
  → replaceTy (tslotXᴵ (target-slot-future t W≼W′))
      (tslotRᴵ (target-slot-future t W≼W′))
      (liftImpreciseTy W≼W′ B)
    ≡ liftImpreciseTy W≼W′
        (replaceTy (tslotXᴵ t) (tslotRᴵ t) B)
target-replace-imprecise-lift t W≼W′ B =
  trans (cong₂ (λ X R → replaceTy X R (liftImpreciseTy W≼W′ B))
    (target-slot-imprecise-variable-lift t W≼W′)
    (target-slot-imprecise-rep-lift t W≼W′))
    (sym (liftImpreciseTy-replace W≼W′
      (tslotXᴵ t) (tslotRᴵ t) B))

lifted-target-reveal : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (t : TargetSlot W) (W≼W′ : Future W W′) (V : Term Δᴵ) (B : Ty Δᴵ)
  → liftImpreciseTerm W≼W′ (V ↑ 〖 tslotXᴵ t , tslotRᴵ t ↑ B 〗)
    ≡ liftImpreciseTerm W≼W′ V
        ↑ 〖 tslotXᴵ (target-slot-future t W≼W′)
            , tslotRᴵ (target-slot-future t W≼W′)
            ↑ liftImpreciseTy W≼W′ B 〗
lifted-target-reveal t W≼W′ V B =
  trans (liftImpreciseTerm-reveal W≼W′ V
      (tslotXᴵ t) (tslotRᴵ t) B)
    (cong (apply↑ (liftImpreciseTerm W≼W′ V))
      (cong₂ (λ X R → pack↑
          〖 X , R ↑ liftImpreciseTy W≼W′ B 〗)
        (sym (target-slot-imprecise-variable-lift t W≼W′))
        (sym (target-slot-imprecise-rep-lift t W≼W′))))
