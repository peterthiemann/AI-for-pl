module proof.LR-narrow.TargetSlot where

-- File Charter:
--   * Lifts target-slot replacement types and reveal terms through futures.
--   * Uses the core target-slot transport in `LR-narrow.SlotSequence`.
--   * Supplies syntactic coherence for scoped pending-bind proofs.

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
