module proof.LR-narrow.PendingTargetFrame where

-- File Charter:
--   * Turns the scoped pending target relation into an ordinary related
--     computation by applying the target slot's structural reveal.
--   * Uses the generic imprecise-side frame composition theorem; ordinary
--     type imprecision remains unchanged.

open import Data.Nat using (ℕ; _≤_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; refl; subst; sym; trans)

open import Types
open import CastTerms using (Term; Value; _↑_)
open import Conversion using (〖_,_↑_〗)
open import LR-narrow.World
open import LR-narrow.SlotSequence
open import LR-narrow.PendingTarget using (TargetTransparent)
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.Closure using (value-imprecision-downward-to)
import proof.LR-narrow.Closure as ClosureProof
open import proof.LR-narrow.ImmediateReturn using (related-values-return)
open import proof.LR-narrow.FramePhases using (Frame)
open import proof.LR-narrow.FrameComposition
open import proof.LR-narrow.RevealFrames using
  (revealFrame; reveal-frm)
open import proof.LR-narrow.SlotLifting using (transported-reveal-eq)
open import proof.LR-narrow.TargetSlot using (lifted-target-reveal)
open import proof.LR-narrow.PendingTarget

open ImpreciseComposition revealFrame using () renaming
  (imprecise-frame-computations-related to
    reveal-imprecise-composition;
   ImprecisePlugValues to RevealImprecisePlugValues)

pending-target-reveal-computations : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} (t : TargetSlot W)
    {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
    (p : TargetTransparent W t Aᴾ Aᴵ)
    {k : ℕ} {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
  → ComputationsRelated W
      (PendingTargetValueRelation t {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p) k Mᴵ Mᴾ
  → ComputationsRelated W
      (FutureValueRelation (target-transparent-derivation t
        {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p)) k
      (Mᴵ ↑ 〖 tslotXᴵ t , tslotRᴵ t ↑ Aᴵ 〗) Mᴾ
pending-target-reveal-computations {W = W} t {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p
    {k = k} {Mᴵ = Mᴵ} {Mᴾ = Mᴾ} related =
  reveal-imprecise-composition
    {R = PendingTargetValueRelation t
      {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p}
    {S = FutureValueRelation
      (target-transparent-derivation t
        {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p)}
    (reveal-frm 〖 tslotXᴵ t , tslotRᴵ t ↑ Aᴵ 〗) k Mᴵ Mᴾ
    plug-values related
  where
  plug-values : RevealImprecisePlugValues W
      (PendingTargetValueRelation t {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p)
      (FutureValueRelation (target-transparent-derivation t
        {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p)) k
      (reveal-frm 〖 tslotXᴵ t , tslotRᴵ t ↑ Aᴵ 〗)
  plug-values {W′ = W′} W≼W′ {χsᴵ = χsᴵ}
      storeᴵ storeᴾ termsᴵ termsᴾ {j = i} i≤k
      {Vᴵ = Uᴵ} {Vᴾ = Uᴾ} value-related =
    related-values-return
      {R = λ W″ W′≼W″ → FutureValueRelation
        (target-transparent-derivation t
          {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p)
        W″ (future-trans W≼W′ W′≼W″)}
      (subst Value (sym term-eq) (imprecise-value endpoints))
      (precise-value endpoints)
      (λ j j≤i → subst
        (λ M → ValueImprecisionᵏ j W′
          (liftCenterImprecision W≼W′
            (target-transparent-derivation t
              {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p)) M Uᴾ)
        (sym term-eq)
        (value-imprecision-downward-to j≤i value-related))
    where
    endpoints = ClosureProof.value-imprecision-endpoints value-related

    term-eq : Frame.plug revealFrame
        (Frame.transports revealFrame χsᴵ
          (reveal-frm 〖 tslotXᴵ t , tslotRᴵ t ↑ Aᴵ 〗)) Uᴵ
      ≡ Uᴵ ↑ 〖 tslotXᴵ (target-slot-future t W≼W′)
            , tslotRᴵ (target-slot-future t W≼W′)
            ↑ liftImpreciseTy W≼W′ Aᴵ 〗
    term-eq = transported-reveal-eq χsᴵ Mᴵ
      (tslotXᴵ t) (tslotRᴵ t) Aᴵ
      (trans (termsᴵ (Mᴵ ↑ 〖 tslotXᴵ t , tslotRᴵ t ↑ Aᴵ 〗))
        (trans (lifted-target-reveal t W≼W′ Mᴵ Aᴵ)
          (cong (λ M → M ↑ _) (sym (termsᴵ Mᴵ)))))
      Uᴵ
