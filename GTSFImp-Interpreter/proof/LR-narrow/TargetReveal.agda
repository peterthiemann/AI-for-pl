module proof.LR-narrow.TargetReveal where

-- File Charter:
--   * Defines the scoped target reading used during a target-only bind.
--   * Proves future stability of that reading.
--   * Turns a scoped related computation into an ordinary one by applying
--     the target slot's structural reveal.
--   * Does not change the ordinary type-imprecision relation.

open import Data.Nat using (ℕ; _≤_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; refl; subst; sym; trans)

open import Types
open import CastTerms using (Term; Value; _↑_)
open import Conversion using (replaceTy; 〖_,_↑_〗)
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.SlotSequence
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.Closure using (value-imprecision-downward-to)
import proof.LR-narrow.Closure as ClosureProof
open import proof.LR-narrow.ImmediateReturn using (related-values-return)
open import proof.LR-narrow.FramePhases using (Frame)
open import proof.LR-narrow.FrameComposition
open import proof.LR-narrow.RevealFrames using (revealFrame; reveal-frm)
open import proof.LR-narrow.SlotLifting using (transported-reveal-eq)
open import proof.LR-narrow.TargetSlot using
  (target-replace-imprecise-lift; lifted-target-reveal)

open ImpreciseComposition revealFrame using () renaming
  (imprecise-frame-computations-related to
    reveal-imprecise-composition;
   ImprecisePlugValues to RevealImprecisePlugValues)

------------------------------------------------------------------------
-- A scoped reading through one target-only slot
------------------------------------------------------------------------

TargetTransparent : ∀ {Δᴾ Δᴵ Δᶜ}
  → (W : World Δᴾ Δᴵ Δᶜ)
  → TargetSlot W → Ty Δᴾ → Ty Δᴵ → Set
TargetTransparent W t Aᴾ Aᴵ = impEnv (core W) I.⊢
  embedPrecise (core W) Aᴾ
    ⊑ embedImprecise (core W)
        (replaceTy (tslotXᴵ t) (tslotRᴵ t) Aᴵ)

target-transparent-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (t : TargetSlot W) (W≼W′ : Future W W′)
  → TargetTransparent W t Aᴾ Aᴵ
  → TargetTransparent W′ (target-slot-future t W≼W′)
      (liftPreciseTy W≼W′ Aᴾ) (liftImpreciseTy W≼W′ Aᴵ)
target-transparent-future {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} {W = W} {W′ = W′}
    t W≼W′ p =
  subst (λ L → impEnv (core W′) I.⊢ L ⊑ embedImprecise (core W′)
      (replaceTy (tslotXᴵ (target-slot-future t W≼W′))
        (tslotRᴵ (target-slot-future t W≼W′))
        (liftImpreciseTy W≼W′ Aᴵ)))
    (sym (embedPrecise-lift W≼W′ Aᴾ))
    (subst (λ R → impEnv (core W′) I.⊢
        liftCenterTy W≼W′ (embedPrecise (core W) Aᴾ) ⊑ R)
      (sym (trans (cong (embedImprecise (core W′))
          (target-replace-imprecise-lift t W≼W′ Aᴵ))
        (embedImprecise-lift W≼W′
          (replaceTy (tslotXᴵ t) (tslotRᴵ t) Aᴵ))))
      (liftCenterImprecision W≼W′ p))

target-transparent-derivation : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} (t : TargetSlot W)
    {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
  → TargetTransparent W t Aᴾ Aᴵ
  → impEnv (core W) I.⊢ embedPrecise (core W) Aᴾ
      ⊑ embedImprecise (core W)
          (replaceTy (tslotXᴵ t) (tslotRᴵ t) Aᴵ)
target-transparent-derivation t p = p

------------------------------------------------------------------------
-- Values awaiting the target reveal
------------------------------------------------------------------------

PendingTargetValueRelation : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} (t : TargetSlot W)
    {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
  → TargetTransparent W t Aᴾ Aᴵ
  → IndexedValueRelation W
PendingTargetValueRelation t {Aᴵ = Aᴵ} p W′ W≼W′ k Vᴵ Vᴾ =
  ValueImprecisionᵏ k W′ (liftCenterImprecision W≼W′ p)
    (Vᴵ ↑ 〖 tslotXᴵ (target-slot-future t W≼W′) ,
      tslotRᴵ (target-slot-future t W≼W′)
      ↑ liftImpreciseTy W≼W′ Aᴵ 〗)
    Vᴾ

------------------------------------------------------------------------
-- Materializing the target reveal
------------------------------------------------------------------------

pending-target-reveal-computations : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} (t : TargetSlot W)
    {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
    (p : TargetTransparent W t Aᴾ Aᴵ)
    {k : ℕ} {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
  → ComputationsRelated W
      (PendingTargetValueRelation t {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p)
      k Mᴵ Mᴾ
  → ComputationsRelated W
      (FutureValueRelation (target-transparent-derivation t
        {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p)) k
      (Mᴵ ↑ 〖 tslotXᴵ t , tslotRᴵ t ↑ Aᴵ 〗) Mᴾ
pending-target-reveal-computations {W = W} t {Aᴾ = Aᴾ}
    {Aᴵ = Aᴵ} p {k = k} {Mᴵ = Mᴵ} {Mᴾ = Mᴾ} related =
  reveal-imprecise-composition
    {R = PendingTargetValueRelation t {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p}
    {S = FutureValueRelation (target-transparent-derivation t
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
        (target-transparent-derivation t {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p)
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
      ≡ Uᴵ ↑ 〖 tslotXᴵ (target-slot-future t W≼W′) ,
            tslotRᴵ (target-slot-future t W≼W′)
            ↑ liftImpreciseTy W≼W′ Aᴵ 〗
    term-eq = transported-reveal-eq χsᴵ Mᴵ
      (tslotXᴵ t) (tslotRᴵ t) Aᴵ
      (trans (termsᴵ (Mᴵ ↑ 〖 tslotXᴵ t , tslotRᴵ t ↑ Aᴵ 〗))
        (trans (lifted-target-reveal t W≼W′ Mᴵ Aᴵ)
          (cong (λ M → M ↑ _) (sym (termsᴵ Mᴵ)))))
      Uᴵ
