module proof.LR-narrow.TargetReveal where

-- File Charter:
--   * Defines the scoped target reading used during a target-only bind.
--   * Proves future stability of that reading.
--   * Turns a scoped related computation into an ordinary one by applying
--     the target slot's structural reveal.
--   * Does not change the ordinary type-imprecision relation.

open import Data.Nat using (ℕ; suc; _≤_)
open import Data.Product using (_,_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; cong₂; refl; subst; sym; trans)

open import Types
open import CastTerms using (Term; _↑_; _↓_)
open import Conversion using (replaceTy; 〖_,_↑_〗; seal)
open import Reduction using (pure-step; conceal-reveal)
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.SlotSequence
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.Closure using (value-imprecision-downward-to)
import proof.LR-narrow.Closure as ClosureProof
open import proof.LR-narrow.ReplaceImprecision using
  (replace-zero-open; open-shifted-body)
open import proof.LR-narrow.ImmediateReturn using (related-values-return)
open import proof.LR-narrow.FramePhases using (Frame)
open import proof.LR-narrow.FrameComposition
open import proof.LR-narrow.RevealFrames using (revealFrame; reveal-frm)
open import proof.LR-narrow.SlotLifting using (transported-reveal-eq)
open import proof.LR-narrow.TargetSlot using
  (target-replace-imprecise-lift; lifted-target-reveal)
open import proof.LR-narrow.TypeApplication using (lift-precise-open)
open import proof.LR-narrow.UniversalReveal using
  (liftImpreciseBody-replace)
open import proof.LR-narrow.RevealLifting using (slot-future)
open import proof.LR-narrow.SlotLifting using
  (slot-imprecise-variable-lift; slot-imprecise-rep-lift)
open import proof.LR-narrow.AliasAvoid using (AliasAvoid★ᵖ)
open import proof.LR-narrow.ImpreciseReveal using
  (replace-right-body-⊑; embI-replace-body-eq)
open import proof.LR-narrow.CastComposition using
  (computations-related-future-compose)
open import proof.LR-narrow.KeepStepExpansion using
  (related-imprecise-keep-step-expand)
open import proof.LR-narrow.RevealSteps using
  (unseal-step-question; unseal-value-none)

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

------------------------------------------------------------------------
-- Fresh target readings created by a one-sided bind
------------------------------------------------------------------------

fresh-target-variable-transparent : ∀ {Δᴾ Δᴵ Δᶜ}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
  → Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ
  → TargetTransparent (impreciseBindWorld W Rᴵ)
      (fresh-target-slot W Rᴵ) Rᴾ (＇ Fin.zero)
fresh-target-variable-transparent {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} {W = W} r =
  subst (λ L → impEnv (core (impreciseBindWorld W Rᴵ)) I.⊢ L
      ⊑ embedImprecise (core (impreciseBindWorld W Rᴵ)) (⇑ᵗ Rᴵ))
    (sym (embedPrecise-imprecise-shift (core W) Rᴵ Rᴾ))
    (subst (λ R → impEnv (core (impreciseBindWorld W Rᴵ)) I.⊢
        ⇑ᵗ (embedPrecise (core W) Rᴾ) ⊑ R)
      (sym (embedImprecise-imprecise-shift (core W) Rᴵ Rᴵ))
      (liftCenterImprecision
        (future-imprecise {Aᴵ = Rᴵ} (future-refl {W = W})) r))

fresh-target-open-transparent : ∀ {Δᴾ Δᴵ Δᶜ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty (suc Δᴵ)}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
  → BodyImprecisionᵇ W Bᴾ Bᴵ
  → Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ
  → TargetTransparent (impreciseBindWorld W Rᴵ)
      (fresh-target-slot W Rᴵ) (Bᴾ [ Rᴾ ]ᵗ) Bᴵ
fresh-target-open-transparent {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
    {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} {W = W} body r =
  subst (λ L → impEnv (core W′) I.⊢ L
      ⊑ embedImprecise (core W′)
          (replaceTy Fin.zero (⇑ᵗ Rᴵ) Bᴵ))
    (sym (embedPrecise-lift step (Bᴾ [ Rᴾ ]ᵗ)))
    (subst (λ R → impEnv (core W′) I.⊢
        liftCenterTy step (embedPrecise (core W) (Bᴾ [ Rᴾ ]ᵗ)) ⊑ R)
      (sym right-eq)
      (liftCenterImprecision step
        (openRelatedBodyImprecision {W = W} (bodyPᵇ body) r)))
  where
  W′ = impreciseBindWorld W Rᴵ
  step = future-imprecise {Aᴵ = Rᴵ} (future-refl {W = W})

  right-eq : embedImprecise (core W′)
      (replaceTy Fin.zero (⇑ᵗ Rᴵ) Bᴵ)
      ≡ liftCenterTy step
          (embedImprecise (core W) (Bᴵ [ Rᴵ ]ᵗ))
  right-eq =
    trans (cong (embedImprecise (core W′))
        (replace-zero-open Rᴵ Bᴵ))
      (embedImprecise-lift step (Bᴵ [ Rᴵ ]ᵗ))

fresh-target-lifted-open-transparent : ∀ {Δᴾ Δᴵ Δᶜ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty (suc Δᴵ)}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
  → BodyImprecisionᵇ W Bᴾ Bᴵ
  → Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ
  → TargetTransparent (impreciseBindWorld W Rᴵ)
      (fresh-target-slot W Rᴵ)
      (liftPreciseBody
          (future-imprecise {Aᴵ = Rᴵ} (future-refl {W = W})) Bᴾ
        [ liftPreciseTy
            (future-imprecise {Aᴵ = Rᴵ} (future-refl {W = W})) Rᴾ ]ᵗ)
      (liftImpreciseBody
          (future-imprecise {Aᴵ = Rᴵ} (future-refl {W = W})) Bᴵ
        [ ＇ Fin.zero ]ᵗ)
fresh-target-lifted-open-transparent {Bᴾ = Bᴾ} {Bᴵ = Bᴵ}
    {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} {W = W} body r =
  subst (λ Aᴵ → TargetTransparent W′ slot precise-open Aᴵ)
    (sym (open-shifted-body Bᴵ))
    (subst (λ Aᴾ → TargetTransparent W′ slot Aᴾ Bᴵ)
      (lift-precise-open step Bᴾ Rᴾ)
      (fresh-target-open-transparent body r))
  where
  W′ = impreciseBindWorld W Rᴵ
  step = future-imprecise {Aᴵ = Rᴵ} (future-refl {W = W})
  slot = fresh-target-slot W Rᴵ
  precise-open =
    liftPreciseBody step Bᴾ [ liftPreciseTy step Rᴾ ]ᵗ

fresh-target-lifted-replaced-open-transparent : ∀ {Δᴾ Δᴵ Δᶜ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty (suc Δᴵ)}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    (s : PairedSlot W)
    (body : BodyImprecisionᵇ W Bᴾ Bᴵ)
  → AliasAvoid★ᵖ (Fin.suc (center s)) (bodyPᵇ body)
  → Fin.suc (center s) ∉ᵗ embedPreciseBody (core W) Bᴾ
  → (r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ)
  → let
      step = future-imprecise {Aᴵ = Rᴵ} (future-refl {W = W})
      s′ = slot-future s step
    in TargetTransparent (impreciseBindWorld W Rᴵ)
        (fresh-target-slot W Rᴵ)
        (liftPreciseBody step Bᴾ [ liftPreciseTy step Rᴾ ]ᵗ)
        (replaceTy (Fin.suc (slotXᴵ s′)) (⇑ᵗ (slotRᴵ s′))
            (liftImpreciseBody step Bᴵ)
          [ ＇ Fin.zero ]ᵗ)
fresh-target-lifted-replaced-open-transparent {Bᴾ = Bᴾ}
    {Bᴵ = Bᴵ} {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} {W = W}
    s body avoid no-occur r =
  subst (TargetTransparent W′ fresh precise-open)
    lifted-replaced-open-eq
    (fresh-target-lifted-open-transparent replaced-body r)
  where
  step = future-imprecise {Aᴵ = Rᴵ} (future-refl {W = W})
  W′ = impreciseBindWorld W Rᴵ
  fresh = fresh-target-slot W Rᴵ
  s′ = slot-future s step
  precise-open =
    liftPreciseBody step Bᴾ [ liftPreciseTy step Rᴾ ]ᵗ

  replaced-body : BodyImprecisionᵇ W Bᴾ
      (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) Bᴵ)
  replaced-body = body-imprecisionᵇ
    (subst (λ R → I.extᵐ (impEnv (core W)) I.⊢
        embedPreciseBody (core W) Bᴾ ⊑ R)
      (sym (embI-replace-body-eq W s Bᴵ))
      (replace-right-body-⊑ W s (bodyPᵇ body) avoid no-occur))

  lifted-replaced-body-eq : liftImpreciseBody step
      (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) Bᴵ)
      ≡ replaceTy (Fin.suc (slotXᴵ s′)) (⇑ᵗ (slotRᴵ s′))
          (liftImpreciseBody step Bᴵ)
  lifted-replaced-body-eq = trans
    (liftImpreciseBody-replace step (slotXᴵ s) (slotRᴵ s) Bᴵ)
    (cong₂
      (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R)
        (liftImpreciseBody step Bᴵ))
      (sym (slot-imprecise-variable-lift s step))
      (sym (slot-imprecise-rep-lift s step)))

  lifted-replaced-open-eq :
      liftImpreciseBody step
          (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) Bᴵ)
        [ ＇ Fin.zero ]ᵗ
      ≡ replaceTy (Fin.suc (slotXᴵ s′)) (⇑ᵗ (slotRᴵ s′))
          (liftImpreciseBody step Bᴵ)
        [ ＇ Fin.zero ]ᵗ
  lifted-replaced-open-eq = cong (_[ ＇ Fin.zero ]ᵗ)
    lifted-replaced-body-eq

------------------------------------------------------------------------
-- Values awaiting the target reveal
------------------------------------------------------------------------

PendingTargetValueRelation : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} (t : TargetSlot W)
    {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
  → TargetTransparent W t Aᴾ Aᴵ
  → IndexedValueRelation W
PendingTargetValueRelation t {Aᴵ = Aᴵ} p W′ W≼W′ k Vᴵ Vᴾ =
  ComputationsRelated W′
    (λ W″ W′≼W″ → FutureValueRelation p W″
      (future-trans W≼W′ W′≼W″)) k
    (Vᴵ ↑ 〖 tslotXᴵ (target-slot-future t W≼W′) ,
      tslotRᴵ (target-slot-future t W≼W′)
      ↑ liftImpreciseTy W≼W′ Aᴵ 〗)
    Vᴾ

-- A pending reveal need not be a value: at the fresh variable it unseals.
-- The producer records the resulting computation, including that step.

fresh-target-sealed-values : ∀ {Δᴾ Δᴵ Δᶜ}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    (r : Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ)
    {k : ℕ} {Uᴵ : Term (suc Δᴵ)} {Vᴾ : Term Δᴾ}
  → ValueImprecision (impreciseBindWorld W Rᴵ)
      (fresh-target-variable-transparent {W = W} r) k Uᴵ Vᴾ
  → PendingTargetValueRelation (fresh-target-slot W Rᴵ)
      (fresh-target-variable-transparent {W = W} r)
      (impreciseBindWorld W Rᴵ) future-refl k
      (Uᴵ ↓ seal Fin.zero (⇑ᵗ Rᴵ)) Vᴾ
fresh-target-sealed-values {Rᴵ = Rᴵ} {W = W} r related
    with unseal-step-question
      {Σ = impreciseStore (core (impreciseBindWorld W Rᴵ))}
      Fin.zero (⇑ᵗ Rᴵ)
      (imprecise-value (ClosureProof.value-imprecision-endpoints related))
... | vUᴵ , step-eq =
  computations-related-future-compose future-refl
    (fresh-target-variable-transparent {W = W} r)
    (related-imprecise-keep-step-expand (λ ())
      (unseal-value-none Fin.zero (⇑ᵗ Rᴵ) vUᴵ)
      (pure-step (conceal-reveal vUᴵ)) step-eq
      (related-values-return vUᴵ
        (precise-value (ClosureProof.value-imprecision-endpoints related))
        (λ j j≤k → value-imprecision-downward-to j≤k related)))

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
  → ComputationsRelated W (FutureValueRelation p) k
      (Mᴵ ↑ 〖 tslotXᴵ t , tslotRᴵ t ↑ Aᴵ 〗) Mᴾ
pending-target-reveal-computations {W = W} t {Aᴾ = Aᴾ}
    {Aᴵ = Aᴵ} p {k = k} {Mᴵ = Mᴵ} {Mᴾ = Mᴾ} related =
  reveal-imprecise-composition
    {R = PendingTargetValueRelation t {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p}
    {S = FutureValueRelation p}
    (reveal-frm 〖 tslotXᴵ t , tslotRᴵ t ↑ Aᴵ 〗) k Mᴵ Mᴾ
    plug-values related
  where
  plug-values : RevealImprecisePlugValues W
      (PendingTargetValueRelation t {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p)
      (FutureValueRelation p) k
      (reveal-frm 〖 tslotXᴵ t , tslotRᴵ t ↑ Aᴵ 〗)
  plug-values {W′ = W′} W≼W′ {χsᴵ = χsᴵ}
      storeᴵ storeᴾ termsᴵ termsᴾ {j = i} i≤k
      {Vᴵ = Uᴵ} {Vᴾ = Uᴾ} value-related =
    subst
      (λ M → ComputationsRelated W′
        (λ W″ W′≼W″ → FutureValueRelation p W″
          (future-trans W≼W′ W′≼W″)) i M Uᴾ)
      (sym term-eq) value-related
    where
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
