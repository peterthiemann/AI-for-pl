module proof.LR-narrow.PendingTarget where

-- File Charter:
--   * Proves future stability of the scoped target-transparent reading.
--   * Establishes the key fresh-bind fact: a related precise representative
--     can be read against the fresh target name after a target-only bind.
--   * Keeps the relaxed reading outside ordinary type imprecision.

import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; cong₂; refl; subst; sym; trans)

open import Types
open import Conversion using (replaceTy)
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.SlotSequence
open import LR-narrow.PendingTarget
open import LR-narrow.LogicalRelation
open import proof.LR-narrow.ReplaceImprecision using
  (replace-zero-open; open-shifted-body)
open import proof.LR-narrow.TargetSlot using
  (target-replace-imprecise-lift)
open import proof.LR-narrow.TypeApplication using (lift-precise-open)
open import proof.LR-narrow.UniversalReveal using
  (liftImpreciseBody-replace)
open import proof.LR-narrow.RevealLifting using (slot-future)
open import proof.LR-narrow.SlotLifting using
  (slot-imprecise-variable-lift; slot-imprecise-rep-lift)
open import proof.LR-narrow.AliasAvoid using (AliasAvoid★ᵖ)
open import proof.LR-narrow.ImpreciseReveal using
  (replace-right-body-⊑; embI-replace-body-eq)

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
target-transparent-derivation {W = W} t {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p =
  p

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
  slot = fresh-target-slot W Rᴵ

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
  → Fin.suc (center s) ∉ᵗ
      embedPreciseBody (core W) Bᴾ
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
