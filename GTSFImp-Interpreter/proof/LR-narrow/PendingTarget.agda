module proof.LR-narrow.PendingTarget where

-- File Charter:
--   * Proves future stability of the scoped target-transparent reading.
--   * Establishes the key fresh-bind fact: a related precise representative
--     can be read against the fresh target name after a target-only bind.
--   * Keeps the relaxed reading outside ordinary type imprecision.

import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; refl; subst; sym; trans)

open import Types
open import CastTerms using (Term; _↑_)
open import Conversion using (replaceTy; 〖_,_↑_〗)
open import Consistency using (toRenameᵗ)
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.SlotSequence
open import LR-narrow.PendingTarget
open import LR-narrow.Computation using (IndexedValueRelation)
open import LR-narrow.LogicalRelation using (ValueImprecisionᵏ)
open import proof.ImprecisionConsistency using (toRenameᵗ-injective)
open import proof.LR-narrow.RevealLifting using
  (renameᵗ-replaceTy; shift-replace)
open import proof.LR-narrow.TargetSlot

liftCenterTy-replace : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (X : TyVar Δᶜ) (R B : Ty Δᶜ)
  → liftCenterTy W≼W′ (replaceTy X R B)
    ≡ replaceTy (liftCenterVariable W≼W′ X)
        (liftCenterTy W≼W′ R) (liftCenterTy W≼W′ B)
liftCenterTy-replace future-refl X R B = refl
liftCenterTy-replace (future-paired W≼W′ r) X R B =
  trans (cong ⇑ᵗ (liftCenterTy-replace W≼W′ X R B))
    (shift-replace (liftCenterVariable W≼W′ X)
      (liftCenterTy W≼W′ R) (liftCenterTy W≼W′ B))
liftCenterTy-replace (future-precise W≼W′ r) X R B =
  trans (cong ⇑ᵗ (liftCenterTy-replace W≼W′ X R B))
    (shift-replace (liftCenterVariable W≼W′ X)
      (liftCenterTy W≼W′ R) (liftCenterTy W≼W′ B))
liftCenterTy-replace (future-alias W≼W′) X R B =
  trans (cong ⇑ᵗ (liftCenterTy-replace W≼W′ X R B))
    (shift-replace (liftCenterVariable W≼W′ X)
      (liftCenterTy W≼W′ R) (liftCenterTy W≼W′ B))
liftCenterTy-replace (future-imprecise W≼W′) X R B =
  trans (cong ⇑ᵗ (liftCenterTy-replace W≼W′ X R B))
    (shift-replace (liftCenterVariable W≼W′ X)
      (liftCenterTy W≼W′ R) (liftCenterTy W≼W′ B))

target-rep-embedding-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (t : TargetSlot W) (W≼W′ : Future W W′)
  → embedImprecise (core W′) (tslotRᴵ (target-slot-future t W≼W′))
    ≡ liftCenterTy W≼W′ (embedImprecise (core W) (tslotRᴵ t))
target-rep-embedding-future {W′ = W′} t W≼W′ =
  trans (cong (embedImprecise (core W′))
      (target-slot-imprecise-rep-lift t W≼W′))
    (embedImprecise-lift W≼W′ (tslotRᴵ t))

target-normalize-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (t : TargetSlot W) (W≼W′ : Future W W′) (B : Ty Δᶜ)
  → targetNormalize W′ (target-slot-future t W≼W′)
      (liftCenterTy W≼W′ B)
    ≡ liftCenterTy W≼W′ (targetNormalize W t B)
target-normalize-future {W = W} {W′ = W′} t W≼W′ B =
  trans (cong (λ R → replaceTy
      (liftCenterVariable W≼W′ (tcenter t)) R (liftCenterTy W≼W′ B))
      (target-rep-embedding-future t W≼W′))
    (sym (liftCenterTy-replace W≼W′ (tcenter t)
      (embedImprecise (core W) (tslotRᴵ t)) B))

target-transparent-center-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′} {A B : Ty Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (t : TargetSlot W) (W≼W′ : Future W W′)
  → TargetTransparentCenter W t A B
  → TargetTransparentCenter W′ (target-slot-future t W≼W′)
      (liftCenterTy W≼W′ A) (liftCenterTy W≼W′ B)
target-transparent-center-future {A = A} {B = B} {W′ = W′}
    t W≼W′ p =
  subst (λ R → impEnv (core W′) I.⊢ liftCenterTy W≼W′ A ⊑ R)
    (sym (target-normalize-future t W≼W′ B))
    (liftCenterImprecision W≼W′ p)

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
  subst (λ L → impEnv (core W′) I.⊢ L ⊑ targetNormalize W′
      (target-slot-future t W≼W′)
      (embedImprecise (core W′) (liftImpreciseTy W≼W′ Aᴵ)))
    (sym (embedPrecise-lift W≼W′ Aᴾ))
    (subst (λ R → impEnv (core W′) I.⊢
        liftCenterTy W≼W′ (embedPrecise (core W) Aᴾ) ⊑ R)
      (sym (cong (targetNormalize W′ (target-slot-future t W≼W′))
        (embedImprecise-lift W≼W′ Aᴵ)))
      (target-transparent-center-future t W≼W′ p))

target-normalize-embedding : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) (t : TargetSlot W) (B : Ty Δᴵ)
  → targetNormalize W t (embedImprecise (core W) B)
    ≡ embedImprecise (core W)
        (replaceTy (tslotXᴵ t) (tslotRᴵ t) B)
target-normalize-embedding W t B =
  trans (cong (λ Z → replaceTy Z
      (embedImprecise (core W) (tslotRᴵ t))
      (embedImprecise (core W) B))
      (sym (targetImpreciseAligned (tatom t))))
    (sym (renameᵗ-replaceTy
      (toRenameᵗ (impreciseEmbedding (core W)))
      (toRenameᵗ-injective (impreciseEmbedding (core W)))
      (tslotXᴵ t) (tslotRᴵ t) B))

target-transparent-derivation : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} (t : TargetSlot W)
    {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
  → TargetTransparent W t Aᴾ Aᴵ
  → impEnv (core W) I.⊢ embedPrecise (core W) Aᴾ
      ⊑ embedImprecise (core W)
          (replaceTy (tslotXᴵ t) (tslotRᴵ t) Aᴵ)
target-transparent-derivation {W = W} t {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p =
  subst (λ R → impEnv (core W) I.⊢ embedPrecise (core W) Aᴾ ⊑ R)
    (target-normalize-embedding W t Aᴵ) p

PendingTargetValueRelation : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} (t : TargetSlot W)
    {Aᴾ : Ty Δᴾ} {Aᴵ : Ty Δᴵ}
  → TargetTransparent W t Aᴾ Aᴵ
  → IndexedValueRelation W
PendingTargetValueRelation t {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p W′ W≼W′ k Vᴵ Vᴾ =
  ValueImprecisionᵏ k W′
    (liftCenterImprecision W≼W′
      (target-transparent-derivation t {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} p))
    (Vᴵ ↑ 〖 tslotXᴵ (target-slot-future t W≼W′) ,
      tslotRᴵ (target-slot-future t W≼W′)
      ↑ liftImpreciseTy W≼W′ Aᴵ 〗)
    Vᴾ

fresh-target-variable-transparent : ∀ {Δᴾ Δᴵ Δᶜ}
    {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
  → Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ
  → TargetTransparent (impreciseBindWorld W Rᴵ)
      (fresh-target-slot W Rᴵ) Rᴾ (＇ Fin.zero)
fresh-target-variable-transparent {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} {W = W} r =
  subst (λ L → impEnv (core (impreciseBindWorld W Rᴵ)) I.⊢ L
      ⊑ targetNormalize (impreciseBindWorld W Rᴵ)
        (fresh-target-slot W Rᴵ)
        (embedImprecise (core (impreciseBindWorld W Rᴵ)) (＇ Fin.zero)))
    (sym (embedPrecise-imprecise-shift (core W) Rᴵ Rᴾ))
    (subst (λ R → impEnv (core (impreciseBindWorld W Rᴵ)) I.⊢
        ⇑ᵗ (embedPrecise (core W) Rᴾ) ⊑ R)
      (sym (embedImprecise-imprecise-shift (core W) Rᴵ Rᴵ))
      (liftCenterImprecision
        (future-imprecise {Aᴵ = Rᴵ} (future-refl {W = W})) r))
