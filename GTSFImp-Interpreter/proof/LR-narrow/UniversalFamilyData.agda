module proof.LR-narrow.UniversalFamilyData where

-- File Charter:
--   * Proves structural operations on two-sided universal producer data.
--   * Supplies future-world closure for the ordinary and pending chains.
--   * Depends on the general LR closure lemmas, but not on reveal obligations.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Unit.Polymorphic.Base using (tt)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; cong₂; refl; sym; trans)
  renaming (subst to subst≡)

open import Types
open import CastTerms
open import Conversion using (replaceTy; 〖_,_↑_〗; makeConceal)
import Imprecision as I
open import proof.ImprecisionComposition using (alias-rebuild)
open import LR-narrow.World
open import LR-narrow.SlotSequence
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.UniversalFamily
import proof.LR-narrow.Closure as Closure
open import proof.LR-narrow.AliasAvoid using
  (AliasAvoidᵖ; AliasAvoid★ᵖ; alias-avoid★-any)
open import proof.LR-narrow.RevealLifting using
  (slot-future; alias-avoid★-lift-body)
open import proof.LR-narrow.SlotLifting using
  (slot-imprecise-variable-lift; slot-imprecise-rep-lift;
   lifted-reveal-imprecise; lifted-conceal-imprecise)
open import proof.LR-narrow.ImpreciseReveal using
  (lift-center-body-∉ᵗ)
open import proof.LR-narrow.UniversalReveal using
  (liftImpreciseBody-replace)
open import proof.LR-narrow.PendingUniversal using
  (pending-target-imprecise-peel-bind-expand)
open import proof.LR-narrow.RevealStatements using (OuterBelow)
open import proof.LR-narrow.RevealStructural using
  (statements-all; reveal-universal-head; conceal-universal-head)

------------------------------------------------------------------------
-- Completed structural induction below any step index
------------------------------------------------------------------------

outer-below-all : ∀ (k : ℕ) → OuterBelow k
outer-below-all k j j<k n = statements-all j n

------------------------------------------------------------------------
-- Fresh precise instantiations as aliases
------------------------------------------------------------------------

fresh-alias-local-imprecision : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) {Rᴾ : Ty Δᴾ} {Rᴵ : Ty Δᴵ}
  → Rᴾ ⊑ᵂ⟨ core W ⟩ Rᴵ
  → ＇ Fin.zero ⊑ᵂ⟨ core (aliasBindWorld W Rᴾ) ⟩ Rᴵ
fresh-alias-local-imprecision W {Rᴾ = Rᴾ} {Rᴵ = Rᴵ} r =
  alias-rebuild
    (isVar? (acenter fresh) (embedImprecise (core bound) Rᴵ))
    (amode-eq fresh) premise
  where
  bound = aliasBindWorld W Rᴾ
  fresh = fresh-alias-slot W Rᴾ

  premise : impEnv (core bound) I.⊢ arepresentative fresh ⊑
      embedImprecise (core bound) Rᴵ
  premise = subst≡
    (λ L → impEnv (core bound) I.⊢ L ⊑ embedImprecise (core bound) Rᴵ)
    (aliasRep-eq (aatom fresh))
    (alias-local-imprecision {rep = Rᴾ} r)

------------------------------------------------------------------------
-- Future lifting of imprecise-only peels
------------------------------------------------------------------------

reveal-imprecise-peel-futureᵇ : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (s : PairedSlot W) {B : Ty (suc Δᴾ)} {C : Ty (suc Δᴵ)}
    (no-occur : Fin.suc (center s) ∉ᵗ embedPreciseBody (core W) B)
    (source : BodyImprecisionᵇ W B C)
    (target : BodyImprecisionᵇ W B
      (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) C))
    (avoid : (j : BodyImprecisionᵇ W B C)
      → AliasAvoid★ᵖ (Fin.suc (center s)) (bodyPᵇ j))
    (W≼W′ : Future W W′)
  → ImprecisePeelᵇ W′ (liftPreciseBody W≼W′ B)
      (liftImpreciseBody W≼W′ C)
      (replaceTy (Fin.suc (slotXᴵ (slot-future s W≼W′)))
        (⇑ᵗ (slotRᴵ (slot-future s W≼W′)))
        (liftImpreciseBody W≼W′ C))
reveal-imprecise-peel-futureᵇ {W′ = W′} s {B = B} {C = C}
    no-occur source target avoid W≼W′ =
  reveal-imprecise-peelᵇ s′ C′ no-occur′ target′ avoid′
  where
  s′ = slot-future s W≼W′
  B′ = liftPreciseBody W≼W′ B
  C′ = liftImpreciseBody W≼W′ C

  target-eq : liftImpreciseBody W≼W′
      (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) C)
      ≡ replaceTy (Fin.suc (slotXᴵ s′)) (⇑ᵗ (slotRᴵ s′)) C′
  target-eq = trans
    (liftImpreciseBody-replace W≼W′ (slotXᴵ s) (slotRᴵ s) C)
    (cong₂ (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R) C′)
      (sym (slot-imprecise-variable-lift s W≼W′))
      (sym (slot-imprecise-rep-lift s W≼W′)))

  no-occur′ : Fin.suc (center s′) ∉ᵗ embedPreciseBody (core W′) B′
  no-occur′ = subst≡ (Fin.suc (center s′) ∉ᵗ_)
    (sym (embedPreciseBody-lift W≼W′ B))
    (lift-center-body-∉ᵗ W≼W′ no-occur)

  target′ : BodyImprecisionᵇ W′ B′
      (replaceTy (Fin.suc (slotXᴵ s′)) (⇑ᵗ (slotRᴵ s′)) C′)
  target′ = body-imprecisionᵇ-subst-imp target-eq
    (body-imprecisionᵇ-future W≼W′ target)

  avoid′ : (j : BodyImprecisionᵇ W′ B′ C′)
    → AliasAvoid★ᵖ (Fin.suc (center s′)) (bodyPᵇ j)
  avoid′ j = alias-avoid★-any
    (liftCenterBodyImprecision W≼W′ (bodyPᵇ source)) (bodyPᵇ j)
    (sym (embedPreciseBody-lift W≼W′ B))
    (sym (embedImpreciseBody-lift W≼W′ C))
    (alias-avoid★-lift-body W≼W′ (center s)
      (bodyPᵇ source) (avoid source))

conceal-imprecise-peel-futureᵇ : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (s : PairedSlot W) {B : Ty (suc Δᴾ)} {C : Ty (suc Δᴵ)}
    (no-occur : Fin.suc (center s) ∉ᵗ embedPreciseBody (core W) B)
    (target : BodyImprecisionᵇ W B C)
    (avoid : (j : BodyImprecisionᵇ W B C)
      → AliasAvoid★ᵖ (Fin.suc (center s)) (bodyPᵇ j))
    (W≼W′ : Future W W′)
  → ImprecisePeelᵇ W′ (liftPreciseBody W≼W′ B)
      (replaceTy (Fin.suc (slotXᴵ (slot-future s W≼W′)))
        (⇑ᵗ (slotRᴵ (slot-future s W≼W′)))
        (liftImpreciseBody W≼W′ C))
      (liftImpreciseBody W≼W′ C)
conceal-imprecise-peel-futureᵇ {W′ = W′} s {B = B} {C = C}
    no-occur target avoid W≼W′ =
  conceal-imprecise-peelᵇ s′ C′ no-occur′ target′ avoid′
  where
  s′ = slot-future s W≼W′
  B′ = liftPreciseBody W≼W′ B
  C′ = liftImpreciseBody W≼W′ C

  no-occur′ : Fin.suc (center s′) ∉ᵗ embedPreciseBody (core W′) B′
  no-occur′ = subst≡ (Fin.suc (center s′) ∉ᵗ_)
    (sym (embedPreciseBody-lift W≼W′ B))
    (lift-center-body-∉ᵗ W≼W′ no-occur)

  target′ : BodyImprecisionᵇ W′ B′ C′
  target′ = body-imprecisionᵇ-future W≼W′ target

  avoid′ : (j : BodyImprecisionᵇ W′ B′ C′)
    → AliasAvoid★ᵖ (Fin.suc (center s′)) (bodyPᵇ j)
  avoid′ j = alias-avoid★-any
    (liftCenterBodyImprecision W≼W′ (bodyPᵇ target)) (bodyPᵇ j)
    (sym (embedPreciseBody-lift W≼W′ B))
    (sym (embedImpreciseBody-lift W≼W′ C))
    (alias-avoid★-lift-body W≼W′ (center s)
      (bodyPᵇ target) (avoid target))

------------------------------------------------------------------------
-- Paired wrapper chain extensions
------------------------------------------------------------------------

reveal-paired-chainᵇ : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty (suc Δᴵ)}
    (source : BodyImprecisionᵇ W Bᴾ Bᴵ)
  → AliasAvoidᵖ (Fin.suc (center s)) (bodyPᵇ source)
  → (target : BodyImprecisionᵇ W
      (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) Bᴾ)
      (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) Bᴵ))
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → UniversalDataᵇ W (bodyPᵇ source) Bᴾ Bᴵ k Vᴵ Vᴾ
  → UniversalsRelated W (bodyPᵇ target)
      (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) Bᴾ)
      (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) Bᴵ) k
      (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ `∀ Bᴵ 〗)
      (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ Bᴾ 〗)
reveal-paired-chainᵇ W s source avoid target {k = zero} dat = tt
reveal-paired-chainᵇ W s source avoid target {k = suc k} dat =
  reveal-universal-head W s (bodyPᵇ source) avoid refl refl
    (outer-below-all (suc k)) dat ,
  reveal-paired-chainᵇ W s source avoid target
    (universal-dataᵇ-downward dat)

conceal-paired-chainᵇ : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty (suc Δᴵ)}
    (target : BodyImprecisionᵇ W Bᴾ Bᴵ)
    (source : BodyImprecisionᵇ W
      (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) Bᴾ)
      (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) Bᴵ))
  → AliasAvoidᵖ (Fin.suc (center s)) (bodyPᵇ target)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → UniversalDataᵇ W (bodyPᵇ source)
      (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) Bᴾ)
      (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) Bᴵ)
      k Vᴵ Vᴾ
  → UniversalsRelated W (bodyPᵇ target) Bᴾ Bᴵ k
      (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (`∀ Bᴵ))
      (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ Bᴾ))
conceal-paired-chainᵇ W s target source avoid {k = zero} dat = tt
conceal-paired-chainᵇ W s target source avoid {k = suc k} dat =
  conceal-universal-head W s (bodyPᵇ target) (bodyPᵇ source) avoid
    refl refl refl refl (outer-below-all (suc k)) dat ,
  conceal-paired-chainᵇ W s target source avoid
    (universal-dataᵇ-downward dat)

------------------------------------------------------------------------
-- Imprecise-only wrapper chain extensions
------------------------------------------------------------------------

reveal-imprecise-chainᵇ : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
    {B : Ty (suc Δᴾ)} {C : Ty (suc Δᴵ)}
    (no-occur : Fin.suc (center s) ∉ᵗ embedPreciseBody (core W) B)
    (source : BodyImprecisionᵇ W B C)
    (target : BodyImprecisionᵇ W B
      (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) C))
    (avoid : (j : BodyImprecisionᵇ W B C)
      → AliasAvoid★ᵖ (Fin.suc (center s)) (bodyPᵇ j))
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → UniversalDataᵇ W (bodyPᵇ source) B C k Vᴵ Vᴾ
  → UniversalsRelated W (bodyPᵇ target) B
      (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) C) k
      (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ `∀ C 〗) Vᴾ
reveal-imprecise-chainᵇ W s no-occur source target avoid
    {k = zero} dat = tt
reveal-imprecise-chainᵇ W s {B = B} {C = C} no-occur source target
    avoid {k = suc k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} dat =
  head ,
  reveal-imprecise-chainᵇ W s no-occur source target avoid
    (universal-dataᵇ-downward dat)
  where
  head : ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) (Rᴾ : Ty Δᴾ′) (Rᴵ : Ty Δᴵ′)
      (r : Rᴾ ⊑ᵂ⟨ core W′ ⟩ Rᴵ)
      (q : liftPreciseBody W≼W′ B [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩
          liftImpreciseBody W≼W′
            (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) C)
          [ Rᴵ ]ᵗ)
    → ComputationsRelated W′ (FutureValueRelation q) (suc k)
        (liftImpreciseTerm W≼W′
            (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ `∀ C 〗)
          ⦂∀ liftImpreciseBody W≼W′
            (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) C)
          [ Rᴵ ])
        (liftPreciseTerm W≼W′ Vᴾ
          ⦂∀ liftPreciseBody W≼W′ B [ Rᴾ ])
  head W′ W≼W′ Rᴾ Rᴵ r q =
    Closure.computations-related-reindex opened q
      refl (sym imprecise-result-eq) (sym termᴵ-eq) refl
      (pending-target-imprecise-peel-bind-expand peel′ r
        (data-pendingᵇ dat W≼W′) valueᴵ′)
    where
    s′ = slot-future s W≼W′
    B′ = liftPreciseBody W≼W′ B
    C′ = liftImpreciseBody W≼W′ C
    D′ = replaceTy (Fin.suc (slotXᴵ s′)) (⇑ᵗ (slotRᴵ s′)) C′

    peel′ : ImprecisePeelᵇ W′ B′ C′ D′
    peel′ = reveal-imprecise-peel-futureᵇ s no-occur source target
      avoid W≼W′

    body-eq : liftImpreciseBody W≼W′
        (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) C) ≡ D′
    body-eq = trans
      (liftImpreciseBody-replace W≼W′ (slotXᴵ s) (slotRᴵ s) C)
      (cong₂ (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R) C′)
        (sym (slot-imprecise-variable-lift s W≼W′))
        (sym (slot-imprecise-rep-lift s W≼W′)))

    opened = openRelatedBodyImprecision {W = W′}
      (bodyPᵇ (imprecise-peel-targetᵇ peel′)) r

    imprecise-result-eq : embedImprecise (core W′)
        (liftImpreciseBody W≼W′
          (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) C)
          [ Rᴵ ]ᵗ)
      ≡ embedImprecise (core W′) (D′ [ Rᴵ ]ᵗ)
    imprecise-result-eq = cong (embedImprecise (core W′))
      (cong (_[ Rᴵ ]ᵗ) body-eq)

    termᴵ-eq :
        liftImpreciseTerm W≼W′
            (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ `∀ C 〗)
          ⦂∀ liftImpreciseBody W≼W′
            (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) C)
          [ Rᴵ ]
      ≡ imprecise-peel-termᴵᵇ peel′ (liftImpreciseTerm W≼W′ Vᴵ)
          ⦂∀ D′ [ Rᴵ ]
    termᴵ-eq
        rewrite lifted-reveal-imprecise s W≼W′ Vᴵ (`∀ C)
              | liftImpreciseTy-universal W≼W′ C
              | body-eq = refl

    valueᴵ′ : Value (liftImpreciseTerm W≼W′ Vᴵ)
    valueᴵ′ = Closure.imprecise-value-future W≼W′
      (imprecise-value (data-endpointsᵇ dat))

conceal-imprecise-chainᵇ : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
    {B : Ty (suc Δᴾ)} {C : Ty (suc Δᴵ)}
    (no-occur : Fin.suc (center s) ∉ᵗ embedPreciseBody (core W) B)
    (target : BodyImprecisionᵇ W B C)
    (source : BodyImprecisionᵇ W B
      (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) C))
    (avoid : (j : BodyImprecisionᵇ W B C)
      → AliasAvoid★ᵖ (Fin.suc (center s)) (bodyPᵇ j))
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → UniversalDataᵇ W (bodyPᵇ source) B
      (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) C)
      k Vᴵ Vᴾ
  → UniversalsRelated W (bodyPᵇ target) B C k
      (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (`∀ C)) Vᴾ
conceal-imprecise-chainᵇ W s no-occur target source avoid
    {k = zero} dat = tt
conceal-imprecise-chainᵇ W s {B = B} {C = C} no-occur target source
    avoid {k = suc k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} dat =
  head ,
  conceal-imprecise-chainᵇ W s no-occur target source avoid
    (universal-dataᵇ-downward dat)
  where
  head : ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) (Rᴾ : Ty Δᴾ′) (Rᴵ : Ty Δᴵ′)
      (r : Rᴾ ⊑ᵂ⟨ core W′ ⟩ Rᴵ)
      (q : liftPreciseBody W≼W′ B [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseBody W≼W′ C [ Rᴵ ]ᵗ)
    → ComputationsRelated W′ (FutureValueRelation q) (suc k)
        (liftImpreciseTerm W≼W′
            (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (`∀ C))
          ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
        (liftPreciseTerm W≼W′ Vᴾ
          ⦂∀ liftPreciseBody W≼W′ B [ Rᴾ ])
  head W′ W≼W′ Rᴾ Rᴵ r q =
    Closure.computations-related-reindex opened q
      refl refl (sym termᴵ-eq) refl
      (pending-target-imprecise-peel-bind-expand peel′ r
        pending′ valueᴵ′)
    where
    s′ = slot-future s W≼W′
    B′ = liftPreciseBody W≼W′ B
    C′ = liftImpreciseBody W≼W′ C
    D′ = replaceTy (Fin.suc (slotXᴵ s′)) (⇑ᵗ (slotRᴵ s′)) C′

    peel′ : ImprecisePeelᵇ W′ B′ D′ C′
    peel′ = conceal-imprecise-peel-futureᵇ s no-occur target avoid
      W≼W′

    body-eq : liftImpreciseBody W≼W′
        (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) C) ≡ D′
    body-eq = trans
      (liftImpreciseBody-replace W≼W′ (slotXᴵ s) (slotRᴵ s) C)
      (cong₂ (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R) C′)
        (sym (slot-imprecise-variable-lift s W≼W′))
        (sym (slot-imprecise-rep-lift s W≼W′)))

    pending′ : PendingTargetUniversalsRelated W′ B′ D′ (suc k)
        (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
    pending′ = Closure.pending-target-universals-related-body-transport
      refl body-eq (data-pendingᵇ dat W≼W′)

    opened = openRelatedBodyImprecision {W = W′}
      (bodyPᵇ (imprecise-peel-targetᵇ peel′)) r

    termᴵ-eq :
        liftImpreciseTerm W≼W′
            (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (`∀ C))
          ⦂∀ C′ [ Rᴵ ]
      ≡ imprecise-peel-termᴵᵇ peel′ (liftImpreciseTerm W≼W′ Vᴵ)
          ⦂∀ C′ [ Rᴵ ]
    termᴵ-eq
        rewrite lifted-conceal-imprecise s W≼W′ Vᴵ (`∀ C)
              | liftImpreciseTy-universal W≼W′ C = refl

    valueᴵ′ : Value (liftImpreciseTerm W≼W′ Vᴵ)
    valueᴵ′ = Closure.imprecise-value-future W≼W′
      (imprecise-value (data-endpointsᵇ dat))

universal-dataᵇ-future : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Aᴾ Aᴵ : Ty (suc Δᶜ)}
    {p : I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty (suc Δᴵ)} {k : ℕ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    (W≼W′ : Future W W′)
  → UniversalDataᵇ W p Bᴾ Bᴵ k Vᴵ Vᴾ
  → UniversalDataᵇ W′ (liftCenterBodyImprecision W≼W′ p)
      (liftPreciseBody W≼W′ Bᴾ) (liftImpreciseBody W≼W′ Bᴵ) k
      (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)
universal-dataᵇ-future {W′ = W′} {Aᴾ = Aᴾ} {Aᴵ = Aᴵ} {p = p}
    {Bᴾ = Bᴾ} {Bᴵ = Bᴵ} {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    W≼W′ dat = universal-dataᵇ
  structural-endpoints
  (Closure.universals-related-future W≼W′ (data-chainᵇ dat))
  pending
  where
  lifted-endpoints =
    Closure.typed-endpoints-future W≼W′ (data-endpointsᵇ dat)

  structural-endpoints = typed-endpoints
    (impreciseType lifted-endpoints) (preciseType lifted-endpoints)
    (trans (impreciseEmbedded lifted-endpoints)
      (liftCenterTy-universal W≼W′ Aᴵ))
    (trans (preciseEmbedded lifted-endpoints)
      (liftCenterTy-universal W≼W′ Aᴾ))
    (imprecise-value lifted-endpoints) (precise-value lifted-endpoints)
    (imprecise-typed lifted-endpoints) (precise-typed lifted-endpoints)

  pending : ∀ {Δᴾ″ Δᴵ″ Δᶜ″} {K : World Δᴾ″ Δᴵ″ Δᶜ″}
      (W′≼K : Future W′ K)
    → PendingTargetUniversalsRelated K
        (liftPreciseBody W′≼K (liftPreciseBody W≼W′ Bᴾ))
        (liftImpreciseBody W′≼K (liftImpreciseBody W≼W′ Bᴵ)) k
        (liftImpreciseTerm W′≼K (liftImpreciseTerm W≼W′ Vᴵ))
        (liftPreciseTerm W′≼K (liftPreciseTerm W≼W′ Vᴾ))
  pending W′≼K =
    Closure.pending-target-universals-related-transport
      (liftImpreciseTerm-trans W≼W′ W′≼K Vᴵ)
      (liftPreciseTerm-trans W≼W′ W′≼K Vᴾ)
      (Closure.pending-target-universals-related-body-transport
        (liftPreciseBody-trans W≼W′ W′≼K Bᴾ)
        (liftImpreciseBody-trans W≼W′ W′≼K Bᴵ)
        (data-pendingᵇ dat (future-trans W≼W′ W′≼K)))
