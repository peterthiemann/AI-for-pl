module proof.LR-narrow.UniversalFamilyData where

-- File Charter:
--   * Proves structural operations on two-sided universal producer data.
--   * Supplies future-world closure for the ordinary and pending chains.
--   * Depends on the general LR closure lemmas, but not on reveal obligations.

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; proj₁)
open import Data.Unit.Polymorphic.Base using (tt)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; cong₂; refl; sym; trans)
  renaming (subst to subst≡)

open import Types
open import CastTerms
open import Conversion using
  (`∀↑_; `∀↓_; replaceTy; 〖_,_↑_〗; makeConceal)
open import Reduction
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
  (slot-precise-variable-lift; slot-precise-rep-lift;
   slot-imprecise-variable-lift; slot-imprecise-rep-lift;
   lifted-reveal-precise; lifted-reveal-imprecise;
   lifted-conceal-precise; lifted-conceal-imprecise)
open import proof.LR-narrow.ImpreciseReveal using
  (lift-center-body-∉ᵗ)
open import proof.LR-narrow.UniversalReveal using
  (reveal-type-app-step-question; conceal-type-app-step-question;
   post-bind-weaken;
   liftPreciseBody-replace; liftImpreciseBody-replace)
open import proof.LR-narrow.BindStepExpansion using
  (alias-step; related-alias-bind-step-expand)
open import proof.LR-narrow.ReplaceImprecision using
  (replace-left-⊑; replace-left-alias-eq-⊑; replace-zero-open;
   open-shifted-body)
open import proof.LR-narrow.PreciseReveal using
  (sizeᵗ; lift-∉ᵗ; precise-revealed-computations;
   precise-concealed-computations)
open import proof.LR-narrow.StarNoOccurrence using (replaceTy-absent)
open import proof.LR-narrow.DynamicReveal using
  (dyn-slot-future; dyn-slot-precise-variable-lift;
   dyn-slot-precise-rep-lift; dyn-lifted-reveal-precise;
   dyn-lifted-conceal-precise; dyn-embed-replace; dyn-embed-∉;
   dyn-revealed-computations; dyn-concealed-computations; ∉-all-inv)
open import proof.LR-narrow.AliasReveal using
  (alias-slot-future; alias-slot-precise-variable-lift;
   alias-slot-precise-rep-lift; alias-lifted-reveal-precise;
   alias-lifted-conceal-precise; alias-embed-replace; alias-embed-∉;
   alias-revealed-computations; alias-concealed-computations)
open import proof.LR-narrow.PendingUniversal using
  (pending-target-imprecise-peel-bind-expand)
open import proof.LR-narrow.RevealStatements using (Below; OuterBelow)
open import proof.LR-narrow.RevealStructural using
  (statements-all; reveal-universal-head; conceal-universal-head)

------------------------------------------------------------------------
-- Completed structural induction below any step index
------------------------------------------------------------------------

outer-below-all : ∀ (k : ℕ) → OuterBelow k
outer-below-all k j j<k n = statements-all j n

below-allᵇ : ∀ (k n : ℕ) → Below k n
below-allᵇ k n j m lex = statements-all j m

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
-- Precise-only dynamic wrapper chain extension
------------------------------------------------------------------------

reveal-dynamic-innerᵇ : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) (d : DynamicSlot W)
    {B : Ty (suc Δᴾ)} {C : Ty (suc Δᴵ)}
    (source : BodyImprecisionᵇ W B C)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → UniversalDataᵇ W (bodyPᵇ source) B C (suc k) Vᴵ Vᴾ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) (Rᴾ : Ty Δᴾ′) (Rᴵ : Ty Δᴵ′)
      (r : Rᴾ ⊑ᵂ⟨ core W′ ⟩ Rᴵ)
      (q : liftPreciseBody W≼W′
            (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B)
            [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseBody W≼W′ C [ Rᴵ ]ᵗ)
  → ComputationsRelated (aliasBindWorld W′ Rᴾ)
      (FutureValueRelation
        (liftCenterImprecision (alias-step W′ Rᴾ) q)) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ
        ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
      (((⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
          ⦂∀ renameᵗ (extᵗ Fin.suc) (liftPreciseBody W≼W′ B)
            [ ＇ Fin.zero ])
        ↑ 〖 Fin.suc (dslotXᴾ (dyn-slot-future d W≼W′)) ,
            ⇑ᵗ (dslotRᴾ (dyn-slot-future d W≼W′))
            ↑ liftPreciseBody W≼W′ B 〗)
        ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ
          ↑ replaceTy
              (Fin.suc (dslotXᴾ (dyn-slot-future d W≼W′)))
              (⇑ᵗ (dslotRᴾ (dyn-slot-future d W≼W′)))
              (liftPreciseBody W≼W′ B) 〗)
reveal-dynamic-innerᵇ W d {B = B} {C = C} source {k = k}
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} dat W′ W≼W′ Rᴾ Rᴵ r q = final
  where
  step = alias-step W′ Rᴾ
  Wb = aliasBindWorld W′ Rᴾ
  W≼Wb : Future W Wb
  W≼Wb = future-alias W≼W′

  d′ = dyn-slot-future d W≼W′
  d₁ = dyn-slot-future d′ step
  a₂ = fresh-alias-slot W′ Rᴾ
  Xᴾ′ = dslotXᴾ d′
  Rᴾ′ = dslotRᴾ d′
  B′ = liftPreciseBody W≼W′ B
  C′ = liftImpreciseBody W≼W′ C
  D′ = replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′

  source′ : BodyImprecisionᵇ Wb
      (renameᵗ (extᵗ Fin.suc) B′) C′
  source′ = body-imprecisionᵇ-future W≼Wb source

  r₀ : ＇ Fin.zero ⊑ᵂ⟨ core Wb ⟩ Rᴵ
  r₀ = fresh-alias-local-imprecision W′ r

  opened : renameᵗ (extᵗ Fin.suc) B′ [ ＇ Fin.zero ]ᵗ
      ⊑ᵂ⟨ core Wb ⟩ C′ [ Rᴵ ]ᵗ
  opened = openRelatedBodyImprecision {W = Wb} (bodyPᵇ source′) r₀

  core-related : ComputationsRelated Wb
      (FutureValueRelation opened) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ ⦂∀ C′ [ Rᴵ ])
      (⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
        ⦂∀ renameᵗ (extᵗ Fin.suc) B′ [ ＇ Fin.zero ])
  core-related = proj₁ (data-chainᵇ dat)
    Wb W≼Wb (＇ Fin.zero) Rᴵ r₀ opened

  open-P : renameᵗ (extᵗ Fin.suc) B′ [ ＇ Fin.zero ]ᵗ ≡ B′
  open-P = open-shifted-body B′

  t₀ : impEnv (core Wb) I.⊢ embedPrecise (core Wb) B′ ⊑
      embedImprecise (core Wb) (C′ [ Rᴵ ]ᵗ)
  t₀ = subst≡
    (λ L → impEnv (core Wb) I.⊢ L ⊑
      embedImprecise (core Wb) (C′ [ Rᴵ ]ᵗ))
    (cong (embedPrecise (core Wb)) open-P) opened

  reindexed : ComputationsRelated Wb (FutureValueRelation t₀) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ ⦂∀ C′ [ Rᴵ ])
      (⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
        ⦂∀ renameᵗ (extᵗ Fin.suc) B′ [ ＇ Fin.zero ])
  reindexed = Closure.computations-related-reindex opened t₀
    (cong (embedPrecise (core Wb)) open-P) refl refl refl core-related

  avoidᴵ : dcenter d₁ ∉ᵗ embedImprecise (core Wb) (C′ [ Rᴵ ]ᵗ)
  avoidᴵ = dyn-embed-∉ d₁ (C′ [ Rᴵ ]ᵗ)

  t₁ : impEnv (core Wb) I.⊢
      replaceTy (dcenter d₁)
        (embedPrecise (core Wb) (dslotRᴾ d₁))
        (embedPrecise (core Wb) B′)
      ⊑ embedImprecise (core Wb) (C′ [ Rᴵ ]ᵗ)
  t₁ = replace-left-⊑ (dcenter d₁) (dmode-eq d₁)
    (dynamicRep-related (datom d₁)) avoidᴵ t₀

  target₁-P : embedPrecise (core Wb)
      (replaceTy (dslotXᴾ d₁) (dslotRᴾ d₁) B′)
      ≡ replaceTy (dcenter d₁)
          (embedPrecise (core Wb) (dslotRᴾ d₁))
          (embedPrecise (core Wb) B′)
  target₁-P = dyn-embed-replace d₁ B′

  Nᴵ = liftImpreciseTerm W≼W′ Vᴵ
  Nᴾ = ⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
    ⦂∀ renameᵗ (extᵗ Fin.suc) B′ [ ＇ Fin.zero ]

  revealed₁ : ComputationsRelated Wb (FutureValueRelation t₁) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᴾ ↑ 〖 dslotXᴾ d₁ , dslotRᴾ d₁ ↑ B′ 〗)
  revealed₁ = dyn-revealed-computations (sizeᵗ B′) (suc k)
    (sizeᵗ B′) (below-allᵇ (suc k) (sizeᵗ B′)) Wb d₁ t₀
    ≤-refl refl t₁ target₁-P reindexed

  wrap-eq-P : (Nᴾ ↑ 〖 dslotXᴾ d₁ , dslotRᴾ d₁ ↑ B′ 〗)
      ≡ (Nᴾ ↑ 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B′ 〗)
  wrap-eq-P = cong₂ (λ X R → Nᴾ ↑ 〖 X , R ↑ B′ 〗)
    (dyn-slot-precise-variable-lift d′ step)
    (dyn-slot-precise-rep-lift d′ step)

  revealed₁′ : ComputationsRelated Wb (FutureValueRelation t₁) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᴾ ↑ 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B′ 〗)
  revealed₁′ = Closure.computations-related-reindex t₁ t₁
    refl refl refl wrap-eq-P revealed₁

  t₁′ : impEnv (core Wb) I.⊢
      replaceTy (dcenter d₁)
        (embedPrecise (core Wb) (dslotRᴾ d₁))
        (embedPrecise (core Wb) B′)
      ⊑ ⇑ᵗ (embedImprecise (core W′) (C′ [ Rᴵ ]ᵗ))
  t₁′ = subst≡
    (λ R → impEnv (core Wb) I.⊢
      replaceTy (dcenter d₁)
        (embedPrecise (core Wb) (dslotRᴾ d₁))
        (embedPrecise (core Wb) B′) ⊑ R)
    (embedImprecise-alias-shift (core W′) Rᴾ (C′ [ Rᴵ ]ᵗ)) t₁

  revealed₁″ : ComputationsRelated Wb (FutureValueRelation t₁′) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᴾ ↑ 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B′ 〗)
  revealed₁″ = Closure.computations-related-reindex t₁ t₁′
    refl
    (embedImprecise-alias-shift (core W′) Rᴾ (C′ [ Rᴵ ]ᵗ))
    refl refl revealed₁′

  source₂-P : embedPrecise (core Wb) D′
      ≡ replaceTy (dcenter d₁)
          (embedPrecise (core Wb) (dslotRᴾ d₁))
          (embedPrecise (core Wb) B′)
  source₂-P = trans
    (cong₂ (λ X R → embedPrecise (core Wb) (replaceTy X R B′))
      (sym (dyn-slot-precise-variable-lift d′ step))
      (sym (dyn-slot-precise-rep-lift d′ step)))
    target₁-P

  body-eq-P : liftPreciseBody W≼W′
      (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B)
      ≡ D′
  body-eq-P = trans
    (liftPreciseBody-replace W≼W′ (dslotXᴾ d) (dslotRᴾ d) B)
    (cong₂ (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R) B′)
      (sym (dyn-slot-precise-variable-lift d W≼W′))
      (sym (dyn-slot-precise-rep-lift d W≼W′)))

  target₂-P : embedPrecise (core Wb)
      (replaceTy Fin.zero (⇑ᵗ Rᴾ) D′)
      ≡ ⇑ᵗ (embedPrecise (core W′)
          (liftPreciseBody W≼W′
            (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B)
            [ Rᴾ ]ᵗ))
  target₂-P = trans
    (cong (embedPrecise (core Wb)) (replace-zero-open Rᴾ D′))
    (trans
      (embedPrecise-alias-shift (core W′) Rᴾ (D′ [ Rᴾ ]ᵗ))
      (cong (λ T → ⇑ᵗ (embedPrecise (core W′) (T [ Rᴾ ]ᵗ)))
        (sym body-eq-P)))

  final : ComputationsRelated Wb
      (FutureValueRelation (liftCenterImprecision step q)) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      ((Nᴾ ↑ 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B′ 〗)
        ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ ↑ D′ 〗)
  final = alias-revealed-computations (sizeᵗ D′) (suc k)
    (sizeᵗ D′) (below-allᵇ (suc k) (sizeᵗ D′)) Wb a₂ t₁′
    ≤-refl source₂-P (liftCenterImprecision step q) target₂-P
    revealed₁″

reveal-dynamic-chainᵇ : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (d : DynamicSlot W)
    {B : Ty (suc Δᴾ)} {C : Ty (suc Δᴵ)}
    (source : BodyImprecisionᵇ W B C)
    (target : BodyImprecisionᵇ W
      (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B) C)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → UniversalDataᵇ W (bodyPᵇ source) B C k Vᴵ Vᴾ
  → UniversalsRelated W (bodyPᵇ target)
      (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B) C k
      Vᴵ (Vᴾ ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ `∀ B 〗)
reveal-dynamic-chainᵇ W d source target {k = zero} dat = tt
reveal-dynamic-chainᵇ W d {B = B} {C = C} source target
    {k = suc k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} dat =
  head ,
  reveal-dynamic-chainᵇ W d source target
    (universal-dataᵇ-downward dat)
  where
  head : ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) (Rᴾ : Ty Δᴾ′) (Rᴵ : Ty Δᴵ′)
      (r : Rᴾ ⊑ᵂ⟨ core W′ ⟩ Rᴵ)
      (q : liftPreciseBody W≼W′
            (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B)
            [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseBody W≼W′ C [ Rᴵ ]ᵗ)
    → ComputationsRelated W′ (FutureValueRelation q) (suc k)
        (liftImpreciseTerm W≼W′ Vᴵ
          ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
        (liftPreciseTerm W≼W′
            (Vᴾ ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ `∀ B 〗)
          ⦂∀ liftPreciseBody W≼W′
            (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B)
            [ Rᴾ ])
  head W′ W≼W′ Rᴾ Rᴵ r q =
    Closure.computations-related-reindex q q refl refl refl
      (sym precise-redex-eq) weakened
    where
    step = alias-step W′ Rᴾ
    d′ = dyn-slot-future d W≼W′
    Xᴾ′ = dslotXᴾ d′
    Rᴾ′ = dslotRᴾ d′
    B′ = liftPreciseBody W≼W′ B
    Vᴾ′ = liftPreciseTerm W≼W′ Vᴾ
    cᴾ = 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B′ 〗

    precise-body-eq : liftPreciseBody W≼W′
        (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B)
        ≡ replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′
    precise-body-eq = trans
      (liftPreciseBody-replace W≼W′ (dslotXᴾ d) (dslotRᴾ d) B)
      (cong₂ (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R) B′)
        (sym (dyn-slot-precise-variable-lift d W≼W′))
        (sym (dyn-slot-precise-rep-lift d W≼W′)))

    precise-redex-eq :
        liftPreciseTerm W≼W′
            (Vᴾ ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ `∀ B 〗)
          ⦂∀ liftPreciseBody W≼W′
            (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B)
            [ Rᴾ ]
      ≡ (Vᴾ′ ↑ `∀↑ cᴾ)
          ⦂∀ replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′ [ Rᴾ ]
    precise-redex-eq
        rewrite dyn-lifted-reveal-precise d W≼W′ Vᴾ (`∀ B)
              | liftPreciseTy-universal W≼W′ B
              | precise-body-eq = refl

    stepped : ComputationsRelated W′
        (PostBindValueRelation step q) (suc k)
        (liftImpreciseTerm W≼W′ Vᴵ
          ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
        ((Vᴾ′ ↑ `∀↑ cᴾ)
          ⦂∀ replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′ [ Rᴾ ])
    stepped
        with reveal-type-app-step-question
               {Σ = preciseStore (core W′)} {A = Rᴾ} cᴾ vVᴾ′
      where
      endpoints = data-endpointsᵇ dat
      vVᴾ′ = Closure.precise-value-future W≼W′
        (precise-value endpoints)
    stepped | vVᴾ″ , step-eqᴾ =
      related-alias-bind-step-expand (λ ()) refl
        (β-reveal-∀ vVᴾ″) step-eqᴾ
        (reveal-dynamic-innerᵇ W d source dat W′ W≼W′
          Rᴾ Rᴵ r q)

    weakened : ComputationsRelated W′ (FutureValueRelation q) (suc k)
        (liftImpreciseTerm W≼W′ Vᴵ
          ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
        ((Vᴾ′ ↑ `∀↑ cᴾ)
          ⦂∀ replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′ [ Rᴾ ])
    weakened = post-bind-weaken step q stepped

conceal-dynamic-innerᵇ : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) (d : DynamicSlot W)
    {B : Ty (suc Δᴾ)} {C : Ty (suc Δᴵ)}
    (target : BodyImprecisionᵇ W B C)
    (source : BodyImprecisionᵇ W
      (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B) C)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → UniversalDataᵇ W (bodyPᵇ source)
      (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B) C
      (suc k) Vᴵ Vᴾ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) (Rᴾ : Ty Δᴾ′) (Rᴵ : Ty Δᴵ′)
      (r : Rᴾ ⊑ᵂ⟨ core W′ ⟩ Rᴵ)
      (q : liftPreciseBody W≼W′ B [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseBody W≼W′ C [ Rᴵ ]ᵗ)
  → ComputationsRelated (aliasBindWorld W′ Rᴾ)
      (FutureValueRelation
        (liftCenterImprecision (alias-step W′ Rᴾ) q)) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ
        ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
      (((⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
          ⦂∀ renameᵗ (extᵗ Fin.suc)
            (replaceTy
              (Fin.suc (dslotXᴾ (dyn-slot-future d W≼W′)))
              (⇑ᵗ (dslotRᴾ (dyn-slot-future d W≼W′)))
              (liftPreciseBody W≼W′ B))
            [ ＇ Fin.zero ])
        ↓ makeConceal
            (Fin.suc (dslotXᴾ (dyn-slot-future d W≼W′)))
            (⇑ᵗ (dslotRᴾ (dyn-slot-future d W≼W′)))
            (liftPreciseBody W≼W′ B))
        ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ ↑ liftPreciseBody W≼W′ B 〗)
conceal-dynamic-innerᵇ W d {B = B} {C = C} target source
    {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} dat W′ W≼W′ Rᴾ Rᴵ r q = final
  where
  step = alias-step W′ Rᴾ
  Wb = aliasBindWorld W′ Rᴾ
  W≼Wb : Future W Wb
  W≼Wb = future-alias W≼W′

  d′ = dyn-slot-future d W≼W′
  d₁ = dyn-slot-future d′ step
  a₂ = fresh-alias-slot W′ Rᴾ
  Xᴾ′ = dslotXᴾ d′
  Rᴾ′ = dslotRᴾ d′
  B′ = liftPreciseBody W≼W′ B
  C′ = liftImpreciseBody W≼W′ C
  D′ = replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′

  body-eq-P : liftPreciseBody W≼W′
      (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B)
      ≡ D′
  body-eq-P = trans
    (liftPreciseBody-replace W≼W′ (dslotXᴾ d) (dslotRᴾ d) B)
    (cong₂ (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R) B′)
      (sym (dyn-slot-precise-variable-lift d W≼W′))
      (sym (dyn-slot-precise-rep-lift d W≼W′)))

  source′ : BodyImprecisionᵇ Wb
      (renameᵗ (extᵗ Fin.suc) D′) C′
  source′ = body-imprecisionᵇ-subst
    (cong (renameᵗ (extᵗ Fin.suc)) body-eq-P)
    (body-imprecisionᵇ-future W≼Wb source)

  target′ : BodyImprecisionᵇ Wb
      (renameᵗ (extᵗ Fin.suc) B′) C′
  target′ = body-imprecisionᵇ-future W≼Wb target

  r₀ : ＇ Fin.zero ⊑ᵂ⟨ core Wb ⟩ Rᴵ
  r₀ = fresh-alias-local-imprecision W′ r

  opened-source : renameᵗ (extᵗ Fin.suc) D′ [ ＇ Fin.zero ]ᵗ
      ⊑ᵂ⟨ core Wb ⟩ C′ [ Rᴵ ]ᵗ
  opened-source = openRelatedBodyImprecision {W = Wb}
    (bodyPᵇ source′) r₀

  opened-target : renameᵗ (extᵗ Fin.suc) B′ [ ＇ Fin.zero ]ᵗ
      ⊑ᵂ⟨ core Wb ⟩ C′ [ Rᴵ ]ᵗ
  opened-target = openRelatedBodyImprecision {W = Wb}
    (bodyPᵇ target′) r₀

  L′ = liftPreciseBody W≼W′
    (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B)

  source₀ : BodyImprecisionᵇ Wb
      (renameᵗ (extᵗ Fin.suc) L′) C′
  source₀ = body-imprecisionᵇ-future W≼Wb source

  opened-source₀ : renameᵗ (extᵗ Fin.suc) L′ [ ＇ Fin.zero ]ᵗ
      ⊑ᵂ⟨ core Wb ⟩ C′ [ Rᴵ ]ᵗ
  opened-source₀ = openRelatedBodyImprecision {W = Wb}
    (bodyPᵇ source₀) r₀

  opened-source-eq : renameᵗ (extᵗ Fin.suc) L′ [ ＇ Fin.zero ]ᵗ
      ≡ renameᵗ (extᵗ Fin.suc) D′ [ ＇ Fin.zero ]ᵗ
  opened-source-eq = cong
    (λ T → renameᵗ (extᵗ Fin.suc) T [ ＇ Fin.zero ]ᵗ) body-eq-P

  Nᵇ = ⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)

  core-related₀ : ComputationsRelated Wb
      (FutureValueRelation opened-source₀) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᵇ ⦂∀ renameᵗ (extᵗ Fin.suc) L′ [ ＇ Fin.zero ])
  core-related₀ = proj₁ (data-chainᵇ dat)
    Wb W≼Wb (＇ Fin.zero) Rᴵ r₀ opened-source₀

  core-related : ComputationsRelated Wb
      (FutureValueRelation opened-source) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᵇ ⦂∀ renameᵗ (extᵗ Fin.suc) D′ [ ＇ Fin.zero ])
  core-related = Closure.computations-related-reindex
    opened-source₀ opened-source
    (cong (embedPrecise (core Wb)) opened-source-eq) refl refl
    (cong (λ T → Nᵇ ⦂∀ renameᵗ (extᵗ Fin.suc) T [ ＇ Fin.zero ])
      body-eq-P)
    core-related₀

  open-source : renameᵗ (extᵗ Fin.suc) D′ [ ＇ Fin.zero ]ᵗ ≡ D′
  open-source = open-shifted-body D′

  open-target : renameᵗ (extᵗ Fin.suc) B′ [ ＇ Fin.zero ]ᵗ ≡ B′
  open-target = open-shifted-body B′

  t₀q : impEnv (core Wb) I.⊢ embedPrecise (core Wb) D′ ⊑
      embedImprecise (core Wb) (C′ [ Rᴵ ]ᵗ)
  t₀q = subst≡
    (λ L → impEnv (core Wb) I.⊢ L ⊑
      embedImprecise (core Wb) (C′ [ Rᴵ ]ᵗ))
    (cong (embedPrecise (core Wb)) open-source) opened-source

  t₀ : impEnv (core Wb) I.⊢ embedPrecise (core Wb) B′ ⊑
      embedImprecise (core Wb) (C′ [ Rᴵ ]ᵗ)
  t₀ = subst≡
    (λ L → impEnv (core Wb) I.⊢ L ⊑
      embedImprecise (core Wb) (C′ [ Rᴵ ]ᵗ))
    (cong (embedPrecise (core Wb)) open-target) opened-target

  Nᴵ = liftImpreciseTerm W≼W′ Vᴵ
  Nᴾ = ⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
    ⦂∀ renameᵗ (extᵗ Fin.suc) D′ [ ＇ Fin.zero ]

  reindexed : ComputationsRelated Wb (FutureValueRelation t₀q) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ]) Nᴾ
  reindexed = Closure.computations-related-reindex opened-source t₀q
    (cong (embedPrecise (core Wb)) open-source) refl refl refl
    core-related

  source₁-P : embedPrecise (core Wb)
      (replaceTy (dslotXᴾ d₁) (dslotRᴾ d₁) B′)
      ≡ embedPrecise (core Wb) D′
  source₁-P = cong₂
    (λ X R → embedPrecise (core Wb) (replaceTy X R B′))
    (dyn-slot-precise-variable-lift d′ step)
    (dyn-slot-precise-rep-lift d′ step)

  concealed₁ : ComputationsRelated Wb (FutureValueRelation t₀) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᴾ ↓ makeConceal (dslotXᴾ d₁) (dslotRᴾ d₁) B′)
  concealed₁ = dyn-concealed-computations (sizeᵗ B′) (suc k)
    (sizeᵗ B′) (below-allᵇ (suc k) (sizeᵗ B′)) Wb d₁ t₀
    ≤-refl refl t₀q source₁-P reindexed

  wrap-eq-P :
      (Nᴾ ↓ makeConceal (dslotXᴾ d₁) (dslotRᴾ d₁) B′)
      ≡ (Nᴾ ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′)
  wrap-eq-P = cong₂ (λ X R → Nᴾ ↓ makeConceal X R B′)
    (dyn-slot-precise-variable-lift d′ step)
    (dyn-slot-precise-rep-lift d′ step)

  concealed₁′ : ComputationsRelated Wb (FutureValueRelation t₀) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᴾ ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′)
  concealed₁′ = Closure.computations-related-reindex t₀ t₀
    refl refl refl wrap-eq-P concealed₁

  t₀′ : impEnv (core Wb) I.⊢ embedPrecise (core Wb) B′ ⊑
      ⇑ᵗ (embedImprecise (core W′) (C′ [ Rᴵ ]ᵗ))
  t₀′ = subst≡
    (λ R → impEnv (core Wb) I.⊢ embedPrecise (core Wb) B′ ⊑ R)
    (embedImprecise-alias-shift (core W′) Rᴾ (C′ [ Rᴵ ]ᵗ)) t₀

  concealed₁″ : ComputationsRelated Wb (FutureValueRelation t₀′) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᴾ ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′)
  concealed₁″ = Closure.computations-related-reindex t₀ t₀′
    refl
    (embedImprecise-alias-shift (core W′) Rᴾ (C′ [ Rᴵ ]ᵗ))
    refl refl concealed₁′

  target₂-P : embedPrecise (core Wb)
      (replaceTy Fin.zero (⇑ᵗ Rᴾ) B′)
      ≡ ⇑ᵗ (embedPrecise (core W′) (B′ [ Rᴾ ]ᵗ))
  target₂-P = trans
    (cong (embedPrecise (core Wb)) (replace-zero-open Rᴾ B′))
    (embedPrecise-alias-shift (core W′) Rᴾ (B′ [ Rᴾ ]ᵗ))

  final : ComputationsRelated Wb
      (FutureValueRelation (liftCenterImprecision step q)) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      ((Nᴾ ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′)
        ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ ↑ B′ 〗)
  final = alias-revealed-computations (sizeᵗ B′) (suc k)
    (sizeᵗ B′) (below-allᵇ (suc k) (sizeᵗ B′)) Wb a₂ t₀′
    ≤-refl refl (liftCenterImprecision step q) target₂-P concealed₁″

conceal-dynamic-chainᵇ : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (d : DynamicSlot W)
    {B : Ty (suc Δᴾ)} {C : Ty (suc Δᴵ)}
    (target : BodyImprecisionᵇ W B C)
    (source : BodyImprecisionᵇ W
      (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B) C)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → UniversalDataᵇ W (bodyPᵇ source)
      (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B) C
      k Vᴵ Vᴾ
  → UniversalsRelated W (bodyPᵇ target) B C k Vᴵ
      (Vᴾ ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) (`∀ B))
conceal-dynamic-chainᵇ W d target source {k = zero} dat = tt
conceal-dynamic-chainᵇ W d {B = B} {C = C} target source
    {k = suc k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} dat =
  head ,
  conceal-dynamic-chainᵇ W d target source
    (universal-dataᵇ-downward dat)
  where
  head : ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) (Rᴾ : Ty Δᴾ′) (Rᴵ : Ty Δᴵ′)
      (r : Rᴾ ⊑ᵂ⟨ core W′ ⟩ Rᴵ)
      (q : liftPreciseBody W≼W′ B [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseBody W≼W′ C [ Rᴵ ]ᵗ)
    → ComputationsRelated W′ (FutureValueRelation q) (suc k)
        (liftImpreciseTerm W≼W′ Vᴵ
          ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
        (liftPreciseTerm W≼W′
            (Vᴾ ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) (`∀ B))
          ⦂∀ liftPreciseBody W≼W′ B [ Rᴾ ])
  head W′ W≼W′ Rᴾ Rᴵ r q =
    Closure.computations-related-reindex q q refl refl refl
      (sym precise-redex-eq) weakened
    where
    step = alias-step W′ Rᴾ
    d′ = dyn-slot-future d W≼W′
    Xᴾ′ = dslotXᴾ d′
    Rᴾ′ = dslotRᴾ d′
    B′ = liftPreciseBody W≼W′ B
    Vᴾ′ = liftPreciseTerm W≼W′ Vᴾ
    dᴾ = makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′

    precise-redex-eq :
        liftPreciseTerm W≼W′
            (Vᴾ ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) (`∀ B))
          ⦂∀ liftPreciseBody W≼W′ B [ Rᴾ ]
      ≡ (Vᴾ′ ↓ `∀↓ dᴾ) ⦂∀ B′ [ Rᴾ ]
    precise-redex-eq
        rewrite dyn-lifted-conceal-precise d W≼W′ Vᴾ (`∀ B)
              | liftPreciseTy-universal W≼W′ B = refl

    stepped : ComputationsRelated W′
        (PostBindValueRelation step q) (suc k)
        (liftImpreciseTerm W≼W′ Vᴵ
          ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
        ((Vᴾ′ ↓ `∀↓ dᴾ) ⦂∀ B′ [ Rᴾ ])
    stepped
        with conceal-type-app-step-question
               {Σ = preciseStore (core W′)} {A = Rᴾ} dᴾ vVᴾ′
      where
      endpoints = data-endpointsᵇ dat
      vVᴾ′ = Closure.precise-value-future W≼W′
        (precise-value endpoints)
    stepped | vVᴾ″ , step-eqᴾ =
      related-alias-bind-step-expand (λ ()) refl
        (β-conceal-∀ vVᴾ″) step-eqᴾ
        (conceal-dynamic-innerᵇ W d target source dat W′ W≼W′
          Rᴾ Rᴵ r q)

    weakened : ComputationsRelated W′ (FutureValueRelation q) (suc k)
        (liftImpreciseTerm W≼W′ Vᴵ
          ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
        ((Vᴾ′ ↓ `∀↓ dᴾ) ⦂∀ B′ [ Rᴾ ])
    weakened = post-bind-weaken step q stepped

------------------------------------------------------------------------
-- Precise-only alias wrapper chain extension
------------------------------------------------------------------------

reveal-alias-innerᵇ : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) (a : AliasSlot W)
    {B : Ty (suc Δᴾ)} {C : Ty (suc Δᴵ)}
    (source : BodyImprecisionᵇ W B C)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → UniversalDataᵇ W (bodyPᵇ source) B C (suc k) Vᴵ Vᴾ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) (Rᴾ : Ty Δᴾ′) (Rᴵ : Ty Δᴵ′)
      (r : Rᴾ ⊑ᵂ⟨ core W′ ⟩ Rᴵ)
      (q : liftPreciseBody W≼W′
            (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B)
            [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseBody W≼W′ C [ Rᴵ ]ᵗ)
  → ComputationsRelated (aliasBindWorld W′ Rᴾ)
      (FutureValueRelation
        (liftCenterImprecision (alias-step W′ Rᴾ) q)) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ
        ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
      (((⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
          ⦂∀ renameᵗ (extᵗ Fin.suc) (liftPreciseBody W≼W′ B)
            [ ＇ Fin.zero ])
        ↑ 〖 Fin.suc (aslotXᴾ (alias-slot-future a W≼W′)) ,
            ⇑ᵗ (aslotRᴾ (alias-slot-future a W≼W′))
            ↑ liftPreciseBody W≼W′ B 〗)
        ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ
          ↑ replaceTy
              (Fin.suc (aslotXᴾ (alias-slot-future a W≼W′)))
              (⇑ᵗ (aslotRᴾ (alias-slot-future a W≼W′)))
              (liftPreciseBody W≼W′ B) 〗)
reveal-alias-innerᵇ W a {B = B} {C = C} source {k = k}
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} dat W′ W≼W′ Rᴾ Rᴵ r q = final
  where
  step = alias-step W′ Rᴾ
  Wb = aliasBindWorld W′ Rᴾ
  W≼Wb : Future W Wb
  W≼Wb = future-alias W≼W′

  a′ = alias-slot-future a W≼W′
  a₁ = alias-slot-future a′ step
  a₂ = fresh-alias-slot W′ Rᴾ
  Xᴾ′ = aslotXᴾ a′
  Rᴾ′ = aslotRᴾ a′
  B′ = liftPreciseBody W≼W′ B
  C′ = liftImpreciseBody W≼W′ C
  D′ = replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′

  source′ : BodyImprecisionᵇ Wb
      (renameᵗ (extᵗ Fin.suc) B′) C′
  source′ = body-imprecisionᵇ-future W≼Wb source

  r₀ : ＇ Fin.zero ⊑ᵂ⟨ core Wb ⟩ Rᴵ
  r₀ = fresh-alias-local-imprecision W′ r

  opened : renameᵗ (extᵗ Fin.suc) B′ [ ＇ Fin.zero ]ᵗ
      ⊑ᵂ⟨ core Wb ⟩ C′ [ Rᴵ ]ᵗ
  opened = openRelatedBodyImprecision {W = Wb} (bodyPᵇ source′) r₀

  core-related : ComputationsRelated Wb
      (FutureValueRelation opened) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ ⦂∀ C′ [ Rᴵ ])
      (⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
        ⦂∀ renameᵗ (extᵗ Fin.suc) B′ [ ＇ Fin.zero ])
  core-related = proj₁ (data-chainᵇ dat)
    Wb W≼Wb (＇ Fin.zero) Rᴵ r₀ opened

  open-P : renameᵗ (extᵗ Fin.suc) B′ [ ＇ Fin.zero ]ᵗ ≡ B′
  open-P = open-shifted-body B′

  t₀ : impEnv (core Wb) I.⊢ embedPrecise (core Wb) B′ ⊑
      embedImprecise (core Wb) (C′ [ Rᴵ ]ᵗ)
  t₀ = subst≡
    (λ L → impEnv (core Wb) I.⊢ L ⊑
      embedImprecise (core Wb) (C′ [ Rᴵ ]ᵗ))
    (cong (embedPrecise (core Wb)) open-P) opened

  reindexed : ComputationsRelated Wb (FutureValueRelation t₀) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ ⦂∀ C′ [ Rᴵ ])
      (⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
        ⦂∀ renameᵗ (extᵗ Fin.suc) B′ [ ＇ Fin.zero ])
  reindexed = Closure.computations-related-reindex opened t₀
    (cong (embedPrecise (core Wb)) open-P) refl refl refl core-related

  avoidᴵ : acenter a₁ ∉ᵗ embedImprecise (core Wb) (C′ [ Rᴵ ]ᵗ)
  avoidᴵ = alias-embed-∉ a₁ (C′ [ Rᴵ ]ᵗ)

  t₁ : impEnv (core Wb) I.⊢
      replaceTy (acenter a₁)
        (embedPrecise (core Wb) (aslotRᴾ a₁))
        (embedPrecise (core Wb) B′)
      ⊑ embedImprecise (core Wb) (C′ [ Rᴵ ]ᵗ)
  t₁ = replace-left-alias-eq-⊑ (acenter a₁) (amode-eq a₁)
    (aliasRep-eq (aatom a₁)) avoidᴵ t₀

  target₁-P : embedPrecise (core Wb)
      (replaceTy (aslotXᴾ a₁) (aslotRᴾ a₁) B′)
      ≡ replaceTy (acenter a₁)
          (embedPrecise (core Wb) (aslotRᴾ a₁))
          (embedPrecise (core Wb) B′)
  target₁-P = alias-embed-replace a₁ B′

  Nᴵ = liftImpreciseTerm W≼W′ Vᴵ
  Nᴾ = ⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
    ⦂∀ renameᵗ (extᵗ Fin.suc) B′ [ ＇ Fin.zero ]

  revealed₁ : ComputationsRelated Wb (FutureValueRelation t₁) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᴾ ↑ 〖 aslotXᴾ a₁ , aslotRᴾ a₁ ↑ B′ 〗)
  revealed₁ = alias-revealed-computations (sizeᵗ B′) (suc k)
    (sizeᵗ B′) (below-allᵇ (suc k) (sizeᵗ B′)) Wb a₁ t₀
    ≤-refl refl t₁ target₁-P reindexed

  wrap-eq-P : (Nᴾ ↑ 〖 aslotXᴾ a₁ , aslotRᴾ a₁ ↑ B′ 〗)
      ≡ (Nᴾ ↑ 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B′ 〗)
  wrap-eq-P = cong₂ (λ X R → Nᴾ ↑ 〖 X , R ↑ B′ 〗)
    (alias-slot-precise-variable-lift a′ step)
    (alias-slot-precise-rep-lift a′ step)

  revealed₁′ : ComputationsRelated Wb (FutureValueRelation t₁) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᴾ ↑ 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B′ 〗)
  revealed₁′ = Closure.computations-related-reindex t₁ t₁
    refl refl refl wrap-eq-P revealed₁

  t₁′ : impEnv (core Wb) I.⊢
      replaceTy (acenter a₁)
        (embedPrecise (core Wb) (aslotRᴾ a₁))
        (embedPrecise (core Wb) B′)
      ⊑ ⇑ᵗ (embedImprecise (core W′) (C′ [ Rᴵ ]ᵗ))
  t₁′ = subst≡
    (λ R → impEnv (core Wb) I.⊢
      replaceTy (acenter a₁)
        (embedPrecise (core Wb) (aslotRᴾ a₁))
        (embedPrecise (core Wb) B′) ⊑ R)
    (embedImprecise-alias-shift (core W′) Rᴾ (C′ [ Rᴵ ]ᵗ)) t₁

  revealed₁″ : ComputationsRelated Wb (FutureValueRelation t₁′) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᴾ ↑ 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B′ 〗)
  revealed₁″ = Closure.computations-related-reindex t₁ t₁′
    refl
    (embedImprecise-alias-shift (core W′) Rᴾ (C′ [ Rᴵ ]ᵗ))
    refl refl revealed₁′

  source₂-P : embedPrecise (core Wb) D′
      ≡ replaceTy (acenter a₁)
          (embedPrecise (core Wb) (aslotRᴾ a₁))
          (embedPrecise (core Wb) B′)
  source₂-P = trans
    (cong₂ (λ X R → embedPrecise (core Wb) (replaceTy X R B′))
      (sym (alias-slot-precise-variable-lift a′ step))
      (sym (alias-slot-precise-rep-lift a′ step)))
    target₁-P

  body-eq-P : liftPreciseBody W≼W′
      (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B)
      ≡ D′
  body-eq-P = trans
    (liftPreciseBody-replace W≼W′ (aslotXᴾ a) (aslotRᴾ a) B)
    (cong₂ (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R) B′)
      (sym (alias-slot-precise-variable-lift a W≼W′))
      (sym (alias-slot-precise-rep-lift a W≼W′)))

  target₂-P : embedPrecise (core Wb)
      (replaceTy Fin.zero (⇑ᵗ Rᴾ) D′)
      ≡ ⇑ᵗ (embedPrecise (core W′)
          (liftPreciseBody W≼W′
            (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B)
            [ Rᴾ ]ᵗ))
  target₂-P = trans
    (cong (embedPrecise (core Wb)) (replace-zero-open Rᴾ D′))
    (trans
      (embedPrecise-alias-shift (core W′) Rᴾ (D′ [ Rᴾ ]ᵗ))
      (cong (λ T → ⇑ᵗ (embedPrecise (core W′) (T [ Rᴾ ]ᵗ)))
        (sym body-eq-P)))

  final : ComputationsRelated Wb
      (FutureValueRelation (liftCenterImprecision step q)) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      ((Nᴾ ↑ 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B′ 〗)
        ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ ↑ D′ 〗)
  final = alias-revealed-computations (sizeᵗ D′) (suc k)
    (sizeᵗ D′) (below-allᵇ (suc k) (sizeᵗ D′)) Wb a₂ t₁′
    ≤-refl source₂-P (liftCenterImprecision step q) target₂-P
    revealed₁″

reveal-alias-chainᵇ : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (a : AliasSlot W)
    {B : Ty (suc Δᴾ)} {C : Ty (suc Δᴵ)}
    (source : BodyImprecisionᵇ W B C)
    (target : BodyImprecisionᵇ W
      (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B) C)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → UniversalDataᵇ W (bodyPᵇ source) B C k Vᴵ Vᴾ
  → UniversalsRelated W (bodyPᵇ target)
      (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B) C k
      Vᴵ (Vᴾ ↑ 〖 aslotXᴾ a , aslotRᴾ a ↑ `∀ B 〗)
reveal-alias-chainᵇ W a source target {k = zero} dat = tt
reveal-alias-chainᵇ W a {B = B} {C = C} source target
    {k = suc k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} dat =
  head ,
  reveal-alias-chainᵇ W a source target
    (universal-dataᵇ-downward dat)
  where
  head : ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) (Rᴾ : Ty Δᴾ′) (Rᴵ : Ty Δᴵ′)
      (r : Rᴾ ⊑ᵂ⟨ core W′ ⟩ Rᴵ)
      (q : liftPreciseBody W≼W′
            (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B)
            [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseBody W≼W′ C [ Rᴵ ]ᵗ)
    → ComputationsRelated W′ (FutureValueRelation q) (suc k)
        (liftImpreciseTerm W≼W′ Vᴵ
          ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
        (liftPreciseTerm W≼W′
            (Vᴾ ↑ 〖 aslotXᴾ a , aslotRᴾ a ↑ `∀ B 〗)
          ⦂∀ liftPreciseBody W≼W′
            (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B)
            [ Rᴾ ])
  head W′ W≼W′ Rᴾ Rᴵ r q =
    Closure.computations-related-reindex q q refl refl refl
      (sym precise-redex-eq) weakened
    where
    step = alias-step W′ Rᴾ
    a′ = alias-slot-future a W≼W′
    Xᴾ′ = aslotXᴾ a′
    Rᴾ′ = aslotRᴾ a′
    B′ = liftPreciseBody W≼W′ B
    Vᴾ′ = liftPreciseTerm W≼W′ Vᴾ
    cᴾ = 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B′ 〗

    precise-body-eq : liftPreciseBody W≼W′
        (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B)
        ≡ replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′
    precise-body-eq = trans
      (liftPreciseBody-replace W≼W′ (aslotXᴾ a) (aslotRᴾ a) B)
      (cong₂ (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R) B′)
        (sym (alias-slot-precise-variable-lift a W≼W′))
        (sym (alias-slot-precise-rep-lift a W≼W′)))

    precise-redex-eq :
        liftPreciseTerm W≼W′
            (Vᴾ ↑ 〖 aslotXᴾ a , aslotRᴾ a ↑ `∀ B 〗)
          ⦂∀ liftPreciseBody W≼W′
            (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B)
            [ Rᴾ ]
      ≡ (Vᴾ′ ↑ `∀↑ cᴾ)
          ⦂∀ replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′ [ Rᴾ ]
    precise-redex-eq
        rewrite alias-lifted-reveal-precise a W≼W′ Vᴾ (`∀ B)
              | liftPreciseTy-universal W≼W′ B
              | precise-body-eq = refl

    stepped : ComputationsRelated W′
        (PostBindValueRelation step q) (suc k)
        (liftImpreciseTerm W≼W′ Vᴵ
          ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
        ((Vᴾ′ ↑ `∀↑ cᴾ)
          ⦂∀ replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′ [ Rᴾ ])
    stepped
        with reveal-type-app-step-question
               {Σ = preciseStore (core W′)} {A = Rᴾ} cᴾ vVᴾ′
      where
      endpoints = data-endpointsᵇ dat
      vVᴾ′ = Closure.precise-value-future W≼W′
        (precise-value endpoints)
    stepped | vVᴾ″ , step-eqᴾ =
      related-alias-bind-step-expand (λ ()) refl
        (β-reveal-∀ vVᴾ″) step-eqᴾ
        (reveal-alias-innerᵇ W a source dat W′ W≼W′ Rᴾ Rᴵ r q)

    weakened : ComputationsRelated W′ (FutureValueRelation q) (suc k)
        (liftImpreciseTerm W≼W′ Vᴵ
          ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
        ((Vᴾ′ ↑ `∀↑ cᴾ)
          ⦂∀ replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′ [ Rᴾ ])
    weakened = post-bind-weaken step q stepped

------------------------------------------------------------------------
-- Precise-only alias wrapper chain concealment
------------------------------------------------------------------------

conceal-alias-innerᵇ : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) (a : AliasSlot W)
    {B : Ty (suc Δᴾ)} {C : Ty (suc Δᴵ)}
    (target : BodyImprecisionᵇ W B C)
    (source : BodyImprecisionᵇ W
      (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B) C)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → UniversalDataᵇ W (bodyPᵇ source)
      (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B) C
      (suc k) Vᴵ Vᴾ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) (Rᴾ : Ty Δᴾ′) (Rᴵ : Ty Δᴵ′)
      (r : Rᴾ ⊑ᵂ⟨ core W′ ⟩ Rᴵ)
      (q : liftPreciseBody W≼W′ B [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseBody W≼W′ C [ Rᴵ ]ᵗ)
  → ComputationsRelated (aliasBindWorld W′ Rᴾ)
      (FutureValueRelation
        (liftCenterImprecision (alias-step W′ Rᴾ) q)) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ
        ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
      (((⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
          ⦂∀ renameᵗ (extᵗ Fin.suc)
            (replaceTy
              (Fin.suc (aslotXᴾ (alias-slot-future a W≼W′)))
              (⇑ᵗ (aslotRᴾ (alias-slot-future a W≼W′)))
              (liftPreciseBody W≼W′ B))
            [ ＇ Fin.zero ])
        ↓ makeConceal
            (Fin.suc (aslotXᴾ (alias-slot-future a W≼W′)))
            (⇑ᵗ (aslotRᴾ (alias-slot-future a W≼W′)))
            (liftPreciseBody W≼W′ B))
        ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ ↑ liftPreciseBody W≼W′ B 〗)
conceal-alias-innerᵇ W a {B = B} {C = C} target source
    {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} dat W′ W≼W′ Rᴾ Rᴵ r q = final
  where
  step = alias-step W′ Rᴾ
  Wb = aliasBindWorld W′ Rᴾ
  W≼Wb : Future W Wb
  W≼Wb = future-alias W≼W′

  a′ = alias-slot-future a W≼W′
  a₁ = alias-slot-future a′ step
  a₂ = fresh-alias-slot W′ Rᴾ
  Xᴾ′ = aslotXᴾ a′
  Rᴾ′ = aslotRᴾ a′
  B′ = liftPreciseBody W≼W′ B
  C′ = liftImpreciseBody W≼W′ C
  D′ = replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′

  body-eq-P : liftPreciseBody W≼W′
      (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B)
      ≡ D′
  body-eq-P = trans
    (liftPreciseBody-replace W≼W′ (aslotXᴾ a) (aslotRᴾ a) B)
    (cong₂ (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R) B′)
      (sym (alias-slot-precise-variable-lift a W≼W′))
      (sym (alias-slot-precise-rep-lift a W≼W′)))

  source′ : BodyImprecisionᵇ Wb
      (renameᵗ (extᵗ Fin.suc) D′) C′
  source′ = body-imprecisionᵇ-subst
    (cong (renameᵗ (extᵗ Fin.suc)) body-eq-P)
    (body-imprecisionᵇ-future W≼Wb source)

  target′ : BodyImprecisionᵇ Wb
      (renameᵗ (extᵗ Fin.suc) B′) C′
  target′ = body-imprecisionᵇ-future W≼Wb target

  r₀ : ＇ Fin.zero ⊑ᵂ⟨ core Wb ⟩ Rᴵ
  r₀ = fresh-alias-local-imprecision W′ r

  opened-source : renameᵗ (extᵗ Fin.suc) D′ [ ＇ Fin.zero ]ᵗ
      ⊑ᵂ⟨ core Wb ⟩ C′ [ Rᴵ ]ᵗ
  opened-source = openRelatedBodyImprecision {W = Wb}
    (bodyPᵇ source′) r₀

  opened-target : renameᵗ (extᵗ Fin.suc) B′ [ ＇ Fin.zero ]ᵗ
      ⊑ᵂ⟨ core Wb ⟩ C′ [ Rᴵ ]ᵗ
  opened-target = openRelatedBodyImprecision {W = Wb}
    (bodyPᵇ target′) r₀

  L′ = liftPreciseBody W≼W′
    (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B)

  source₀ : BodyImprecisionᵇ Wb
      (renameᵗ (extᵗ Fin.suc) L′) C′
  source₀ = body-imprecisionᵇ-future W≼Wb source

  opened-source₀ : renameᵗ (extᵗ Fin.suc) L′ [ ＇ Fin.zero ]ᵗ
      ⊑ᵂ⟨ core Wb ⟩ C′ [ Rᴵ ]ᵗ
  opened-source₀ = openRelatedBodyImprecision {W = Wb}
    (bodyPᵇ source₀) r₀

  opened-source-eq : renameᵗ (extᵗ Fin.suc) L′ [ ＇ Fin.zero ]ᵗ
      ≡ renameᵗ (extᵗ Fin.suc) D′ [ ＇ Fin.zero ]ᵗ
  opened-source-eq = cong
    (λ T → renameᵗ (extᵗ Fin.suc) T [ ＇ Fin.zero ]ᵗ) body-eq-P

  Nᵇ = ⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)

  core-related₀ : ComputationsRelated Wb
      (FutureValueRelation opened-source₀) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᵇ ⦂∀ renameᵗ (extᵗ Fin.suc) L′ [ ＇ Fin.zero ])
  core-related₀ = proj₁ (data-chainᵇ dat)
    Wb W≼Wb (＇ Fin.zero) Rᴵ r₀ opened-source₀

  core-related : ComputationsRelated Wb
      (FutureValueRelation opened-source) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᵇ ⦂∀ renameᵗ (extᵗ Fin.suc) D′ [ ＇ Fin.zero ])
  core-related = Closure.computations-related-reindex
    opened-source₀ opened-source
    (cong (embedPrecise (core Wb)) opened-source-eq) refl refl
    (cong (λ T → Nᵇ ⦂∀ renameᵗ (extᵗ Fin.suc) T [ ＇ Fin.zero ])
      body-eq-P)
    core-related₀

  open-source : renameᵗ (extᵗ Fin.suc) D′ [ ＇ Fin.zero ]ᵗ ≡ D′
  open-source = open-shifted-body D′

  open-target : renameᵗ (extᵗ Fin.suc) B′ [ ＇ Fin.zero ]ᵗ ≡ B′
  open-target = open-shifted-body B′

  t₀q : impEnv (core Wb) I.⊢ embedPrecise (core Wb) D′ ⊑
      embedImprecise (core Wb) (C′ [ Rᴵ ]ᵗ)
  t₀q = subst≡
    (λ L → impEnv (core Wb) I.⊢ L ⊑
      embedImprecise (core Wb) (C′ [ Rᴵ ]ᵗ))
    (cong (embedPrecise (core Wb)) open-source) opened-source

  t₀ : impEnv (core Wb) I.⊢ embedPrecise (core Wb) B′ ⊑
      embedImprecise (core Wb) (C′ [ Rᴵ ]ᵗ)
  t₀ = subst≡
    (λ L → impEnv (core Wb) I.⊢ L ⊑
      embedImprecise (core Wb) (C′ [ Rᴵ ]ᵗ))
    (cong (embedPrecise (core Wb)) open-target) opened-target

  Nᴵ = liftImpreciseTerm W≼W′ Vᴵ
  Nᴾ = ⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
    ⦂∀ renameᵗ (extᵗ Fin.suc) D′ [ ＇ Fin.zero ]

  reindexed : ComputationsRelated Wb (FutureValueRelation t₀q) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ]) Nᴾ
  reindexed = Closure.computations-related-reindex opened-source t₀q
    (cong (embedPrecise (core Wb)) open-source) refl refl refl
    core-related

  source₁-P : embedPrecise (core Wb)
      (replaceTy (aslotXᴾ a₁) (aslotRᴾ a₁) B′)
      ≡ embedPrecise (core Wb) D′
  source₁-P = cong₂
    (λ X R → embedPrecise (core Wb) (replaceTy X R B′))
    (alias-slot-precise-variable-lift a′ step)
    (alias-slot-precise-rep-lift a′ step)

  concealed₁ : ComputationsRelated Wb (FutureValueRelation t₀) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᴾ ↓ makeConceal (aslotXᴾ a₁) (aslotRᴾ a₁) B′)
  concealed₁ = alias-concealed-computations (sizeᵗ B′) (suc k)
    (sizeᵗ B′) (below-allᵇ (suc k) (sizeᵗ B′)) Wb a₁ t₀
    ≤-refl refl t₀q source₁-P reindexed

  wrap-eq-P :
      (Nᴾ ↓ makeConceal (aslotXᴾ a₁) (aslotRᴾ a₁) B′)
      ≡ (Nᴾ ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′)
  wrap-eq-P = cong₂ (λ X R → Nᴾ ↓ makeConceal X R B′)
    (alias-slot-precise-variable-lift a′ step)
    (alias-slot-precise-rep-lift a′ step)

  concealed₁′ : ComputationsRelated Wb (FutureValueRelation t₀) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᴾ ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′)
  concealed₁′ = Closure.computations-related-reindex t₀ t₀
    refl refl refl wrap-eq-P concealed₁

  t₀′ : impEnv (core Wb) I.⊢ embedPrecise (core Wb) B′ ⊑
      ⇑ᵗ (embedImprecise (core W′) (C′ [ Rᴵ ]ᵗ))
  t₀′ = subst≡
    (λ R → impEnv (core Wb) I.⊢ embedPrecise (core Wb) B′ ⊑ R)
    (embedImprecise-alias-shift (core W′) Rᴾ (C′ [ Rᴵ ]ᵗ)) t₀

  concealed₁″ : ComputationsRelated Wb (FutureValueRelation t₀′) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᴾ ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′)
  concealed₁″ = Closure.computations-related-reindex t₀ t₀′
    refl
    (embedImprecise-alias-shift (core W′) Rᴾ (C′ [ Rᴵ ]ᵗ))
    refl refl concealed₁′

  target₂-P : embedPrecise (core Wb)
      (replaceTy Fin.zero (⇑ᵗ Rᴾ) B′)
      ≡ ⇑ᵗ (embedPrecise (core W′) (B′ [ Rᴾ ]ᵗ))
  target₂-P = trans
    (cong (embedPrecise (core Wb)) (replace-zero-open Rᴾ B′))
    (embedPrecise-alias-shift (core W′) Rᴾ (B′ [ Rᴾ ]ᵗ))

  final : ComputationsRelated Wb
      (FutureValueRelation (liftCenterImprecision step q)) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      ((Nᴾ ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′)
        ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ ↑ B′ 〗)
  final = alias-revealed-computations (sizeᵗ B′) (suc k)
    (sizeᵗ B′) (below-allᵇ (suc k) (sizeᵗ B′)) Wb a₂ t₀′
    ≤-refl refl (liftCenterImprecision step q) target₂-P concealed₁″

conceal-alias-chainᵇ : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (a : AliasSlot W)
    {B : Ty (suc Δᴾ)} {C : Ty (suc Δᴵ)}
    (target : BodyImprecisionᵇ W B C)
    (source : BodyImprecisionᵇ W
      (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B) C)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → UniversalDataᵇ W (bodyPᵇ source)
      (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B) C
      k Vᴵ Vᴾ
  → UniversalsRelated W (bodyPᵇ target) B C k Vᴵ
      (Vᴾ ↓ makeConceal (aslotXᴾ a) (aslotRᴾ a) (`∀ B))
conceal-alias-chainᵇ W a target source {k = zero} dat = tt
conceal-alias-chainᵇ W a {B = B} {C = C} target source
    {k = suc k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} dat =
  head ,
  conceal-alias-chainᵇ W a target source
    (universal-dataᵇ-downward dat)
  where
  head : ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) (Rᴾ : Ty Δᴾ′) (Rᴵ : Ty Δᴵ′)
      (r : Rᴾ ⊑ᵂ⟨ core W′ ⟩ Rᴵ)
      (q : liftPreciseBody W≼W′ B [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseBody W≼W′ C [ Rᴵ ]ᵗ)
    → ComputationsRelated W′ (FutureValueRelation q) (suc k)
        (liftImpreciseTerm W≼W′ Vᴵ
          ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
        (liftPreciseTerm W≼W′
            (Vᴾ ↓ makeConceal (aslotXᴾ a) (aslotRᴾ a) (`∀ B))
          ⦂∀ liftPreciseBody W≼W′ B [ Rᴾ ])
  head W′ W≼W′ Rᴾ Rᴵ r q =
    Closure.computations-related-reindex q q refl refl refl
      (sym precise-redex-eq) weakened
    where
    step = alias-step W′ Rᴾ
    a′ = alias-slot-future a W≼W′
    Xᴾ′ = aslotXᴾ a′
    Rᴾ′ = aslotRᴾ a′
    B′ = liftPreciseBody W≼W′ B
    Vᴾ′ = liftPreciseTerm W≼W′ Vᴾ
    aᴾ = makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′

    precise-redex-eq :
        liftPreciseTerm W≼W′
            (Vᴾ ↓ makeConceal (aslotXᴾ a) (aslotRᴾ a) (`∀ B))
          ⦂∀ liftPreciseBody W≼W′ B [ Rᴾ ]
      ≡ (Vᴾ′ ↓ `∀↓ aᴾ) ⦂∀ B′ [ Rᴾ ]
    precise-redex-eq
        rewrite alias-lifted-conceal-precise a W≼W′ Vᴾ (`∀ B)
              | liftPreciseTy-universal W≼W′ B = refl

    stepped : ComputationsRelated W′
        (PostBindValueRelation step q) (suc k)
        (liftImpreciseTerm W≼W′ Vᴵ
          ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
        ((Vᴾ′ ↓ `∀↓ aᴾ) ⦂∀ B′ [ Rᴾ ])
    stepped
        with conceal-type-app-step-question
               {Σ = preciseStore (core W′)} {A = Rᴾ} aᴾ vVᴾ′
      where
      endpoints = data-endpointsᵇ dat
      vVᴾ′ = Closure.precise-value-future W≼W′
        (precise-value endpoints)
    stepped | vVᴾ″ , step-eqᴾ =
      related-alias-bind-step-expand (λ ()) refl
        (β-conceal-∀ vVᴾ″) step-eqᴾ
        (conceal-alias-innerᵇ W a target source dat W′ W≼W′
          Rᴾ Rᴵ r q)

    weakened : ComputationsRelated W′ (FutureValueRelation q) (suc k)
        (liftImpreciseTerm W≼W′ Vᴵ
          ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
        ((Vᴾ′ ↓ `∀↓ aᴾ) ⦂∀ B′ [ Rᴾ ])
    weakened = post-bind-weaken step q stepped

------------------------------------------------------------------------
-- Precise-only inert wrapper chain reveal
------------------------------------------------------------------------

reveal-inert-innerᵇ : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
    {B : Ty (suc Δᴾ)} {C : Ty (suc Δᴵ)}
    (no-occur : slotXᴾ s ∉ᵗ `∀ B)
    (source : BodyImprecisionᵇ W B C)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → UniversalDataᵇ W (bodyPᵇ source) B C (suc k) Vᴵ Vᴾ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) (Rᴾ : Ty Δᴾ′) (Rᴵ : Ty Δᴵ′)
      (r : Rᴾ ⊑ᵂ⟨ core W′ ⟩ Rᴵ)
      (q : liftPreciseBody W≼W′ B [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseBody W≼W′ C [ Rᴵ ]ᵗ)
  → ComputationsRelated (aliasBindWorld W′ Rᴾ)
      (FutureValueRelation
        (liftCenterImprecision (alias-step W′ Rᴾ) q)) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ
        ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
      (((⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
          ⦂∀ renameᵗ (extᵗ Fin.suc) (liftPreciseBody W≼W′ B)
            [ ＇ Fin.zero ])
        ↑ 〖 Fin.suc (slotXᴾ (slot-future s W≼W′)) ,
            ⇑ᵗ (slotRᴾ (slot-future s W≼W′))
            ↑ liftPreciseBody W≼W′ B 〗)
        ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ
          ↑ replaceTy
              (Fin.suc (slotXᴾ (slot-future s W≼W′)))
              (⇑ᵗ (slotRᴾ (slot-future s W≼W′)))
              (liftPreciseBody W≼W′ B) 〗)
reveal-inert-innerᵇ W s {B = B} {C = C} no-occur source
    {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} dat W′ W≼W′ Rᴾ Rᴵ r q = final
  where
  step = alias-step W′ Rᴾ
  Wb = aliasBindWorld W′ Rᴾ
  W≼Wb : Future W Wb
  W≼Wb = future-alias W≼W′

  s′ = slot-future s W≼W′
  s₁ = slot-future s′ step
  a₂ = fresh-alias-slot W′ Rᴾ
  Xᴾ′ = slotXᴾ s′
  Rᴾ′ = slotRᴾ s′
  B′ = liftPreciseBody W≼W′ B
  C′ = liftImpreciseBody W≼W′ C
  D′ = replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′

  source′ : BodyImprecisionᵇ Wb
      (renameᵗ (extᵗ Fin.suc) B′) C′
  source′ = body-imprecisionᵇ-future W≼Wb source

  r₀ : ＇ Fin.zero ⊑ᵂ⟨ core Wb ⟩ Rᴵ
  r₀ = fresh-alias-local-imprecision W′ r

  opened : renameᵗ (extᵗ Fin.suc) B′ [ ＇ Fin.zero ]ᵗ
      ⊑ᵂ⟨ core Wb ⟩ C′ [ Rᴵ ]ᵗ
  opened = openRelatedBodyImprecision {W = Wb} (bodyPᵇ source′) r₀

  core-related : ComputationsRelated Wb
      (FutureValueRelation opened) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ ⦂∀ C′ [ Rᴵ ])
      (⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
        ⦂∀ renameᵗ (extᵗ Fin.suc) B′ [ ＇ Fin.zero ])
  core-related = proj₁ (data-chainᵇ dat)
    Wb W≼Wb (＇ Fin.zero) Rᴵ r₀ opened

  open-P : renameᵗ (extᵗ Fin.suc) B′ [ ＇ Fin.zero ]ᵗ ≡ B′
  open-P = open-shifted-body B′

  t₀ : impEnv (core Wb) I.⊢ embedPrecise (core Wb) B′ ⊑
      embedImprecise (core Wb) (C′ [ Rᴵ ]ᵗ)
  t₀ = subst≡
    (λ L → impEnv (core Wb) I.⊢ L ⊑
      embedImprecise (core Wb) (C′ [ Rᴵ ]ᵗ))
    (cong (embedPrecise (core Wb)) open-P) opened

  Nᴵ = liftImpreciseTerm W≼W′ Vᴵ
  Nᴾ = ⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
    ⦂∀ renameᵗ (extᵗ Fin.suc) B′ [ ＇ Fin.zero ]

  reindexed : ComputationsRelated Wb (FutureValueRelation t₀) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ]) Nᴾ
  reindexed = Closure.computations-related-reindex opened t₀
    (cong (embedPrecise (core Wb)) open-P) refl refl refl core-related

  slot-absent : slotXᴾ s₁ ∉ᵗ B′
  slot-absent = subst≡ (_∉ᵗ B′)
    (sym (slot-precise-variable-lift s′ step))
    (∉-all-inv
      (subst≡ (slotXᴾ s′ ∉ᵗ_) (liftPreciseTy-universal W≼W′ B)
        (subst≡ (_∉ᵗ liftPreciseTy W≼W′ (`∀ B))
          (sym (slot-precise-variable-lift s W≼W′))
          (lift-∉ᵗ W≼W′ no-occur))))

  revealed₁ : ComputationsRelated Wb (FutureValueRelation t₀) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᴾ ↑ 〖 slotXᴾ s₁ , slotRᴾ s₁ ↑ B′ 〗)
  revealed₁ = precise-revealed-computations (sizeᵗ B′) (suc k)
    (below-allᵇ (suc k) (sizeᵗ B′)) Wb s₁ t₀
    ≤-refl slot-absent refl reindexed

  wrap-eq-P : (Nᴾ ↑ 〖 slotXᴾ s₁ , slotRᴾ s₁ ↑ B′ 〗)
      ≡ (Nᴾ ↑ 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B′ 〗)
  wrap-eq-P = cong₂ (λ X R → Nᴾ ↑ 〖 X , R ↑ B′ 〗)
    (slot-precise-variable-lift s′ step)
    (slot-precise-rep-lift s′ step)

  revealed₁′ : ComputationsRelated Wb (FutureValueRelation t₀) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᴾ ↑ 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B′ 〗)
  revealed₁′ = Closure.computations-related-reindex t₀ t₀
    refl refl refl wrap-eq-P revealed₁

  t₀′ : impEnv (core Wb) I.⊢ embedPrecise (core Wb) B′ ⊑
      ⇑ᵗ (embedImprecise (core W′) (C′ [ Rᴵ ]ᵗ))
  t₀′ = subst≡
    (λ R → impEnv (core Wb) I.⊢ embedPrecise (core Wb) B′ ⊑ R)
    (embedImprecise-alias-shift (core W′) Rᴾ (C′ [ Rᴵ ]ᵗ)) t₀

  revealed₁″ : ComputationsRelated Wb (FutureValueRelation t₀′) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᴾ ↑ 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B′ 〗)
  revealed₁″ = Closure.computations-related-reindex t₀ t₀′
    refl
    (embedImprecise-alias-shift (core W′) Rᴾ (C′ [ Rᴵ ]ᵗ))
    refl refl revealed₁′

  body-id : D′ ≡ B′
  body-id = replaceTy-absent (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′)
    (subst≡ (_∉ᵗ B′) (slot-precise-variable-lift s′ step)
      slot-absent)

  source₂-P : embedPrecise (core Wb) D′
      ≡ embedPrecise (core Wb) B′
  source₂-P = cong (embedPrecise (core Wb)) body-id

  target₂-P : embedPrecise (core Wb)
      (replaceTy Fin.zero (⇑ᵗ Rᴾ) D′)
      ≡ ⇑ᵗ (embedPrecise (core W′) (B′ [ Rᴾ ]ᵗ))
  target₂-P = trans
    (cong (embedPrecise (core Wb)) (replace-zero-open Rᴾ D′))
    (trans
      (embedPrecise-alias-shift (core W′) Rᴾ (D′ [ Rᴾ ]ᵗ))
      (cong (λ T → ⇑ᵗ (embedPrecise (core W′) (T [ Rᴾ ]ᵗ)))
        body-id))

  final : ComputationsRelated Wb
      (FutureValueRelation (liftCenterImprecision step q)) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      ((Nᴾ ↑ 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B′ 〗)
        ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ ↑ D′ 〗)
  final = alias-revealed-computations (sizeᵗ D′) (suc k)
    (sizeᵗ D′) (below-allᵇ (suc k) (sizeᵗ D′)) Wb a₂ t₀′
    ≤-refl source₂-P (liftCenterImprecision step q) target₂-P
    revealed₁″

reveal-inert-chainᵇ : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {B : Ty (suc Δᴾ)} {C : Ty (suc Δᴵ)}
    (no-occur : slotXᴾ s ∉ᵗ `∀ B)
    (source : BodyImprecisionᵇ W B C)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → UniversalDataᵇ W (bodyPᵇ source) B C k Vᴵ Vᴾ
  → UniversalsRelated W (bodyPᵇ source) B C k Vᴵ
      (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B 〗)
reveal-inert-chainᵇ W s no-occur source {k = zero} dat = tt
reveal-inert-chainᵇ W s {B = B} {C = C} no-occur source
    {k = suc k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} dat =
  head ,
  reveal-inert-chainᵇ W s no-occur source
    (universal-dataᵇ-downward dat)
  where
  head : ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) (Rᴾ : Ty Δᴾ′) (Rᴵ : Ty Δᴵ′)
      (r : Rᴾ ⊑ᵂ⟨ core W′ ⟩ Rᴵ)
      (q : liftPreciseBody W≼W′ B [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseBody W≼W′ C [ Rᴵ ]ᵗ)
    → ComputationsRelated W′ (FutureValueRelation q) (suc k)
        (liftImpreciseTerm W≼W′ Vᴵ
          ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
        (liftPreciseTerm W≼W′
            (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B 〗)
          ⦂∀ liftPreciseBody W≼W′ B [ Rᴾ ])
  head W′ W≼W′ Rᴾ Rᴵ r q =
    Closure.computations-related-reindex q q refl refl refl
      (sym precise-redex-eq) weakened
    where
    step = alias-step W′ Rᴾ
    s′ = slot-future s W≼W′
    Xᴾ′ = slotXᴾ s′
    Rᴾ′ = slotRᴾ s′
    B′ = liftPreciseBody W≼W′ B
    Vᴾ′ = liftPreciseTerm W≼W′ Vᴾ
    D′ = replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′
    cᴾ = 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B′ 〗

    slot-absent′ : Fin.suc Xᴾ′ ∉ᵗ B′
    slot-absent′ = ∉-all-inv
      (subst≡ (Xᴾ′ ∉ᵗ_) (liftPreciseTy-universal W≼W′ B)
        (subst≡ (_∉ᵗ liftPreciseTy W≼W′ (`∀ B))
          (sym (slot-precise-variable-lift s W≼W′))
          (lift-∉ᵗ W≼W′ no-occur)))

    body-id : D′ ≡ B′
    body-id = replaceTy-absent (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′)
      slot-absent′

    lifted-wrapper-eq : liftPreciseTerm W≼W′
        (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B 〗)
        ≡ Vᴾ′ ↑ `∀↑ cᴾ
    lifted-wrapper-eq
        rewrite lifted-reveal-precise s W≼W′ Vᴾ (`∀ B)
              | liftPreciseTy-universal W≼W′ B = refl

    precise-redex-eq :
        liftPreciseTerm W≼W′
            (Vᴾ ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B 〗)
          ⦂∀ B′ [ Rᴾ ]
      ≡ (Vᴾ′ ↑ `∀↑ cᴾ) ⦂∀ D′ [ Rᴾ ]
    precise-redex-eq = trans
      (cong (λ M → M ⦂∀ B′ [ Rᴾ ]) lifted-wrapper-eq)
      (cong (λ T → (Vᴾ′ ↑ `∀↑ cᴾ) ⦂∀ T [ Rᴾ ])
        (sym body-id))

    stepped : ComputationsRelated W′
        (PostBindValueRelation step q) (suc k)
        (liftImpreciseTerm W≼W′ Vᴵ
          ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
        ((Vᴾ′ ↑ `∀↑ cᴾ) ⦂∀ D′ [ Rᴾ ])
    stepped
        with reveal-type-app-step-question
               {Σ = preciseStore (core W′)} {A = Rᴾ} cᴾ vVᴾ′
      where
      endpoints = data-endpointsᵇ dat
      vVᴾ′ = Closure.precise-value-future W≼W′
        (precise-value endpoints)
    stepped | vVᴾ″ , step-eqᴾ =
      related-alias-bind-step-expand (λ ()) refl
        (β-reveal-∀ vVᴾ″) step-eqᴾ
        (reveal-inert-innerᵇ W s no-occur source dat W′ W≼W′
          Rᴾ Rᴵ r q)

    weakened : ComputationsRelated W′ (FutureValueRelation q) (suc k)
        (liftImpreciseTerm W≼W′ Vᴵ
          ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
        ((Vᴾ′ ↑ `∀↑ cᴾ) ⦂∀ D′ [ Rᴾ ])
    weakened = post-bind-weaken step q stepped

------------------------------------------------------------------------
-- Precise-only inert wrapper chain concealment
------------------------------------------------------------------------

conceal-inert-innerᵇ : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
    {B : Ty (suc Δᴾ)} {C : Ty (suc Δᴵ)}
    (no-occur : slotXᴾ s ∉ᵗ `∀ B)
    (source : BodyImprecisionᵇ W B C)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → UniversalDataᵇ W (bodyPᵇ source) B C (suc k) Vᴵ Vᴾ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) (Rᴾ : Ty Δᴾ′) (Rᴵ : Ty Δᴵ′)
      (r : Rᴾ ⊑ᵂ⟨ core W′ ⟩ Rᴵ)
      (q : liftPreciseBody W≼W′ B [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseBody W≼W′ C [ Rᴵ ]ᵗ)
  → ComputationsRelated (aliasBindWorld W′ Rᴾ)
      (FutureValueRelation
        (liftCenterImprecision (alias-step W′ Rᴾ) q)) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ
        ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
      (((⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
          ⦂∀ renameᵗ (extᵗ Fin.suc)
            (replaceTy
              (Fin.suc (slotXᴾ (slot-future s W≼W′)))
              (⇑ᵗ (slotRᴾ (slot-future s W≼W′)))
              (liftPreciseBody W≼W′ B))
            [ ＇ Fin.zero ])
        ↓ makeConceal
            (Fin.suc (slotXᴾ (slot-future s W≼W′)))
            (⇑ᵗ (slotRᴾ (slot-future s W≼W′)))
            (liftPreciseBody W≼W′ B))
        ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ ↑ liftPreciseBody W≼W′ B 〗)
conceal-inert-innerᵇ W s {B = B} {C = C} no-occur source
    {k = k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} dat W′ W≼W′ Rᴾ Rᴵ r q = final
  where
  step = alias-step W′ Rᴾ
  Wb = aliasBindWorld W′ Rᴾ
  W≼Wb : Future W Wb
  W≼Wb = future-alias W≼W′

  s′ = slot-future s W≼W′
  s₁ = slot-future s′ step
  a₂ = fresh-alias-slot W′ Rᴾ
  Xᴾ′ = slotXᴾ s′
  Rᴾ′ = slotRᴾ s′
  B′ = liftPreciseBody W≼W′ B
  C′ = liftImpreciseBody W≼W′ C
  D′ = replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′

  slot-absent′ : Fin.suc Xᴾ′ ∉ᵗ B′
  slot-absent′ = ∉-all-inv
    (subst≡ (Xᴾ′ ∉ᵗ_) (liftPreciseTy-universal W≼W′ B)
      (subst≡ (_∉ᵗ liftPreciseTy W≼W′ (`∀ B))
        (sym (slot-precise-variable-lift s W≼W′))
        (lift-∉ᵗ W≼W′ no-occur)))

  body-eq-P : B′ ≡ D′
  body-eq-P = sym
    (replaceTy-absent (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) slot-absent′)

  source′ : BodyImprecisionᵇ Wb
      (renameᵗ (extᵗ Fin.suc) D′) C′
  source′ = body-imprecisionᵇ-subst
    (cong (renameᵗ (extᵗ Fin.suc)) body-eq-P)
    (body-imprecisionᵇ-future W≼Wb source)

  target′ : BodyImprecisionᵇ Wb
      (renameᵗ (extᵗ Fin.suc) B′) C′
  target′ = body-imprecisionᵇ-future W≼Wb source

  r₀ : ＇ Fin.zero ⊑ᵂ⟨ core Wb ⟩ Rᴵ
  r₀ = fresh-alias-local-imprecision W′ r

  opened-source : renameᵗ (extᵗ Fin.suc) D′ [ ＇ Fin.zero ]ᵗ
      ⊑ᵂ⟨ core Wb ⟩ C′ [ Rᴵ ]ᵗ
  opened-source = openRelatedBodyImprecision {W = Wb}
    (bodyPᵇ source′) r₀

  opened-target : renameᵗ (extᵗ Fin.suc) B′ [ ＇ Fin.zero ]ᵗ
      ⊑ᵂ⟨ core Wb ⟩ C′ [ Rᴵ ]ᵗ
  opened-target = openRelatedBodyImprecision {W = Wb}
    (bodyPᵇ target′) r₀

  L′ = B′

  source₀ : BodyImprecisionᵇ Wb
      (renameᵗ (extᵗ Fin.suc) L′) C′
  source₀ = body-imprecisionᵇ-future W≼Wb source

  opened-source₀ : renameᵗ (extᵗ Fin.suc) L′ [ ＇ Fin.zero ]ᵗ
      ⊑ᵂ⟨ core Wb ⟩ C′ [ Rᴵ ]ᵗ
  opened-source₀ = openRelatedBodyImprecision {W = Wb}
    (bodyPᵇ source₀) r₀

  opened-source-eq : renameᵗ (extᵗ Fin.suc) L′ [ ＇ Fin.zero ]ᵗ
      ≡ renameᵗ (extᵗ Fin.suc) D′ [ ＇ Fin.zero ]ᵗ
  opened-source-eq = cong
    (λ T → renameᵗ (extᵗ Fin.suc) T [ ＇ Fin.zero ]ᵗ) body-eq-P

  Nᵇ = ⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)

  core-related₀ : ComputationsRelated Wb
      (FutureValueRelation opened-source₀) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᵇ ⦂∀ renameᵗ (extᵗ Fin.suc) L′ [ ＇ Fin.zero ])
  core-related₀ = proj₁ (data-chainᵇ dat)
    Wb W≼Wb (＇ Fin.zero) Rᴵ r₀ opened-source₀

  core-related : ComputationsRelated Wb
      (FutureValueRelation opened-source) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᵇ ⦂∀ renameᵗ (extᵗ Fin.suc) D′ [ ＇ Fin.zero ])
  core-related = Closure.computations-related-reindex
    opened-source₀ opened-source
    (cong (embedPrecise (core Wb)) opened-source-eq) refl refl
    (cong (λ T → Nᵇ ⦂∀ renameᵗ (extᵗ Fin.suc) T [ ＇ Fin.zero ])
      body-eq-P)
    core-related₀

  open-source : renameᵗ (extᵗ Fin.suc) D′ [ ＇ Fin.zero ]ᵗ ≡ D′
  open-source = open-shifted-body D′

  open-target : renameᵗ (extᵗ Fin.suc) B′ [ ＇ Fin.zero ]ᵗ ≡ B′
  open-target = open-shifted-body B′

  t₀q : impEnv (core Wb) I.⊢ embedPrecise (core Wb) D′ ⊑
      embedImprecise (core Wb) (C′ [ Rᴵ ]ᵗ)
  t₀q = subst≡
    (λ L → impEnv (core Wb) I.⊢ L ⊑
      embedImprecise (core Wb) (C′ [ Rᴵ ]ᵗ))
    (cong (embedPrecise (core Wb)) open-source) opened-source

  t₀ : impEnv (core Wb) I.⊢ embedPrecise (core Wb) B′ ⊑
      embedImprecise (core Wb) (C′ [ Rᴵ ]ᵗ)
  t₀ = subst≡
    (λ L → impEnv (core Wb) I.⊢ L ⊑
      embedImprecise (core Wb) (C′ [ Rᴵ ]ᵗ))
    (cong (embedPrecise (core Wb)) open-target) opened-target

  Nᴵ = liftImpreciseTerm W≼W′ Vᴵ
  Nᴾ = ⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
    ⦂∀ renameᵗ (extᵗ Fin.suc) D′ [ ＇ Fin.zero ]

  reindexed : ComputationsRelated Wb (FutureValueRelation t₀q) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ]) Nᴾ
  reindexed = Closure.computations-related-reindex opened-source t₀q
    (cong (embedPrecise (core Wb)) open-source) refl refl refl
    core-related

  left-agree : embedPrecise (core Wb) D′
      ≡ embedPrecise (core Wb) B′
  left-agree = cong (embedPrecise (core Wb)) (sym body-eq-P)

  reindexed₀ : ComputationsRelated Wb (FutureValueRelation t₀) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ]) Nᴾ
  reindexed₀ = Closure.computations-related-reindex t₀q t₀
    left-agree refl refl refl reindexed

  slot-absent : slotXᴾ s₁ ∉ᵗ B′
  slot-absent = subst≡ (_∉ᵗ B′)
    (sym (slot-precise-variable-lift s′ step)) slot-absent′

  concealed₁ : ComputationsRelated Wb (FutureValueRelation t₀) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᴾ ↓ makeConceal (slotXᴾ s₁) (slotRᴾ s₁) B′)
  concealed₁ = precise-concealed-computations (sizeᵗ B′) (suc k)
    (below-allᵇ (suc k) (sizeᵗ B′)) Wb s₁ t₀
    ≤-refl slot-absent refl reindexed₀

  wrap-eq-P :
      (Nᴾ ↓ makeConceal (slotXᴾ s₁) (slotRᴾ s₁) B′)
      ≡ (Nᴾ ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′)
  wrap-eq-P = cong₂ (λ X R → Nᴾ ↓ makeConceal X R B′)
    (slot-precise-variable-lift s′ step)
    (slot-precise-rep-lift s′ step)

  concealed₁′ : ComputationsRelated Wb (FutureValueRelation t₀) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᴾ ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′)
  concealed₁′ = Closure.computations-related-reindex t₀ t₀
    refl refl refl wrap-eq-P concealed₁

  t₀′ : impEnv (core Wb) I.⊢ embedPrecise (core Wb) B′ ⊑
      ⇑ᵗ (embedImprecise (core W′) (C′ [ Rᴵ ]ᵗ))
  t₀′ = subst≡
    (λ R → impEnv (core Wb) I.⊢ embedPrecise (core Wb) B′ ⊑ R)
    (embedImprecise-alias-shift (core W′) Rᴾ (C′ [ Rᴵ ]ᵗ)) t₀

  concealed₁″ : ComputationsRelated Wb (FutureValueRelation t₀′) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      (Nᴾ ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′)
  concealed₁″ = Closure.computations-related-reindex t₀ t₀′
    refl
    (embedImprecise-alias-shift (core W′) Rᴾ (C′ [ Rᴵ ]ᵗ))
    refl refl concealed₁′

  target₂-P : embedPrecise (core Wb)
      (replaceTy Fin.zero (⇑ᵗ Rᴾ) B′)
      ≡ ⇑ᵗ (embedPrecise (core W′) (B′ [ Rᴾ ]ᵗ))
  target₂-P = trans
    (cong (embedPrecise (core Wb)) (replace-zero-open Rᴾ B′))
    (embedPrecise-alias-shift (core W′) Rᴾ (B′ [ Rᴾ ]ᵗ))

  final : ComputationsRelated Wb
      (FutureValueRelation (liftCenterImprecision step q)) (suc k)
      (Nᴵ ⦂∀ C′ [ Rᴵ ])
      ((Nᴾ ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′)
        ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ ↑ B′ 〗)
  final = alias-revealed-computations (sizeᵗ B′) (suc k)
    (sizeᵗ B′) (below-allᵇ (suc k) (sizeᵗ B′)) Wb a₂ t₀′
    ≤-refl refl (liftCenterImprecision step q) target₂-P concealed₁″

conceal-inert-chainᵇ : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W)
    {B : Ty (suc Δᴾ)} {C : Ty (suc Δᴵ)}
    (no-occur : slotXᴾ s ∉ᵗ `∀ B)
    (source : BodyImprecisionᵇ W B C)
  → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → UniversalDataᵇ W (bodyPᵇ source) B C k Vᴵ Vᴾ
  → UniversalsRelated W (bodyPᵇ source) B C k Vᴵ
      (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ B))
conceal-inert-chainᵇ W s no-occur source {k = zero} dat = tt
conceal-inert-chainᵇ W s {B = B} {C = C} no-occur source
    {k = suc k} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} dat =
  head ,
  conceal-inert-chainᵇ W s no-occur source
    (universal-dataᵇ-downward dat)
  where
  head : ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
      (W≼W′ : Future W W′) (Rᴾ : Ty Δᴾ′) (Rᴵ : Ty Δᴵ′)
      (r : Rᴾ ⊑ᵂ⟨ core W′ ⟩ Rᴵ)
      (q : liftPreciseBody W≼W′ B [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseBody W≼W′ C [ Rᴵ ]ᵗ)
    → ComputationsRelated W′ (FutureValueRelation q) (suc k)
        (liftImpreciseTerm W≼W′ Vᴵ
          ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
        (liftPreciseTerm W≼W′
            (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ B))
          ⦂∀ liftPreciseBody W≼W′ B [ Rᴾ ])
  head W′ W≼W′ Rᴾ Rᴵ r q =
    Closure.computations-related-reindex q q refl refl refl
      (sym precise-redex-eq) weakened
    where
    step = alias-step W′ Rᴾ
    s′ = slot-future s W≼W′
    Xᴾ′ = slotXᴾ s′
    Rᴾ′ = slotRᴾ s′
    B′ = liftPreciseBody W≼W′ B
    Vᴾ′ = liftPreciseTerm W≼W′ Vᴾ
    sᴾ = makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B′

    precise-redex-eq :
        liftPreciseTerm W≼W′
            (Vᴾ ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ B))
          ⦂∀ liftPreciseBody W≼W′ B [ Rᴾ ]
      ≡ (Vᴾ′ ↓ `∀↓ sᴾ) ⦂∀ B′ [ Rᴾ ]
    precise-redex-eq
        rewrite lifted-conceal-precise s W≼W′ Vᴾ (`∀ B)
              | liftPreciseTy-universal W≼W′ B = refl

    stepped : ComputationsRelated W′
        (PostBindValueRelation step q) (suc k)
        (liftImpreciseTerm W≼W′ Vᴵ
          ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
        ((Vᴾ′ ↓ `∀↓ sᴾ) ⦂∀ B′ [ Rᴾ ])
    stepped
        with conceal-type-app-step-question
               {Σ = preciseStore (core W′)} {A = Rᴾ} sᴾ vVᴾ′
      where
      endpoints = data-endpointsᵇ dat
      vVᴾ′ = Closure.precise-value-future W≼W′
        (precise-value endpoints)
    stepped | vVᴾ″ , step-eqᴾ =
      related-alias-bind-step-expand (λ ()) refl
        (β-conceal-∀ vVᴾ″) step-eqᴾ
        (conceal-inert-innerᵇ W s no-occur source dat W′ W≼W′
          Rᴾ Rᴵ r q)

    weakened : ComputationsRelated W′ (FutureValueRelation q) (suc k)
        (liftImpreciseTerm W≼W′ Vᴵ
          ⦂∀ liftImpreciseBody W≼W′ C [ Rᴵ ])
        ((Vᴾ′ ↓ `∀↓ sᴾ) ⦂∀ B′ [ Rᴾ ])
    weakened = post-bind-weaken step q stepped

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
