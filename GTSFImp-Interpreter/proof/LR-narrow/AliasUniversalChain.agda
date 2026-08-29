open import proof.LR-narrow.RevealStatements

module proof.LR-narrow.AliasUniversalChain where

-- File Charter:
--   * Extends right-universal instantiation chains across one alias-slot
--     reveal or conceal wrapper.
--   * Reuses the alias computation transformer at the inherited slot and
--     the dynamic transformer at the fresh precise instantiation slot.
--   * Supplies the alias cases of the generic right-universal family kit.

open import Data.Nat using (ℕ; suc; _≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)
import Data.Fin as Fin

open import Types
open import TyStore
open import CastTerms
open import Conversion using
  (`∀↑_; `∀↓_; replaceTy; 〖_,_↑_〗; makeConceal)
open import Consistency using (toRenameᵗ)
import Imprecision as I
open import Reduction
open import proof.ImprecisionConsistency using (ty-all-injective)

open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.UniversalFamily
import proof.LR-narrow.Closure as ClosureProof
open import proof.LR-narrow.BindStepExpansion using
  (related-precise-bind-step-expand)
open import proof.LR-narrow.TypeBetaExpansion using (precise-step)
open import proof.LR-narrow.UniversalReveal using
  (reveal-type-app-step-question; conceal-type-app-step-question;
   post-bind-weaken; embed-body-lift-precise;
   embed-precise-precise-bind-body; right-universals-head;
   liftPreciseBody-replace)
open import proof.LR-narrow.ReplaceImprecision using
  (replace-left-alias-eq-⊑; replace-zero-open; open-shifted-body)
open import proof.LR-narrow.ImprecisionSize using (sizeᵖ)
open import proof.LR-narrow.PreciseReveal using (sizeᵗ)
open import proof.LR-narrow.AliasReveal using
  (alias-revealed-computations; alias-concealed-computations;
   alias-slot-future; alias-slot-precise-variable-lift;
   alias-slot-precise-rep-lift; alias-lifted-reveal-precise;
   alias-lifted-conceal-precise; alias-embed-replace; alias-embed-∉)
open import proof.LR-narrow.DynamicReveal using
  (dyn-revealed-computations)

reveal-alias-universal-inner : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) (a : AliasSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Ac)
  → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Bc)
  → ∀ {k n : ℕ} (below : Below (suc k) n)
      (size< : suc (sizeᵖ p₀) ≤ n)
      {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvar occurs p₀ B₀ᴾ Bᴵ (suc k) Vᴵ Vᴾ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′) (W≼W′ : Future W W′)
      (Rᴾ : Ty Δᴾ′)
      (r★ : impEnv (core W′) I.⊢ embedPrecise (core W′) Rᴾ ⊑ ★)
      (t : liftPreciseBody W≼W′
            (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B₀ᴾ)
            [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseTy W≼W′ Bᴵ)
  → ComputationsRelated (preciseBindWorld W′ Rᴾ r★)
      (FutureValueRelation
        (liftCenterImprecision (precise-step W′ r★) t)) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ)
      (((⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
          ⦂∀ renameᵗ (extᵗ Fin.suc) (liftPreciseBody W≼W′ B₀ᴾ)
            [ ＇ Fin.zero ])
        ↑ 〖 Fin.suc (aslotXᴾ (alias-slot-future a W≼W′)) ,
            ⇑ᵗ (aslotRᴾ (alias-slot-future a W≼W′))
            ↑ liftPreciseBody W≼W′ B₀ᴾ 〗)
        ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ
          ↑ replaceTy (Fin.suc (aslotXᴾ (alias-slot-future a W≼W′)))
              (⇑ᵗ (aslotRᴾ (alias-slot-future a W≼W′)))
              (liftPreciseBody W≼W′ B₀ᴾ) 〗)
reveal-alias-universal-inner W a {B₀ᴾ = B₀ᴾ} {Bᴵ = Bᴵ}
    {Ac = Ac} {Bc = Bc} nonvar occurs p₀ sourceᴾ sourceᴵ
    {k = k} {n = n} below size< {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} dat
    W′ W≼W′ Rᴾ r★ t = final
  where
  chain = data-chain dat

  Wb = preciseBindWorld W′ Rᴾ r★

  W≼Wb : Future W Wb
  W≼Wb = future-precise W≼W′ r★

  a′ = alias-slot-future a W≼W′
  a₁ = alias-slot-future a′ (precise-step W′ r★)
  a₂ : DynamicSlot Wb
  a₂ = dynamic-slot Fin.zero
    (fresh-dynamic-semantic-atom (core W′) Rᴾ r★) is-dynamic
  Xᴾ′ = aslotXᴾ a′
  Rᴾ′ = aslotRᴾ a′
  B₀ᴾ′ = liftPreciseBody W≼W′ B₀ᴾ
  Bᴰ = replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′

  p₀′ : I.instᵐ (impEnv (core W′)) I.⊢
      liftCenterBody W≼W′ Ac ⊑ liftCenterBody W≼W′ (⇑ᵗ Bc)
  p₀′ = liftCenterDynamicBodyImprecision W≼W′ p₀

  Ac-eq : Ac
      ≡ renameᵗ (extᵗ (toRenameᵗ (preciseEmbedding (core W)))) B₀ᴾ
  Ac-eq = ty-all-injective (sym sourceᴾ)

  embed-eq-P : embedPrecise (core Wb) B₀ᴾ′ ≡ liftCenterBody W≼W′ Ac
  embed-eq-P = trans
    (embed-precise-precise-bind-body (core W′) Rᴾ B₀ᴾ′)
    (trans (embed-body-lift-precise W≼W′ B₀ᴾ)
      (cong (liftCenterBody W≼W′) (sym Ac-eq)))

  shift-eq : embedImprecise (core Wb) (liftImpreciseTy W≼Wb Bᴵ)
      ≡ ⇑ᵗ (liftCenterTy W≼W′ Bc)
  shift-eq = trans
    (embedImprecise-precise-shift (core W′) Rᴾ
      (liftImpreciseTy W≼W′ Bᴵ))
    (trans (cong ⇑ᵗ (embedImprecise-lift W≼W′ Bᴵ))
      (cong (λ T → ⇑ᵗ (liftCenterTy W≼W′ T)) sourceᴵ))

  right-eq : liftCenterBody W≼W′ (⇑ᵗ Bc)
      ≡ embedImprecise (core Wb) (liftImpreciseTy W≼Wb Bᴵ)
  right-eq = trans (liftCenterBody-shift W≼W′ Bc) (sym shift-eq)

  t₀ : impEnv (core Wb) I.⊢ embedPrecise (core Wb) B₀ᴾ′
      ⊑ embedImprecise (core Wb) (liftImpreciseTy W≼Wb Bᴵ)
  t₀ = subst≡
    (λ L → impEnv (core Wb) I.⊢ L
      ⊑ embedImprecise (core Wb) (liftImpreciseTy W≼Wb Bᴵ))
    (sym embed-eq-P)
    (subst≡
      (λ R → impEnv (core Wb) I.⊢ liftCenterBody W≼W′ Ac ⊑ R)
      right-eq p₀′)

  open-P : renameᵗ (extᵗ Fin.suc) B₀ᴾ′ [ ＇ Fin.zero ]ᵗ ≡ B₀ᴾ′
  open-P = open-shifted-body B₀ᴾ′

  s₀ : renameᵗ (extᵗ Fin.suc) B₀ᴾ′ [ ＇ Fin.zero ]ᵗ
      ⊑ᵂ⟨ core Wb ⟩ liftImpreciseTy W≼Wb Bᴵ
  s₀ = subst≡
    (λ L → L ⊑ᵂ⟨ core Wb ⟩ liftImpreciseTy W≼Wb Bᴵ)
    (sym open-P) t₀

  r₀ : impEnv (core Wb) I.⊢
      embedPrecise (core Wb) (＇ Fin.zero) ⊑ ★
  r₀ = I.X⊑★ refl

  core-related : ComputationsRelated Wb
      (PostBindValueRelation
        (future-precise (future-refl {W = Wb}) r₀) s₀) (suc k)
      (liftImpreciseTerm W≼Wb Vᴵ)
      (liftPreciseTerm W≼Wb Vᴾ
        ⦂∀ liftPreciseBody W≼Wb B₀ᴾ [ ＇ Fin.zero ])
  core-related = right-universals-head {W = W} {p = p₀} {Bᴾ = B₀ᴾ}
    {Bᴵ = Bᴵ} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} {n = suc k}
    k ≤-refl chain
    Wb W≼Wb (＇ Fin.zero) r₀ s₀

  weakened : ComputationsRelated Wb (FutureValueRelation s₀) (suc k)
      (liftImpreciseTerm W≼Wb Vᴵ)
      (liftPreciseTerm W≼Wb Vᴾ
        ⦂∀ liftPreciseBody W≼Wb B₀ᴾ [ ＇ Fin.zero ])
  weakened = post-bind-weaken
    (future-precise (future-refl {W = Wb}) r₀) s₀ core-related

  reindexed : ComputationsRelated Wb (FutureValueRelation t₀) (suc k)
      (liftImpreciseTerm W≼Wb Vᴵ)
      (liftPreciseTerm W≼Wb Vᴾ
        ⦂∀ liftPreciseBody W≼Wb B₀ᴾ [ ＇ Fin.zero ])
  reindexed = ClosureProof.computations-related-reindex s₀ t₀
    (cong (embedPrecise (core Wb)) open-P)
    refl refl refl weakened

  avoidᴵ : acenter a₁
      ∉ᵗ embedImprecise (core Wb) (liftImpreciseTy W≼Wb Bᴵ)
  avoidᴵ = alias-embed-∉ a₁ (liftImpreciseTy W≼Wb Bᴵ)

  t₁ : impEnv (core Wb) I.⊢
      replaceTy (acenter a₁)
        (embedPrecise (core Wb) (aslotRᴾ a₁))
        (embedPrecise (core Wb) B₀ᴾ′)
      ⊑ embedImprecise (core Wb) (liftImpreciseTy W≼Wb Bᴵ)
  t₁ = replace-left-alias-eq-⊑ (acenter a₁) (amode-eq a₁)
    (aliasRep-eq (aatom a₁)) avoidᴵ t₀

  target₁-P : embedPrecise (core Wb)
      (replaceTy (aslotXᴾ a₁) (aslotRᴾ a₁) B₀ᴾ′)
      ≡ replaceTy (acenter a₁)
          (embedPrecise (core Wb) (aslotRᴾ a₁))
          (embedPrecise (core Wb) B₀ᴾ′)
  target₁-P = alias-embed-replace a₁ B₀ᴾ′

  Nᴵ = liftImpreciseTerm W≼W′ Vᴵ
  Nᴾ = ⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
    ⦂∀ renameᵗ (extᵗ Fin.suc) B₀ᴾ′ [ ＇ Fin.zero ]

  revealed₁ : ComputationsRelated Wb (FutureValueRelation t₁) (suc k)
      Nᴵ (Nᴾ ↑ 〖 aslotXᴾ a₁ , aslotRᴾ a₁ ↑ B₀ᴾ′ 〗)
  revealed₁ = alias-revealed-computations (sizeᵗ B₀ᴾ′) (suc k) n below
    Wb a₁ t₀ ≤-refl refl t₁ target₁-P reindexed

  wrap-eq-P : (Nᴾ ↑ 〖 aslotXᴾ a₁ , aslotRᴾ a₁ ↑ B₀ᴾ′ 〗)
      ≡ (Nᴾ ↑ 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B₀ᴾ′ 〗)
  wrap-eq-P = cong₂ (λ X R → Nᴾ ↑ 〖 X , R ↑ B₀ᴾ′ 〗)
    (alias-slot-precise-variable-lift a′ (precise-step W′ r★))
    (alias-slot-precise-rep-lift a′ (precise-step W′ r★))

  revealed₁′ : ComputationsRelated Wb (FutureValueRelation t₁)
      (suc k)
      Nᴵ (Nᴾ ↑ 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B₀ᴾ′ 〗)
  revealed₁′ = ClosureProof.computations-related-reindex t₁ t₁
    refl refl refl wrap-eq-P revealed₁

  t₁′ : impEnv (core Wb) I.⊢
      replaceTy (acenter a₁)
        (embedPrecise (core Wb) (aslotRᴾ a₁))
        (embedPrecise (core Wb) B₀ᴾ′)
      ⊑ ⇑ᵗ (embedImprecise (core W′) (liftImpreciseTy W≼W′ Bᴵ))
  t₁′ = subst≡
    (λ R → impEnv (core Wb) I.⊢
      replaceTy (acenter a₁)
        (embedPrecise (core Wb) (aslotRᴾ a₁))
        (embedPrecise (core Wb) B₀ᴾ′) ⊑ R)
    (embedImprecise-precise-shift (core W′) Rᴾ
      (liftImpreciseTy W≼W′ Bᴵ))
    t₁

  revealed₁″ : ComputationsRelated Wb (FutureValueRelation t₁′)
      (suc k)
      Nᴵ (Nᴾ ↑ 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B₀ᴾ′ 〗)
  revealed₁″ = ClosureProof.computations-related-reindex t₁ t₁′
    refl
    (embedImprecise-precise-shift (core W′) Rᴾ
      (liftImpreciseTy W≼W′ Bᴵ))
    refl refl revealed₁′

  source₂-P : embedPrecise (core Wb) Bᴰ
      ≡ replaceTy (acenter a₁)
          (embedPrecise (core Wb) (aslotRᴾ a₁))
          (embedPrecise (core Wb) B₀ᴾ′)
  source₂-P = trans
    (cong₂ (λ X R → embedPrecise (core Wb) (replaceTy X R B₀ᴾ′))
      (sym (alias-slot-precise-variable-lift a′ (precise-step W′ r★)))
      (sym (alias-slot-precise-rep-lift a′ (precise-step W′ r★))))
    target₁-P

  body-eq-P : liftPreciseBody W≼W′
      (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B₀ᴾ)
      ≡ Bᴰ
  body-eq-P = trans
    (liftPreciseBody-replace W≼W′ (aslotXᴾ a) (aslotRᴾ a) B₀ᴾ)
    (cong₂ (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R) B₀ᴾ′)
      (sym (alias-slot-precise-variable-lift a W≼W′))
      (sym (alias-slot-precise-rep-lift a W≼W′)))

  target₂-P : embedPrecise (core Wb)
      (replaceTy Fin.zero (⇑ᵗ Rᴾ) Bᴰ)
      ≡ ⇑ᵗ (embedPrecise (core W′)
          (liftPreciseBody W≼W′
            (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B₀ᴾ)
            [ Rᴾ ]ᵗ))
  target₂-P = trans
    (cong (embedPrecise (core Wb)) (replace-zero-open Rᴾ Bᴰ))
    (trans
      (embedPrecise-precise-shift (core W′) Rᴾ (Bᴰ [ Rᴾ ]ᵗ))
      (cong (λ T → ⇑ᵗ (embedPrecise (core W′) (T [ Rᴾ ]ᵗ)))
        (sym body-eq-P)))

  final : ComputationsRelated Wb
      (FutureValueRelation
        (liftCenterImprecision (precise-step W′ r★) t)) (suc k)
      Nᴵ
      ((Nᴾ ↑ 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B₀ᴾ′ 〗)
        ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ ↑ Bᴰ 〗)
  final = dyn-revealed-computations (sizeᵗ Bᴰ) (suc k) n below
    Wb a₂ t₁′ ≤-refl source₂-P
    (liftCenterImprecision (precise-step W′ r★) t)
    target₂-P
    revealed₁″

reveal-alias-universal-head : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) (a : AliasSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Ac)
  → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Bc)
  → ∀ {k n : ℕ} (below : Below (suc k) n)
      (size< : suc (sizeᵖ p₀) ≤ n)
      {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvar occurs p₀ B₀ᴾ Bᴵ (suc k) Vᴵ Vᴾ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′) (W≼W′ : Future W W′)
      (Rᴾ : Ty Δᴾ′)
      (r★ : impEnv (core W′) I.⊢ embedPrecise (core W′) Rᴾ ⊑ ★)
      (t : liftPreciseBody W≼W′
            (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B₀ᴾ)
            [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseTy W≼W′ Bᴵ)
  → ComputationsRelated W′
      (PostBindValueRelation
        (future-precise (future-refl {W = W′}) r★) t) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ)
      (liftPreciseTerm W≼W′
        (Vᴾ ↑ 〖 aslotXᴾ a , aslotRᴾ a ↑ `∀ B₀ᴾ 〗)
        ⦂∀ liftPreciseBody W≼W′
          (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B₀ᴾ)
          [ Rᴾ ])
reveal-alias-universal-head W a {B₀ᴾ = B₀ᴾ} {Bᴵ = Bᴵ}
    nonvar occurs p₀ sourceᴾ sourceᴵ
    {k = k} {n = n} below size< {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} dat
    W′ W≼W′ Rᴾ r★ t =
  ClosureProof.computations-related-post-bind-reindex t t
    refl refl refl (sym precise-redex-eq)
    stepped
  where
  a′ = alias-slot-future a W≼W′
  Xᴾ′ = aslotXᴾ a′
  Rᴾ′ = aslotRᴾ a′
  B₀ᴾ′ = liftPreciseBody W≼W′ B₀ᴾ
  Vᴾ′ = liftPreciseTerm W≼W′ Vᴾ
  cᴾ = 〖 Fin.suc Xᴾ′ , ⇑ᵗ Rᴾ′ ↑ B₀ᴾ′ 〗

  precise-body-eq :
      liftPreciseBody W≼W′
        (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B₀ᴾ)
      ≡ replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′
  precise-body-eq = trans
    (liftPreciseBody-replace W≼W′ (aslotXᴾ a) (aslotRᴾ a) B₀ᴾ)
    (cong₂ (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R) B₀ᴾ′)
      (sym (alias-slot-precise-variable-lift a W≼W′))
      (sym (alias-slot-precise-rep-lift a W≼W′)))

  precise-redex-eq :
      liftPreciseTerm W≼W′
        (Vᴾ ↑ 〖 aslotXᴾ a , aslotRᴾ a ↑ `∀ B₀ᴾ 〗)
        ⦂∀ liftPreciseBody W≼W′
          (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B₀ᴾ)
          [ Rᴾ ]
      ≡ (Vᴾ′ ↑ `∀↑ cᴾ)
          ⦂∀ replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′ [ Rᴾ ]
  precise-redex-eq
      rewrite alias-lifted-reveal-precise a W≼W′ Vᴾ (`∀ B₀ᴾ)
            | liftPreciseTy-universal W≼W′ B₀ᴾ
            | precise-body-eq = refl

  stepped : ComputationsRelated W′
      (PostBindValueRelation
        (future-precise (future-refl {W = W′}) r★) t) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ)
      ((Vᴾ′ ↑ `∀↑ cᴾ)
        ⦂∀ replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′ [ Rᴾ ])
  stepped
      with reveal-type-app-step-question
             {Σ = preciseStore (core W′)} {A = Rᴾ} cᴾ vVᴾ′
    where
    endpoints = data-endpoints dat
    vVᴾ′ = ClosureProof.precise-value-future W≼W′
      (precise-value endpoints)
  stepped | vVᴾ″ , step-eqᴾ =
    related-precise-bind-step-expand (λ ()) refl
      (β-reveal-∀ vVᴾ″) step-eqᴾ
      (reveal-alias-universal-inner W a nonvar occurs p₀
        sourceᴾ sourceᴵ below size< dat W′ W≼W′ Rᴾ r★ t)

-- The dual: concealing a right-universal value at a dynamic slot.
-- The chain of the value at the replaced body yields the chain of the
-- concealed value at the original body.

conceal-alias-universal-inner : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) (a : AliasSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    {Acʳ : Ty (suc Δᶜ)}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
    (nonvarʳ : NonVar Acʳ) (occursʳ : Fin.zero ∈ᵗ Acʳ)
    (q₀ : I.instᵐ (impEnv (core W)) I.⊢ Acʳ ⊑ ⇑ᵗ Bc)
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Ac)
  → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Bc)
  → (targetᴾ : embedPrecise (core W)
      (`∀ (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B₀ᴾ))
      ≡ `∀ Acʳ)
  → ∀ {k n : ℕ} (below : Below (suc k) n)
      (size< : suc (sizeᵖ p₀) ≤ n)
      {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvarʳ occursʳ q₀
      (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B₀ᴾ)
      Bᴵ (suc k) Vᴵ Vᴾ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′) (W≼W′ : Future W W′)
      (Rᴾ : Ty Δᴾ′)
      (r★ : impEnv (core W′) I.⊢ embedPrecise (core W′) Rᴾ ⊑ ★)
      (t : liftPreciseBody W≼W′ B₀ᴾ [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseTy W≼W′ Bᴵ)
  → ComputationsRelated (preciseBindWorld W′ Rᴾ r★)
      (FutureValueRelation
        (liftCenterImprecision (precise-step W′ r★) t)) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ)
      (((⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
          ⦂∀ renameᵗ (extᵗ Fin.suc)
              (replaceTy (Fin.suc (aslotXᴾ (alias-slot-future a W≼W′)))
                (⇑ᵗ (aslotRᴾ (alias-slot-future a W≼W′)))
                (liftPreciseBody W≼W′ B₀ᴾ))
            [ ＇ Fin.zero ])
        ↓ makeConceal (Fin.suc (aslotXᴾ (alias-slot-future a W≼W′)))
            (⇑ᵗ (aslotRᴾ (alias-slot-future a W≼W′)))
            (liftPreciseBody W≼W′ B₀ᴾ))
        ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ ↑ liftPreciseBody W≼W′ B₀ᴾ 〗)
conceal-alias-universal-inner W a {B₀ᴾ = B₀ᴾ} {Bᴵ = Bᴵ}
    {Ac = Ac} {Bc = Bc} {Acʳ = Acʳ}
    nonvar occurs p₀ nonvarʳ occursʳ q₀ sourceᴾ sourceᴵ targetᴾ
    {k = k} {n = n} below size< {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} dat
    W′ W≼W′ Rᴾ r★ t = final
  where
  chain = data-chain dat

  Wb = preciseBindWorld W′ Rᴾ r★

  W≼Wb : Future W Wb
  W≼Wb = future-precise W≼W′ r★

  a′ = alias-slot-future a W≼W′
  a₁ = alias-slot-future a′ (precise-step W′ r★)
  a₂ : DynamicSlot Wb
  a₂ = dynamic-slot Fin.zero
    (fresh-dynamic-semantic-atom (core W′) Rᴾ r★) is-dynamic
  Xᴾ′ = aslotXᴾ a′
  Rᴾ′ = aslotRᴾ a′
  B₀ᴾ′ = liftPreciseBody W≼W′ B₀ᴾ
  Bᴰ = replaceTy (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′

  q₀′ : I.instᵐ (impEnv (core W′)) I.⊢
      liftCenterBody W≼W′ Acʳ ⊑ liftCenterBody W≼W′ (⇑ᵗ Bc)
  q₀′ = liftCenterDynamicBodyImprecision W≼W′ q₀

  p₀′ : I.instᵐ (impEnv (core W′)) I.⊢
      liftCenterBody W≼W′ Ac ⊑ liftCenterBody W≼W′ (⇑ᵗ Bc)
  p₀′ = liftCenterDynamicBodyImprecision W≼W′ p₀

  Ac-eq : Ac
      ≡ renameᵗ (extᵗ (toRenameᵗ (preciseEmbedding (core W)))) B₀ᴾ
  Ac-eq = ty-all-injective (sym sourceᴾ)

  Acʳ-eq : Acʳ
      ≡ renameᵗ (extᵗ (toRenameᵗ (preciseEmbedding (core W))))
          (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B₀ᴾ)
  Acʳ-eq = ty-all-injective (sym targetᴾ)

  body-eq-P : liftPreciseBody W≼W′
      (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B₀ᴾ)
      ≡ Bᴰ
  body-eq-P = trans
    (liftPreciseBody-replace W≼W′ (aslotXᴾ a) (aslotRᴾ a) B₀ᴾ)
    (cong₂ (λ X R → replaceTy (Fin.suc X) (⇑ᵗ R) B₀ᴾ′)
      (sym (alias-slot-precise-variable-lift a W≼W′))
      (sym (alias-slot-precise-rep-lift a W≼W′)))

  embed-eq-P : embedPrecise (core Wb) B₀ᴾ′ ≡ liftCenterBody W≼W′ Ac
  embed-eq-P = trans
    (embed-precise-precise-bind-body (core W′) Rᴾ B₀ᴾ′)
    (trans (embed-body-lift-precise W≼W′ B₀ᴾ)
      (cong (liftCenterBody W≼W′) (sym Ac-eq)))

  embed-eq-Pq : embedPrecise (core Wb) Bᴰ
      ≡ liftCenterBody W≼W′ Acʳ
  embed-eq-Pq = trans
    (cong (embedPrecise (core Wb)) (sym body-eq-P))
    (trans
      (embed-precise-precise-bind-body (core W′) Rᴾ
        (liftPreciseBody W≼W′
          (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B₀ᴾ)))
      (trans
        (embed-body-lift-precise W≼W′
          (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B₀ᴾ))
        (cong (liftCenterBody W≼W′) (sym Acʳ-eq))))

  shift-eq : embedImprecise (core Wb) (liftImpreciseTy W≼Wb Bᴵ)
      ≡ ⇑ᵗ (liftCenterTy W≼W′ Bc)
  shift-eq = trans
    (embedImprecise-precise-shift (core W′) Rᴾ
      (liftImpreciseTy W≼W′ Bᴵ))
    (trans (cong ⇑ᵗ (embedImprecise-lift W≼W′ Bᴵ))
      (cong (λ T → ⇑ᵗ (liftCenterTy W≼W′ T)) sourceᴵ))

  right-eq : liftCenterBody W≼W′ (⇑ᵗ Bc)
      ≡ embedImprecise (core Wb) (liftImpreciseTy W≼Wb Bᴵ)
  right-eq = trans (liftCenterBody-shift W≼W′ Bc) (sym shift-eq)

  t₀q : impEnv (core Wb) I.⊢ embedPrecise (core Wb) Bᴰ
      ⊑ embedImprecise (core Wb) (liftImpreciseTy W≼Wb Bᴵ)
  t₀q = subst≡
    (λ L → impEnv (core Wb) I.⊢ L
      ⊑ embedImprecise (core Wb) (liftImpreciseTy W≼Wb Bᴵ))
    (sym embed-eq-Pq)
    (subst≡
      (λ R → impEnv (core Wb) I.⊢ liftCenterBody W≼W′ Acʳ ⊑ R)
      right-eq q₀′)

  t₀ : impEnv (core Wb) I.⊢ embedPrecise (core Wb) B₀ᴾ′
      ⊑ embedImprecise (core Wb) (liftImpreciseTy W≼Wb Bᴵ)
  t₀ = subst≡
    (λ L → impEnv (core Wb) I.⊢ L
      ⊑ embedImprecise (core Wb) (liftImpreciseTy W≼Wb Bᴵ))
    (sym embed-eq-P)
    (subst≡
      (λ R → impEnv (core Wb) I.⊢ liftCenterBody W≼W′ Ac ⊑ R)
      right-eq p₀′)

  Lᴾ = liftPreciseBody W≼W′
    (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B₀ᴾ)

  open-Pq : renameᵗ (extᵗ Fin.suc) Lᴾ [ ＇ Fin.zero ]ᵗ ≡ Bᴰ
  open-Pq = trans (open-shifted-body Lᴾ) body-eq-P

  s₀ : renameᵗ (extᵗ Fin.suc) Lᴾ [ ＇ Fin.zero ]ᵗ
      ⊑ᵂ⟨ core Wb ⟩ liftImpreciseTy W≼Wb Bᴵ
  s₀ = subst≡
    (λ L → L ⊑ᵂ⟨ core Wb ⟩ liftImpreciseTy W≼Wb Bᴵ)
    (sym open-Pq) t₀q

  r₀ : impEnv (core Wb) I.⊢
      embedPrecise (core Wb) (＇ Fin.zero) ⊑ ★
  r₀ = I.X⊑★ refl

  core-related : ComputationsRelated Wb
      (PostBindValueRelation
        (future-precise (future-refl {W = Wb}) r₀) s₀) (suc k)
      (liftImpreciseTerm W≼Wb Vᴵ)
      (liftPreciseTerm W≼Wb Vᴾ
        ⦂∀ liftPreciseBody W≼Wb
          (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B₀ᴾ)
          [ ＇ Fin.zero ])
  core-related = right-universals-head {W = W} {p = q₀}
    {Bᴾ = replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B₀ᴾ}
    {Bᴵ = Bᴵ} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} {n = suc k}
    k ≤-refl chain
    Wb W≼Wb (＇ Fin.zero) r₀ s₀

  weakened : ComputationsRelated Wb (FutureValueRelation s₀) (suc k)
      (liftImpreciseTerm W≼Wb Vᴵ)
      (liftPreciseTerm W≼Wb Vᴾ
        ⦂∀ liftPreciseBody W≼Wb
          (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B₀ᴾ)
          [ ＇ Fin.zero ])
  weakened = post-bind-weaken
    (future-precise (future-refl {W = Wb}) r₀) s₀ core-related

  Nᴵ = liftImpreciseTerm W≼W′ Vᴵ
  Nᴾ = ⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
    ⦂∀ renameᵗ (extᵗ Fin.suc) Lᴾ [ ＇ Fin.zero ]

  reindexed : ComputationsRelated Wb (FutureValueRelation t₀q)
      (suc k) Nᴵ Nᴾ
  reindexed = ClosureProof.computations-related-reindex s₀ t₀q
    (cong (embedPrecise (core Wb)) open-Pq) refl
    refl refl weakened

  avoidᴵ : acenter a₁
      ∉ᵗ embedImprecise (core Wb) (liftImpreciseTy W≼Wb Bᴵ)
  avoidᴵ = alias-embed-∉ a₁ (liftImpreciseTy W≼Wb Bᴵ)

  source₁-P : embedPrecise (core Wb)
      (replaceTy (aslotXᴾ a₁) (aslotRᴾ a₁) B₀ᴾ′)
      ≡ embedPrecise (core Wb) Bᴰ
  source₁-P = cong₂
    (λ X R → embedPrecise (core Wb) (replaceTy X R B₀ᴾ′))
    (alias-slot-precise-variable-lift a′ (precise-step W′ r★))
    (alias-slot-precise-rep-lift a′ (precise-step W′ r★))

  concealed₁ : ComputationsRelated Wb (FutureValueRelation t₀)
      (suc k)
      Nᴵ (Nᴾ ↓ makeConceal (aslotXᴾ a₁) (aslotRᴾ a₁) B₀ᴾ′)
  concealed₁ = alias-concealed-computations (sizeᵗ B₀ᴾ′) (suc k) n
    below Wb a₁ t₀ ≤-refl refl t₀q source₁-P reindexed

  wrap-eq-P : (Nᴾ ↓ makeConceal (aslotXᴾ a₁) (aslotRᴾ a₁) B₀ᴾ′)
      ≡ (Nᴾ ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′)
  wrap-eq-P = cong₂ (λ X R → Nᴾ ↓ makeConceal X R B₀ᴾ′)
    (alias-slot-precise-variable-lift a′ (precise-step W′ r★))
    (alias-slot-precise-rep-lift a′ (precise-step W′ r★))

  concealed₁′ : ComputationsRelated Wb (FutureValueRelation t₀)
      (suc k)
      Nᴵ (Nᴾ ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′)
  concealed₁′ = ClosureProof.computations-related-reindex t₀ t₀
    refl refl refl wrap-eq-P concealed₁

  t₀′ : impEnv (core Wb) I.⊢ embedPrecise (core Wb) B₀ᴾ′
      ⊑ ⇑ᵗ (embedImprecise (core W′) (liftImpreciseTy W≼W′ Bᴵ))
  t₀′ = subst≡
    (λ R → impEnv (core Wb) I.⊢ embedPrecise (core Wb) B₀ᴾ′ ⊑ R)
    (embedImprecise-precise-shift (core W′) Rᴾ
      (liftImpreciseTy W≼W′ Bᴵ))
    t₀

  concealed₁″ : ComputationsRelated Wb (FutureValueRelation t₀′)
      (suc k)
      Nᴵ (Nᴾ ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′)
  concealed₁″ = ClosureProof.computations-related-reindex t₀ t₀′
    refl
    (embedImprecise-precise-shift (core W′) Rᴾ
      (liftImpreciseTy W≼W′ Bᴵ))
    refl refl concealed₁′

  target₂-P : embedPrecise (core Wb)
      (replaceTy Fin.zero (⇑ᵗ Rᴾ) B₀ᴾ′)
      ≡ ⇑ᵗ (embedPrecise (core W′) (B₀ᴾ′ [ Rᴾ ]ᵗ))
  target₂-P = trans
    (cong (embedPrecise (core Wb)) (replace-zero-open Rᴾ B₀ᴾ′))
    (embedPrecise-precise-shift (core W′) Rᴾ (B₀ᴾ′ [ Rᴾ ]ᵗ))

  final₀ : ComputationsRelated Wb
      (FutureValueRelation
        (liftCenterImprecision (precise-step W′ r★) t)) (suc k)
      Nᴵ
      ((Nᴾ ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′)
        ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ ↑ B₀ᴾ′ 〗)
  final₀ = dyn-revealed-computations (sizeᵗ B₀ᴾ′) (suc k) n below
    Wb a₂ t₀′ ≤-refl refl
    (liftCenterImprecision (precise-step W′ r★) t)
    target₂-P
    concealed₁″

  final : ComputationsRelated Wb
      (FutureValueRelation
        (liftCenterImprecision (precise-step W′ r★) t)) (suc k)
      Nᴵ
      ((((⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
            ⦂∀ renameᵗ (extᵗ Fin.suc) Bᴰ [ ＇ Fin.zero ])
          ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′))
        ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ ↑ B₀ᴾ′ 〗)
  final = ClosureProof.computations-related-reindex
    (liftCenterImprecision (precise-step W′ r★) t)
    (liftCenterImprecision (precise-step W′ r★) t)
    refl refl refl
    (cong (λ T →
      ((⇑ᵗᵐ (liftPreciseTerm W≼W′ Vᴾ)
          ⦂∀ renameᵗ (extᵗ Fin.suc) T [ ＇ Fin.zero ])
        ↓ makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′)
        ↑ 〖 Fin.zero , ⇑ᵗ Rᴾ ↑ B₀ᴾ′ 〗)
      body-eq-P)
    final₀

conceal-alias-universal-head : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : World Δᴾ Δᴵ Δᶜ) (a : AliasSlot W)
    {B₀ᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ} {Acʳ : Ty (suc Δᶜ)}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
    (nonvarʳ : NonVar Acʳ) (occursʳ : Fin.zero ∈ᵗ Acʳ)
    (q₀ : I.instᵐ (impEnv (core W)) I.⊢ Acʳ ⊑ ⇑ᵗ Bc)
  → (sourceᴾ : embedPrecise (core W) (`∀ B₀ᴾ) ≡ `∀ Ac)
  → (sourceᴵ : embedImprecise (core W) Bᴵ ≡ Bc)
  → (targetᴾ : embedPrecise (core W)
      (`∀ (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B₀ᴾ))
      ≡ `∀ Acʳ)
  → ∀ {k n : ℕ} (below : Below (suc k) n)
      (size< : suc (sizeᵖ p₀) ≤ n)
      {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → RightUniversalData W nonvarʳ occursʳ q₀
      (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B₀ᴾ)
      Bᴵ (suc k) Vᴵ Vᴾ
  → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′) (W≼W′ : Future W W′)
      (Rᴾ : Ty Δᴾ′)
      (r★ : impEnv (core W′) I.⊢ embedPrecise (core W′) Rᴾ ⊑ ★)
      (t : liftPreciseBody W≼W′ B₀ᴾ [ Rᴾ ]ᵗ
        ⊑ᵂ⟨ core W′ ⟩ liftImpreciseTy W≼W′ Bᴵ)
  → ComputationsRelated W′
      (PostBindValueRelation
        (future-precise (future-refl {W = W′}) r★) t) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ)
      (liftPreciseTerm W≼W′
        (Vᴾ ↓ makeConceal (aslotXᴾ a) (aslotRᴾ a) (`∀ B₀ᴾ))
        ⦂∀ liftPreciseBody W≼W′ B₀ᴾ [ Rᴾ ])
conceal-alias-universal-head W a {B₀ᴾ = B₀ᴾ} {Bᴵ = Bᴵ}
    nonvar occurs p₀ nonvarʳ occursʳ q₀ sourceᴾ sourceᴵ targetᴾ
    {k = k} {n = n} below size< {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} dat
    W′ W≼W′ Rᴾ r★ t =
  ClosureProof.computations-related-post-bind-reindex t t
    refl refl refl (sym precise-redex-eq)
    stepped
  where
  a′ = alias-slot-future a W≼W′
  Xᴾ′ = aslotXᴾ a′
  Rᴾ′ = aslotRᴾ a′
  B₀ᴾ′ = liftPreciseBody W≼W′ B₀ᴾ
  Vᴾ′ = liftPreciseTerm W≼W′ Vᴾ
  aᴾ = makeConceal (Fin.suc Xᴾ′) (⇑ᵗ Rᴾ′) B₀ᴾ′

  precise-redex-eq :
      liftPreciseTerm W≼W′
        (Vᴾ ↓ makeConceal (aslotXᴾ a) (aslotRᴾ a) (`∀ B₀ᴾ))
        ⦂∀ liftPreciseBody W≼W′ B₀ᴾ [ Rᴾ ]
      ≡ (Vᴾ′ ↓ `∀↓ aᴾ) ⦂∀ B₀ᴾ′ [ Rᴾ ]
  precise-redex-eq
      rewrite alias-lifted-conceal-precise a W≼W′ Vᴾ (`∀ B₀ᴾ)
            | liftPreciseTy-universal W≼W′ B₀ᴾ = refl

  stepped : ComputationsRelated W′
      (PostBindValueRelation
        (future-precise (future-refl {W = W′}) r★) t) (suc k)
      (liftImpreciseTerm W≼W′ Vᴵ)
      ((Vᴾ′ ↓ `∀↓ aᴾ) ⦂∀ B₀ᴾ′ [ Rᴾ ])
  stepped
      with conceal-type-app-step-question
             {Σ = preciseStore (core W′)} {A = Rᴾ} aᴾ vVᴾ′
    where
    endpoints = data-endpoints dat
    vVᴾ′ = ClosureProof.precise-value-future W≼W′
      (precise-value endpoints)
  stepped | vVᴾ″ , step-eqᴾ =
    related-precise-bind-step-expand (λ ()) refl
      (β-conceal-∀ vVᴾ″) step-eqᴾ
      (conceal-alias-universal-inner W a nonvar occurs p₀
        nonvarʳ occursʳ q₀ sourceᴾ sourceᴵ targetᴾ
        below size< dat W′ W≼W′ Rᴾ r★ t)
