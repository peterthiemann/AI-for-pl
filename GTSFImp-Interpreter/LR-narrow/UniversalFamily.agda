module LR-narrow.UniversalFamily where

-- File Charter:
--   * States the replacement-closure kit: the ability to turn a bare
--     right-universal instantiation chain into the replacement-closed
--     family stored by the `∀⊑` clause of the logical relation.
--   * The kit's type mentions only the logical relation, so producers
--     of `∀⊑` values (the `Λ` introduction and the structural
--     assemblies) can take it as an argument without depending on the
--     obligation-parameterized reveal development, where its value is
--     constructed.  See REPLACEMENT-CLOSURE-DESIGN.md.

open import Data.Nat using (ℕ; suc; _≤_)
import Data.Fin as Fin
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Types
open import CastTerms
import Imprecision as I
import Consistency as C
import proof.DGG.CtxImp as CTI
open import LR-narrow.World
open import LR-narrow.SlotSequence
open import LR-narrow.LogicalRelation
open import LR-narrow.ClosingSubstitution
open import LR-narrow.ClosingSubstitutionProperties
open import LR-narrow.TermRelation using
  (CompiledUniversalBodyRelation; compiledContext; forgetWorld)

-- The clause data of a right-universal value with the stored family
-- replaced by a bare instantiation chain: exactly what a producer of
-- such a value can establish directly, and what the wrapper
-- extensions consume and produce.

record RightUniversalData {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
    (Bᴾ : Ty (suc Δᴾ)) (Bᴵ : Ty Δᴵ) (k : ℕ)
    (Vᴵ : Term Δᴵ) (Vᴾ : Term Δᴾ) : Set where
  constructor universal-data
  field
    data-endpoints : TypedEndpoints W (I.∀⊑ nonvar occurs p₀) Vᴵ Vᴾ
    data-embedᴾ : embedPrecise (core W) (`∀ Bᴾ) ≡ `∀ Ac
    data-embedᴵ : embedImprecise (core W) Bᴵ ≡ Bc
    data-chain : RightUniversalsRelated W p₀ Bᴾ Bᴵ k Vᴵ Vᴾ

open RightUniversalData public

record RightUniversalFamilyKit : Set where
  field
    to-family : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
        {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty Δᴵ} {k : ℕ}
        {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
        {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
        {nonvar : NonVar Ac} {occurs : Fin.zero ∈ᵗ Ac}
        {p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc}
      → RightUniversalData W nonvar occurs p₀ Bᴾ Bᴵ k Vᴵ Vᴾ
      → RightUniversalFamily W p₀ Bᴾ Bᴵ k Vᴵ Vᴾ

open RightUniversalFamilyKit public

-- Producer data for the two-sided universal cascade.  Unlike the
-- unprovable chain-only interface ruled out by Finding I, this carries
-- both observations needed to cross the asymmetric wrappers: the ordinary
-- instantiation chain and the exact applications of imprecise-only first
-- peels.
-- Ground producers construct this data from their concrete application
-- reductions; wrapper extensions preserve it one step at a time.

record UniversalDataᵇ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    {Aᴾ Aᴵ : Ty (suc Δᶜ)}
    (p : I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ)
    (Bᴾ : Ty (suc Δᴾ)) (Bᴵ : Ty (suc Δᴵ)) (k : ℕ)
    (Vᴵ : Term Δᴵ) (Vᴾ : Term Δᴾ) : Set where
  constructor universal-dataᵇ
  field
    data-endpointsᵇ : TypedEndpoints W (I.∀⊑∀ p) Vᴵ Vᴾ
    data-chainᵇ : UniversalsRelated W p Bᴾ Bᴵ k Vᴵ Vᴾ
    data-pendingᵇ : ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
        {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      → (W≼W′ : Future W W′)
      → PendingTargetUniversalsRelated W′
          (liftPreciseBody W≼W′ Bᴾ) (liftImpreciseBody W≼W′ Bᴵ) k
          (liftImpreciseTerm W≼W′ Vᴵ) (liftPreciseTerm W≼W′ Vᴾ)

open UniversalDataᵇ public

universal-dataᵇ-downward : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Aᴾ Aᴵ : Ty (suc Δᶜ)}
    {p : I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty (suc Δᴵ)} {k : ℕ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → UniversalDataᵇ W p Bᴾ Bᴵ (suc k) Vᴵ Vᴾ
  → UniversalDataᵇ W p Bᴾ Bᴵ k Vᴵ Vᴾ
universal-dataᵇ-downward d = universal-dataᵇ
  (data-endpointsᵇ d) (proj₂ (data-chainᵇ d))
  (λ W≼W′ → proj₂ (data-pendingᵇ d W≼W′))

universal-dataᵇ-of-family : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {Aᴾ Aᴵ : Ty (suc Δᶜ)}
    {p : I.extᵐ (impEnv (core W)) I.⊢ Aᴾ ⊑ Aᴵ}
    {Bᴾ : Ty (suc Δᴾ)} {Bᴵ : Ty (suc Δᴵ)} {k : ℕ}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → TypedEndpoints W (I.∀⊑∀ p) Vᴵ Vᴾ
  → UniversalFamily W p Bᴾ Bᴵ k Vᴵ Vᴾ
  → UniversalDataᵇ W p Bᴾ Bᴵ k Vᴵ Vᴾ
universal-dataᵇ-of-family endpoints family = universal-dataᵇ endpoints
  (proj₁ (family future-refl []))
  (λ W≼W′ → proj₂ (family W≼W′ []))

-- The remaining cast-family obligation for the `∀⊑∀` clause.  A
-- chain-in/family-out
-- statement is UNPROVABLE here (Finding I in
-- REPLACEMENT-CLOSURE-DESIGN.md): a chain undercharacterizes the
-- value, and extending a chain across one wrapper is exactly the
-- blocked one-sided statement.  Universal introduction owns its producer
-- directly; this temporary kit contains only the cast producer until Cast
-- constructs it internally.

record UniversalFamilyKitᵇ : Set where
  field
    -- The one observation which is not generated by the structural
    -- wrapper fold: exact applications whose outermost peel is on the
    -- imprecise endpoint.  Stability under a further future is part of
    -- the interface because `UniversalDataᵇ` stores pending observations
    -- at every future of the world in which each wrapper prefix lives.
    cast-pendingᵇ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
        {Aᴾc Aᴵc Bᴾc Bᴵc : Ty (suc Δᶜ)}
        {Aᴾ₀ Aᴾ₁ : Ty (suc Δᴾ)} {Aᴵ₀ Aᴵ₁ : Ty (suc Δᴵ)}
        (p₀ : I.extᵐ (impEnv (core W)) I.⊢ Aᴾc ⊑ Aᴵc)
      → embedPrecise (core W) (`∀ Aᴾ₀) ≡ `∀ Aᴾc
      → embedImprecise (core W) (`∀ Aᴵ₀) ≡ `∀ Aᴵc
      → ∀ {μᴾ : C.Env∼ Δᴾ}
          (cᴾ : C.extᵐ μᴾ C.⊢ Aᴾ₀ ∼ Aᴾ₁)
          {μᴵ : C.Env∼ Δᴵ}
          (cᴵ : C.extᵐ μᴵ C.⊢ Aᴵ₀ ∼ Aᴵ₁)
          (q₀ : I.extᵐ (impEnv (core W)) I.⊢ Bᴾc ⊑ Bᴵc)
      → embedPrecise (core W) (`∀ Aᴾ₁) ≡ `∀ Bᴾc
      → embedImprecise (core W) (`∀ Aᴵ₁) ≡ `∀ Bᴵc
      → ∀ {k : ℕ} {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
      → ValueImprecision W (I.∀⊑∀ p₀) (suc k) Vᴵ Vᴾ
      → TypedEndpoints W (I.∀⊑∀ q₀)
          (Vᴵ ⟨ C.∀ᶜ cᴵ ⟩) (Vᴾ ⟨ C.∀ᶜ cᴾ ⟩)
      → ∀ {Δᴾ′ Δᴵ′ Δᶜ′}
          {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
          (W≼W′ : Future W W′)
          {Bᴾ′ : Ty (suc Δᴾ′)} {Bᴵ′ : Ty (suc Δᴵ′)}
          (σ : UniWrapsᵇ W′ (liftPreciseBody W≼W′ Aᴾ₁)
            (liftImpreciseBody W≼W′ Aᴵ₁) Bᴾ′ Bᴵ′)
      → ∀ {Δᴾ″ Δᴵ″ Δᶜ″}
          {W″ : World Δᴾ″ Δᴵ″ Δᶜ″}
          (W′≼W″ : Future W′ W″)
      → PendingTargetUniversalsRelated W″
          (liftPreciseBody W′≼W″ Bᴾ′)
          (liftImpreciseBody W′≼W″ Bᴵ′) (suc k)
          (liftImpreciseTerm W′≼W″
            (wrapTermᴵᵇ σ
              (liftImpreciseTerm W≼W′ (Vᴵ ⟨ C.∀ᶜ cᴵ ⟩))))
          (liftPreciseTerm W′≼W″
            (wrapTermᴾᵇ σ
              (liftPreciseTerm W≼W′ (Vᴾ ⟨ C.∀ᶜ cᴾ ⟩))))

open UniversalFamilyKitᵇ public
