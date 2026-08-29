module proof.LR-narrow.StoreChangesCoherence where

-- File Charter:
--   * Proves that store-change sequences with the same context endpoints
--     induce the same action on terms.
--   * Supplies the residual action coherence needed when a known first
--     allocation is removed from a paired computation observation.

open import Data.Empty using (⊥-elim)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; 1+n≰n)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong)

open import Types
open import CastTerms
open import Reduction
open import LR-narrow.World

infixr 5 _++ᶜ_

_++ᶜ_ : ∀ {Δ₀ Δ₁ Δ₂}
  → StoreChanges Δ₀ Δ₁
  → StoreChanges Δ₁ Δ₂
  → StoreChanges Δ₀ Δ₂
[] ++ᶜ ψs = ψs
(χ ∷ χs) ++ᶜ ψs = χ ∷ (χs ++ᶜ ψs)

apply-terms-++ᶜ : ∀ {Δ₀ Δ₁ Δ₂}
    (χs : StoreChanges Δ₀ Δ₁) (ψs : StoreChanges Δ₁ Δ₂)
    (M : Term Δ₀)
  → (χs ++ᶜ ψs) ▶ᵀ M ≡ ψs ▶ᵀ (χs ▶ᵀ M)
apply-terms-++ᶜ [] ψs M = refl
apply-terms-++ᶜ (χ ∷ χs) ψs M =
  apply-terms-++ᶜ χs ψs (χ ▷ᵀ M)

store-changes-monotone : ∀ {Δ Δ′}
  → StoreChanges Δ Δ′
  → Δ ≤ Δ′
store-changes-monotone [] = ≤-refl
store-changes-monotone (keep ∷ χs) = store-changes-monotone χs
store-changes-monotone {Δ = Δ} (bind A ∷ χs) =
  ≤-trans (n≤1+n Δ) (store-changes-monotone χs)

store-changes-terms-unique : ∀ {Δ Δ′}
    (χs ψs : StoreChanges Δ Δ′) (M : Term Δ)
  → χs ▶ᵀ M ≡ ψs ▶ᵀ M
store-changes-terms-unique [] [] M = refl
store-changes-terms-unique [] (keep ∷ ψs) M =
  store-changes-terms-unique [] ψs M
store-changes-terms-unique {Δ = Δ} [] (bind A ∷ ψs) M =
  ⊥-elim (1+n≰n (store-changes-monotone ψs))
store-changes-terms-unique (keep ∷ χs) ψs M =
  store-changes-terms-unique χs ψs M
store-changes-terms-unique {Δ = Δ} (bind A ∷ χs) [] M =
  ⊥-elim (1+n≰n (store-changes-monotone χs))
store-changes-terms-unique (bind A ∷ χs) (keep ∷ ψs) M =
  store-changes-terms-unique (bind A ∷ χs) ψs M
store-changes-terms-unique (bind A ∷ χs) (bind B ∷ ψs) M =
  store-changes-terms-unique χs ψs (⇑ᵗᵐ M)

future-precise-changes : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′ → StoreChanges Δᴾ Δᴾ′
future-precise-changes future-refl = []
future-precise-changes (future-paired {Aᴾ = Aᴾ} W≼W′ r) =
  future-precise-changes W≼W′ ++ᶜ (bind Aᴾ ∷ [])
future-precise-changes (future-precise {Aᴾ = Aᴾ} W≼W′ r) =
  future-precise-changes W≼W′ ++ᶜ (bind Aᴾ ∷ [])
future-precise-changes (future-alias {rep = rep} W≼W′) =
  future-precise-changes W≼W′ ++ᶜ (bind rep ∷ [])
future-precise-changes (future-imprecise W≼W′) =
  future-precise-changes W≼W′

future-imprecise-changes : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → Future W W′ → StoreChanges Δᴵ Δᴵ′
future-imprecise-changes future-refl = []
future-imprecise-changes (future-paired {Aᴵ = Aᴵ} W≼W′ r) =
  future-imprecise-changes W≼W′ ++ᶜ (bind Aᴵ ∷ [])
future-imprecise-changes (future-precise W≼W′ r) =
  future-imprecise-changes W≼W′
future-imprecise-changes (future-alias W≼W′) =
  future-imprecise-changes W≼W′
future-imprecise-changes (future-imprecise {Aᴵ = Aᴵ} W≼W′) =
  future-imprecise-changes W≼W′ ++ᶜ (bind Aᴵ ∷ [])

future-precise-changes-action : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (M : Term Δᴾ)
  → future-precise-changes W≼W′ ▶ᵀ M ≡ liftPreciseTerm W≼W′ M
future-precise-changes-action future-refl M = refl
future-precise-changes-action (future-paired W≼W′ r) M =
  trans (apply-terms-++ᶜ (future-precise-changes W≼W′)
      (bind _ ∷ []) M)
    (cong ⇑ᵗᵐ (future-precise-changes-action W≼W′ M))
future-precise-changes-action (future-precise W≼W′ r) M =
  trans (apply-terms-++ᶜ (future-precise-changes W≼W′)
      (bind _ ∷ []) M)
    (cong ⇑ᵗᵐ (future-precise-changes-action W≼W′ M))
future-precise-changes-action (future-alias W≼W′) M =
  trans (apply-terms-++ᶜ (future-precise-changes W≼W′)
      (bind _ ∷ []) M)
    (cong ⇑ᵗᵐ (future-precise-changes-action W≼W′ M))
future-precise-changes-action (future-imprecise W≼W′) M =
  future-precise-changes-action W≼W′ M

future-imprecise-changes-action : ∀
    {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (M : Term Δᴵ)
  → future-imprecise-changes W≼W′ ▶ᵀ M
      ≡ liftImpreciseTerm W≼W′ M
future-imprecise-changes-action future-refl M = refl
future-imprecise-changes-action (future-paired W≼W′ r) M =
  trans (apply-terms-++ᶜ (future-imprecise-changes W≼W′)
      (bind _ ∷ []) M)
    (cong ⇑ᵗᵐ (future-imprecise-changes-action W≼W′ M))
future-imprecise-changes-action (future-precise W≼W′ r) M =
  future-imprecise-changes-action W≼W′ M
future-imprecise-changes-action (future-alias W≼W′) M =
  future-imprecise-changes-action W≼W′ M
future-imprecise-changes-action (future-imprecise W≼W′) M =
  trans (apply-terms-++ᶜ (future-imprecise-changes W≼W′)
      (bind _ ∷ []) M)
    (cong ⇑ᵗᵐ (future-imprecise-changes-action W≼W′ M))
