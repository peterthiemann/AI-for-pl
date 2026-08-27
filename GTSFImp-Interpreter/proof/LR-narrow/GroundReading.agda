module proof.LR-narrow.GroundReading where

-- File Charter:
--   * Ground readings are unique: two imprecision derivations from
--     one source to types that are images of imprecise GROUNDS reach
--     the same type.
--   * This replaces the target-level agreement lemma that the cast
--     proof used to run on `NonStar` targets.  That statement is
--     false once alias representatives may be arbitrary types
--     (Finding J of REPLACEMENT-CLOSURE-DESIGN.md): a `∀`-shaped
--     representative whose binder occurs reads both as `★ ⇒ ★` (by
--     `∀⊑`, the binder star-discharged) and as itself (by `∀⊑∀`).
--     The second reading is not a ground, and a runtime tag check
--     only ever compares grounds, so restricting both sides to
--     ground images restores uniqueness — the `∀⊑`/`∀⊑∀` fork is
--     cut by the occurrence premise, since a `∀`-ground body is `★`,
--     where the paired binder cannot occur.
--   * The side condition is exactly the alias slots' target
--     non-occupancy: no image of the imprecise embedding is at an
--     alias mode.

open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; z≤n)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; Σ-syntax)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types
import Imprecision as I
import proof.Imprecision as PI
open import proof.ImprecisionConsistency using
  (fin-suc-injective; renameᵗ-injective)
open import proof.LR-narrow.ImprecisionSize using (sizeᵖ)
open import proof.LR-narrow.StarNoOccurrence using
  (star-no-occurrence)

------------------------------------------------------------------------
-- The image of a ground pins down its shape
------------------------------------------------------------------------

ground-image-not-star : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) {H : Ty Δ}
  → Ground H → ★ ≡ renameᵗ ρ H → ⊥
ground-image-not-star ρ (＇ Y) ()
ground-image-not-star ρ (‵ ι) ()
ground-image-not-star ρ ★⇒★ ()
ground-image-not-star ρ ∀★ ()

ground-image-var : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) {H : Ty Δ} {X : TyVar Δ′}
  → Ground H → ＇ X ≡ renameᵗ ρ H
  → Σ[ Y ∈ TyVar Δ ] ρ Y ≡ X
ground-image-var ρ (＇ Y) refl = Y , refl
ground-image-var ρ (‵ ι) ()
ground-image-var ρ ★⇒★ ()
ground-image-var ρ ∀★ ()

ground-image-fun : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) {H : Ty Δ} {A B : Ty Δ′}
  → Ground H → A ⇒ B ≡ renameᵗ ρ H → A ⇒ B ≡ ★ ⇒ ★
ground-image-fun ρ (＇ Y) ()
ground-image-fun ρ (‵ ι) ()
ground-image-fun ρ ★⇒★ refl = refl
ground-image-fun ρ ∀★ ()

ground-image-all : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) {H : Ty Δ}
    {A : Ty (suc Δ′)}
  → Ground H → `∀ A ≡ renameᵗ ρ H → A ≡ ★
ground-image-all ρ (＇ Y) ()
ground-image-all ρ (‵ ι) ()
ground-image-all ρ ★⇒★ ()
ground-image-all ρ ∀★ refl = refl

------------------------------------------------------------------------
-- The side condition
------------------------------------------------------------------------

-- No image of the imprecise embedding is at an alias mode: alias
-- slots are precise-only allocations, which is exactly the
-- `aliasNoTargetOccupant` field of the alias atom.

NoAliasImage : ∀ {Δᴵ Δᶜ} → (Δᴵ ⇒ʳ Δᶜ) → I.ImpEnv Δᶜ → Set
NoAliasImage ρ μ = ∀ Y {T} → μ (ρ Y) ≡ I.X⊑ᵗ T → ⊥

no-alias-image-shift : ∀ {Δᴵ Δᶜ} {ρ : Δᴵ ⇒ʳ Δᶜ} {μ : I.ImpEnv Δᶜ}
    {v : I.VarImp (suc Δᶜ)}
  → NoAliasImage ρ μ
  → NoAliasImage (λ Y → Fin.suc (ρ Y)) (I.extendᵐ v μ)
no-alias-image-shift h Y eq with I.lift-alias-inv eq
no-alias-image-shift h Y eq | T₀ , mode , refl = h Y mode

------------------------------------------------------------------------
-- Ground readings are unique
------------------------------------------------------------------------

ground-readings-unique : ∀ {Δᴵ Δᶜ} {μ : I.ImpEnv Δᶜ}
    (ρ : Δᴵ ⇒ʳ Δᶜ) (fuel : ℕ)
    {A B₁ B₂ : Ty Δᶜ} {H₁ H₂ : Ty Δᴵ}
  → NoAliasImage ρ μ
  → (p : μ I.⊢ A ⊑ B₁)
  → (q : μ I.⊢ A ⊑ B₂)
  → sizeᵖ p ≤ fuel
  → Ground H₁ → Ground H₂
  → B₁ ≡ renameᵗ ρ H₁
  → B₂ ≡ renameᵗ ρ H₂
  → B₁ ≡ B₂
ground-readings-unique ρ fuel na I.★⊑★ q le g₁ g₂ e₁ e₂ =
  ⊥-elim (ground-image-not-star ρ g₁ e₁)
ground-readings-unique ρ fuel na I.ι⊑ι I.ι⊑ι le g₁ g₂ e₁ e₂ = refl
ground-readings-unique ρ fuel na I.ι⊑ι I.ι⊑★ le g₁ g₂ e₁ e₂ =
  ⊥-elim (ground-image-not-star ρ g₂ e₂)
ground-readings-unique ρ fuel na I.X⊑X I.X⊑X le g₁ g₂ e₁ e₂ = refl
ground-readings-unique ρ fuel na I.X⊑X (I.X⊑★ mode) le g₁ g₂
    e₁ e₂ =
  ⊥-elim (ground-image-not-star ρ g₂ e₂)
ground-readings-unique {μ = μ} ρ fuel na I.X⊑X
    (I.alias {T = T} eq q₀) le g₁ g₂ e₁ e₂
    with ground-image-var ρ g₁ e₁
ground-readings-unique {μ = μ} ρ fuel na I.X⊑X
    (I.alias {T = T} eq q₀) le g₁ g₂ e₁ e₂ | Y , ρY≡X =
  ⊥-elim (na Y (subst≡ (λ Z → μ Z ≡ I.X⊑ᵗ T) (sym ρY≡X) eq))
ground-readings-unique ρ fuel na (I.⇒⊑⇒ p₁ p₂) (I.⇒⊑⇒ q₁ q₂) le
    g₁ g₂ e₁ e₂ =
  trans (ground-image-fun ρ g₁ e₁)
    (sym (ground-image-fun ρ g₂ e₂))
ground-readings-unique ρ fuel na (I.⇒⊑⇒ p₁ p₂) (I.⇒⊑★ q₁ q₂) le
    g₁ g₂ e₁ e₂ =
  ⊥-elim (ground-image-not-star ρ g₂ e₂)
ground-readings-unique ρ fuel na (I.∀⊑∀ p₀) (I.∀⊑∀ q₀) le
    g₁ g₂ e₁ e₂ =
  trans (cong `∀ (ground-image-all ρ g₁ e₁))
    (sym (cong `∀ (ground-image-all ρ g₂ e₂)))
ground-readings-unique {μ = μ} ρ fuel na
    (I.∀⊑∀ {A = A₀} p₀) (I.∀⊑ nonvar occurs q₀) le g₁ g₂ e₁ e₂ =
  ⊥-elim (PI.∈∉-⊥
    (star-no-occurrence Fin.zero refl
      (subst≡ (λ T → I.extᵐ μ I.⊢ A₀ ⊑ T)
        (ground-image-all ρ g₁ e₁) p₀))
    occurs)
ground-readings-unique ρ fuel na (I.∀⊑∀ p₀) I.∀★⊑★ le
    g₁ g₂ e₁ e₂ =
  ⊥-elim (ground-image-not-star ρ g₂ e₂)
ground-readings-unique ρ fuel na (I.∀⊑∀ p₀) (I.∀⊑★ nonstar q₀) le
    g₁ g₂ e₁ e₂ =
  ⊥-elim (ground-image-not-star ρ g₂ e₂)
ground-readings-unique ρ fuel na (I.∀⊑∀ p₀) I.bot-elim le
    g₁ g₂ e₁ e₂ =
  trans (cong `∀ (ground-image-all ρ g₁ e₁))
    (sym (cong `∀ (ground-image-all ρ g₂ e₂)))
ground-readings-unique ρ fuel na (I.∀⊑∀ p₀) I.bot⊑★ le
    g₁ g₂ e₁ e₂ =
  ⊥-elim (ground-image-not-star ρ g₂ e₂)
ground-readings-unique ρ fuel na (I.⇒⊑★ p₁ p₂) q le g₁ g₂ e₁ e₂ =
  ⊥-elim (ground-image-not-star ρ g₁ e₁)
ground-readings-unique ρ fuel na I.ι⊑★ q le g₁ g₂ e₁ e₂ =
  ⊥-elim (ground-image-not-star ρ g₁ e₁)
ground-readings-unique ρ fuel na (I.X⊑★ mode) q le g₁ g₂ e₁ e₂ =
  ⊥-elim (ground-image-not-star ρ g₁ e₁)
ground-readings-unique {μ = μ} ρ fuel na
    (I.∀⊑ {A = A₀} nonvar occurs p₀) (I.∀⊑∀ q₀) le g₁ g₂ e₁ e₂ =
  ⊥-elim (PI.∈∉-⊥
    (star-no-occurrence Fin.zero refl
      (subst≡ (λ T → I.extᵐ μ I.⊢ A₀ ⊑ T)
        (ground-image-all ρ g₂ e₂) q₀))
    occurs)
ground-readings-unique {μ = μ} ρ (suc fuel) na
    (I.∀⊑ nonvar occurs p₀)
    (I.∀⊑ nonvar′ occurs′ q₀) (s≤s le) g₁ g₂ e₁ e₂ =
  renameᵗ-injective fin-suc-injective
    (ground-readings-unique (λ Y → Fin.suc (ρ Y)) fuel
      (no-alias-image-shift {ρ = ρ} {μ = μ} {v = I.X⊑★} na)
      p₀ q₀ le g₁ g₂
      (shift-eq e₁) (shift-eq e₂))
  where
  shift-eq : ∀ {B : Ty _} {H : Ty _} → B ≡ renameᵗ ρ H
    → ⇑ᵗ B ≡ renameᵗ (λ Y → Fin.suc (ρ Y)) H
  shift-eq {H = H} eq =
    trans (cong ⇑ᵗ eq) (renameᵗ-comp ρ Fin.suc H)
ground-readings-unique ρ zero na (I.∀⊑ nonvar occurs p₀)
    (I.∀⊑ nonvar′ occurs′ q₀) () g₁ g₂ e₁ e₂
ground-readings-unique ρ fuel na (I.∀⊑ nonvar occurs p₀) I.∀★⊑★ le
    g₁ g₂ e₁ e₂ =
  ⊥-elim (ground-image-not-star ρ g₂ e₂)
ground-readings-unique ρ fuel na (I.∀⊑ nonvar occurs p₀)
    (I.∀⊑★ nonstar q₀) le g₁ g₂ e₁ e₂ =
  ⊥-elim (ground-image-not-star ρ g₂ e₂)
ground-readings-unique ρ fuel na (I.∀⊑ () occurs p₀) I.bot-elim le
    g₁ g₂ e₁ e₂
ground-readings-unique ρ fuel na (I.∀⊑ nonvar occurs p₀) I.bot⊑★ le
    g₁ g₂ e₁ e₂ =
  ⊥-elim (ground-image-not-star ρ g₂ e₂)
ground-readings-unique ρ fuel na I.∀★⊑★ q le g₁ g₂ e₁ e₂ =
  ⊥-elim (ground-image-not-star ρ g₁ e₁)
ground-readings-unique ρ fuel na (I.∀⊑★ nonstar p₀) q le
    g₁ g₂ e₁ e₂ =
  ⊥-elim (ground-image-not-star ρ g₁ e₁)
ground-readings-unique ρ fuel na I.bot-elim (I.∀⊑∀ q₀) le
    g₁ g₂ e₁ e₂ =
  trans (cong `∀ (ground-image-all ρ g₁ e₁))
    (sym (cong `∀ (ground-image-all ρ g₂ e₂)))
ground-readings-unique ρ fuel na I.bot-elim (I.∀⊑ () occurs q₀) le
    g₁ g₂ e₁ e₂
ground-readings-unique ρ fuel na I.bot-elim (I.∀⊑★ nonstar q₀) le
    g₁ g₂ e₁ e₂ =
  ⊥-elim (ground-image-not-star ρ g₂ e₂)
ground-readings-unique ρ fuel na I.bot-elim I.bot-elim le
    g₁ g₂ e₁ e₂ = refl
ground-readings-unique ρ fuel na I.bot-elim I.bot⊑★ le
    g₁ g₂ e₁ e₂ =
  ⊥-elim (ground-image-not-star ρ g₂ e₂)
ground-readings-unique ρ fuel na I.bot⊑★ q le g₁ g₂ e₁ e₂ =
  ⊥-elim (ground-image-not-star ρ g₁ e₁)
ground-readings-unique {μ = μ} ρ fuel na
    (I.alias {T = T} eq p₀) I.X⊑X le g₁ g₂ e₁ e₂
    with ground-image-var ρ g₂ e₂
ground-readings-unique {μ = μ} ρ fuel na
    (I.alias {T = T} eq p₀) I.X⊑X le g₁ g₂ e₁ e₂ | Y , ρY≡X =
  ⊥-elim (na Y (subst≡ (λ Z → μ Z ≡ I.X⊑ᵗ T) (sym ρY≡X) eq))
ground-readings-unique ρ fuel na (I.alias eq p₀) (I.X⊑★ mode) le
    g₁ g₂ e₁ e₂ =
  ⊥-elim (ground-image-not-star ρ g₂ e₂)
ground-readings-unique {μ = μ} ρ (suc fuel) na
    (I.alias {T = T} eq p₀) (I.alias {T = T′} eq′ q₀) (s≤s le)
    g₁ g₂ e₁ e₂ =
  ground-readings-unique ρ fuel na p₀
    (subst≡ (λ S → μ I.⊢ S ⊑ _) (sym rep-eq) q₀) le g₁ g₂ e₁ e₂
  where
  rep-eq : T ≡ T′
  rep-eq with trans (sym eq) eq′
  rep-eq | refl = refl
ground-readings-unique ρ zero na (I.alias eq p₀)
    (I.alias eq′ q₀) () g₁ g₂ e₁ e₂
