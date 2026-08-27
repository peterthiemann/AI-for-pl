module proof.LR-narrow.ConsistencyAvoid where

-- File Charter:
--   * A paired consistency binder cannot be crossed by ★: if a
--     center variable is at the paired consistency mode `X∼X`, then
--     one side of a consistency avoiding it forces the other side to
--     avoid it too.
--   * This is the consistency-side counterpart of
--     `star-no-occurrence` on the imprecision side, and it is what
--     rules out the Finding J configuration
--     (REPLACEMENT-CLOSURE-DESIGN.md): the two readings of an alias
--     variable differ only when the representative's ∀-binder
--     occurs, and a cast that projects at the `∀★` ground forces the
--     projected body to be reachable from ★ under a PAIRED binder,
--     where the bound variable cannot occur at all.
--   * A core-consistency fact with no logical-relation content; it
--     lives here because its consumer is the cast proof.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (suc)
import Data.Fin as Fin
open import Data.Fin.Properties using (_≟_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Types
open import Consistency
import Imprecision as I
import proof.Imprecision as PI
open import proof.ImprecisionConsistency using
  (fin-suc-injective; source-occurs-target)
open import proof.LR-narrow.StarNoOccurrence using
  (renameᵗ-∉ᵗ; renameᵗ-reflects-∉ᵗ)

------------------------------------------------------------------------
-- A paired variable is not one of ★'s ground partners
------------------------------------------------------------------------

star-to-ground-avoids : ∀ {Δ} {ν : Env∼ Δ} {Z : TyVar Δ} {G : Ty Δ}
  → ν Z ≡ X∼X → ν ⊢★∼ G → Z ∉ᵗ G
star-to-ground-avoids eq ★∼⇒ = ∉-fun ∉-star ∉-star
star-to-ground-avoids eq ★∼ι = ∉-base
star-to-ground-avoids {Z = Z} eq (★∼Xᵍ {X = Y} eq′) with Z ≟ Y
star-to-ground-avoids {Z = Z} eq (★∼Xᵍ {X = Y} eq′) | yes refl
    with trans (sym eq) eq′
star-to-ground-avoids {Z = Z} eq (★∼Xᵍ {X = Y} eq′) | yes refl | ()
star-to-ground-avoids {Z = Z} eq (★∼Xᵍ {X = Y} eq′) | no Z≢Y =
  ∉-var (≢→≢ᶠ Z≢Y)
star-to-ground-avoids {Z = Z} eq (★∼Xᶜ {X = Y} eq′) with Z ≟ Y
star-to-ground-avoids {Z = Z} eq (★∼Xᶜ {X = Y} eq′) | yes refl
    with trans (sym eq) eq′
star-to-ground-avoids {Z = Z} eq (★∼Xᶜ {X = Y} eq′) | yes refl | ()
star-to-ground-avoids {Z = Z} eq (★∼Xᶜ {X = Y} eq′) | no Z≢Y =
  ∉-var (≢→≢ᶠ Z≢Y)
star-to-ground-avoids eq ★∼∀ = ∉-all ∉-star

ground-to-star-avoids : ∀ {Δ} {ν : Env∼ Δ} {Z : TyVar Δ} {G : Ty Δ}
  → ν Z ≡ X∼X → ν ⊢ G ∼★ → Z ∉ᵗ G
ground-to-star-avoids eq ⇒∼★ = ∉-fun ∉-star ∉-star
ground-to-star-avoids eq ι∼★ = ∉-base
ground-to-star-avoids {Z = Z} eq (X∼★ᵍ {X = Y} eq′) with Z ≟ Y
ground-to-star-avoids {Z = Z} eq (X∼★ᵍ {X = Y} eq′) | yes refl
    with trans (sym eq) eq′
ground-to-star-avoids {Z = Z} eq (X∼★ᵍ {X = Y} eq′) | yes refl | ()
ground-to-star-avoids {Z = Z} eq (X∼★ᵍ {X = Y} eq′) | no Z≢Y =
  ∉-var (≢→≢ᶠ Z≢Y)
ground-to-star-avoids {Z = Z} eq (X∼★ᶜ {X = Y} eq′) with Z ≟ Y
ground-to-star-avoids {Z = Z} eq (X∼★ᶜ {X = Y} eq′) | yes refl
    with trans (sym eq) eq′
ground-to-star-avoids {Z = Z} eq (X∼★ᶜ {X = Y} eq′) | yes refl | ()
ground-to-star-avoids {Z = Z} eq (X∼★ᶜ {X = Y} eq′) | no Z≢Y =
  ∉-var (≢→≢ᶠ Z≢Y)
ground-to-star-avoids eq ∀∼★ = ∉-all ∉-star

------------------------------------------------------------------------
-- Avoidance of a paired variable travels across a consistency
------------------------------------------------------------------------

mutual
  avoid-target : ∀ {Δ} {ν : Env∼ Δ} {Z : TyVar Δ} {A B : Ty Δ}
    → ν Z ≡ X∼X → Z ∉ᵗ A → ν ⊢ A ∼ B → Z ∉ᵗ B
  avoid-target eq no-occur (id a) = no-occur
  avoid-target eq (∉-fun nA nB) (c₁ ↦ c₂) =
    ∉-fun (avoid-source (cong flipVar∼ eq) nA c₁)
      (avoid-target eq nB c₂)
  avoid-target eq (∉-all n) (∀ᶜ c) =
    ∉-all (avoid-target eq n c)
  avoid-target eq no-occur (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Ans ⦄) = ∉-star
  avoid-target eq no-occur (？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) =
    avoid-target eq (star-to-ground-avoids eq ★∼G) c
  avoid-target {B = B₀} eq (∉-all n) ((inst_ c) ne) =
    renameᵗ-reflects-∉ᵗ Fin.suc B₀ (avoid-target eq n c)
  avoid-target eq no-occur ((gen_ c) ne) =
    ∉-all (avoid-target eq
      (renameᵗ-∉ᵗ Fin.suc fin-suc-injective no-occur) c)
  avoid-target eq no-occur bot-elim = ∉-all ∉-star
  avoid-target eq no-occur bot-intro =
    ∉-all (∉-var (≢→≢ᶠ (λ ())))

  avoid-source : ∀ {Δ} {ν : Env∼ Δ} {Z : TyVar Δ} {A B : Ty Δ}
    → ν Z ≡ X∼X → Z ∉ᵗ B → ν ⊢ A ∼ B → Z ∉ᵗ A
  avoid-source eq no-occur (id a) = no-occur
  avoid-source eq (∉-fun nA′ nB′) (c₁ ↦ c₂) =
    ∉-fun (avoid-target (cong flipVar∼ eq) nA′ c₁)
      (avoid-source eq nB′ c₂)
  avoid-source eq (∉-all n) (∀ᶜ c) =
    ∉-all (avoid-source eq n c)
  avoid-source eq no-occur (_! ⦃ Gᵍ ⦄ ⦃ G∼★ ⦄ c ⦃ Ans ⦄) =
    avoid-source eq (ground-to-star-avoids eq G∼★) c
  avoid-source eq no-occur (？_ ⦃ Gᵍ ⦄ ⦃ ★∼G ⦄ c ⦃ Bns ⦄) = ∉-star
  avoid-source eq no-occur ((inst_ c) ne) =
    ∉-all (avoid-source eq
      (renameᵗ-∉ᵗ Fin.suc fin-suc-injective no-occur) c)
  avoid-source {A = A₀} eq (∉-all n) ((gen_ c) ne) =
    renameᵗ-reflects-∉ᵗ Fin.suc A₀ (avoid-source eq n c)
  avoid-source eq no-occur bot-elim =
    ∉-all (∉-var (≢→≢ᶠ (λ ())))
  avoid-source eq no-occur bot-intro = ∉-all ∉-star

------------------------------------------------------------------------
-- The Finding J fork is dead at a `∀★` projection
------------------------------------------------------------------------

-- The two readings of an alias variable diverge only when the
-- representative's binder OCCURS in its body: that is what lets the
-- `∀⊑` route reach a fun ground while `∀⊑∀` keeps the ∀ shape.  A
-- cast that projects at the `∀★` ground and lands on a `∀` type
-- relates the two bodies under a PAIRED consistency binder, where
-- the bound variable cannot occur; the `∀⊑∀` route transports the
-- occurrence into that body.  The two are incompatible, so the
-- configuration never arises.

paired-fork-excluded : ∀ {Δ} {μ : I.ImpEnv Δ}
    {ν : Env∼ (suc Δ)} {A₀ D₀ : Ty (suc Δ)}
  → ν Fin.zero ≡ X∼X
  → Fin.zero ∈ᵗ A₀
  → I.extᵐ μ I.⊢ A₀ ⊑ D₀
  → ν ⊢ ★ ∼ D₀
  → ⊥
paired-fork-excluded eq occurs q₀ c =
  PI.∈∉-⊥ (avoid-target eq ∉-star c)
    (source-occurs-target refl q₀ occurs)
