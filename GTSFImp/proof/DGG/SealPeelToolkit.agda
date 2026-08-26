module proof.DGG.SealPeelToolkit where

-- File Charter:
--   * Provides type and world views used by the bare-seal case of seal
--     peeling in the right-injection inversion.
--   * Inverts right-variable obligations and source-variable consistency.
--   * Relates non-variable store entries to their canonical representations.
--   * Decides target alignment and constructs fully dynamized worlds.
--   * Depends on CastTermImprecision2's worlds and resolution functions and
--     on WorldDecay's environment-decay relation.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; subst; sym)
open import Relation.Nullary using (Dec; yes; no)

open import Types
open import TyStore using
  (TyStore; _∋_⦂_; Z∋; S-lift∋; S-bind∋)
open import Consistency using
  (Env∼; _⊢_∼_; _↪ᵗ_; empty; keep; skip; toRenameᵗ; id; _!; gen_)
open import Imprecision
import proof.DGG.CtxImp as CTI2
open CTI2 using
  (World;
   world;
   _⊑ᵂ⟨_⟩_;
   ηᴸʷ;
   ηᴿʷ;
   impEnvʷ;
   sourceStoreʷ;
   targetStoreʷ;
   resolveVar;
   resolveRep)
import proof.DGG.WorldDecay as WD

------------------------------------------------------------------------
-- Right-variable obligations
------------------------------------------------------------------------

private
  imprecision-variable-nonvar-occurs⊥ : ∀ {Δ} {μ : ImpEnv Δ}
      {A : Ty Δ} {X Y : TyVar Δ}
    → μ ⊢ A ⊑ ＇ X
    → NonVar A
    → Y ∈ᵗ A
    → ⊥
  imprecision-variable-nonvar-occurs⊥ X⊑X () var-∈
  imprecision-variable-nonvar-occurs⊥
      (∀⊑ Anv zero∈A A⊑X) nonvar-all (∈-all Y∈A) =
    imprecision-variable-nonvar-occurs⊥ A⊑X Anv zero∈A

  -- A derivation into a bare variable either starts at that same
  -- variable or at a variable aliased to a representative that is
  -- itself below the target variable.

  data RightVarView {Δ} (μ : ImpEnv Δ) (X : TyVar Δ)
      (A : Ty Δ) : Set where
    rv-self : A ≡ ＇ X → RightVarView μ X A
    rv-alias : ∀ {Z} {T : Ty Δ}
      → A ≡ ＇ Z
      → μ Z ≡ X⊑ᵗ T
      → μ ⊢ T ⊑ ＇ X
      → RightVarView μ X A

  imprecision-right-variable : ∀ {Δ} {μ : ImpEnv Δ}
      {A : Ty Δ} {X : TyVar Δ}
    → μ ⊢ A ⊑ ＇ X
    → RightVarView μ X A
  imprecision-right-variable X⊑X = rv-self refl
  imprecision-right-variable (∀⊑ Anv zero∈A A⊑X) =
    ⊥-elim (imprecision-variable-nonvar-occurs⊥ A⊑X Anv zero∈A)
  imprecision-right-variable (alias eq p) =
    rv-alias refl eq p

  ty-var-injective : ∀ {Δ} {X Y : TyVar Δ}
    → _≡_ {A = Ty Δ} (＇ X) (＇ Y)
    → X ≡ Y
  ty-var-injective {X = X} {.X} refl = refl

-- The world-level view of a store representative below a bare target
-- variable: either the aligned variable, or an aliased source-center
-- variable whose representative is below the target's center image.

data RightVarObligationView {Δᴸ Δᴿ Δ} (W : World Δᴸ Δᴿ Δ)
    (R : Ty Δᴸ) (Y : TyVar Δᴿ) : Set where
  rv-aligned : ∀ X₂
    → R ≡ ＇ X₂
    → toRenameᵗ (ηᴸʷ W) X₂ ≡ toRenameᵗ (ηᴿʷ W) Y
    → RightVarObligationView W R Y
  rv-aliased : ∀ X₂ {T}
    → R ≡ ＇ X₂
    → impEnvʷ W (toRenameᵗ (ηᴸʷ W) X₂) ≡ X⊑ᵗ T
    → impEnvʷ W ⊢ T ⊑ ＇ (toRenameᵗ (ηᴿʷ W) Y)
    → RightVarObligationView W R Y

right-var-obligation-view : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
    {R : Ty Δᴸ} {Y : TyVar Δᴿ}
  → R ⊑ᵂ⟨ W ⟩ (＇ Y)
  → RightVarObligationView W R Y
right-var-obligation-view {R = ＇ X₂} p
    with imprecision-right-variable p
right-var-obligation-view {R = ＇ X₂} p | rv-self eqA =
  rv-aligned X₂ refl (ty-var-injective eqA)
right-var-obligation-view {W = W} {R = ＇ X₂} p
    | rv-alias {T = T} eqA eq q =
  rv-aliased X₂ refl
    (subst (λ V → impEnvʷ W V ≡ X⊑ᵗ T)
      (sym (ty-var-injective eqA)) eq)
    q
right-var-obligation-view {R = ‵ ι} p
    with imprecision-right-variable p
right-var-obligation-view {R = ‵ ι} p | rv-self ()
right-var-obligation-view {R = ‵ ι} p
    | rv-alias () eq q
right-var-obligation-view {R = ★} p
    with imprecision-right-variable p
right-var-obligation-view {R = ★} p | rv-self ()
right-var-obligation-view {R = ★} p
    | rv-alias () eq q
right-var-obligation-view {R = A ⇒ B} p
    with imprecision-right-variable p
right-var-obligation-view {R = A ⇒ B} p | rv-self ()
right-var-obligation-view {R = A ⇒ B} p
    | rv-alias () eq q
right-var-obligation-view {R = `∀ A} p
    with imprecision-right-variable p
right-var-obligation-view {R = `∀ A} p | rv-self ()
right-var-obligation-view {R = `∀ A} p
    | rv-alias () eq q

------------------------------------------------------------------------
-- Resolution of non-variable store entries
------------------------------------------------------------------------

private
  unshift-nonvar : ∀ {Δ} {A : Ty Δ}
    → NonVar (⇑ᵗ A)
    → NonVar A
  unshift-nonvar {A = ＇ X} ()
  unshift-nonvar {A = ‵ ι} nonvar-base = nonvar-base
  unshift-nonvar {A = ★} nonvar-star = nonvar-star
  unshift-nonvar {A = A ⇒ B} nonvar-fun = nonvar-fun
  unshift-nonvar {A = `∀ A} nonvar-all = nonvar-all

  resolveRep-nonvar : ∀ {Δ} (Σ : TyStore Δ) {R : Ty Δ}
    → NonVar R
    → resolveRep Σ R ≡ R
  resolveRep-nonvar Σ nonvar-base = refl
  resolveRep-nonvar Σ nonvar-star = refl
  resolveRep-nonvar Σ nonvar-fun = refl
  resolveRep-nonvar Σ nonvar-all = refl

resolveVar-nonvar : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ}
    {R : Ty Δ}
  → Σ ∋ X ⦂ R
  → NonVar R
  → resolveVar Σ X ≡ R
resolveVar-nonvar (Z∋ {A = A} refl) Rnv =
  cong ⇑ᵗ (resolveRep-nonvar _ (unshift-nonvar Rnv))
resolveVar-nonvar (S-lift∋ X∈ refl) Rnv =
  cong ⇑ᵗ (resolveVar-nonvar X∈ (unshift-nonvar Rnv))
resolveVar-nonvar (S-bind∋ X∈ refl) Rnv =
  cong ⇑ᵗ (resolveVar-nonvar X∈ (unshift-nonvar Rnv))

------------------------------------------------------------------------
-- Alignment at a source center
------------------------------------------------------------------------

private
  fin-suc-injective : ∀ {n} {X Y : Fin n}
    → Fin.suc X ≡ Fin.suc Y
    → X ≡ Y
  fin-suc-injective refl = refl

  alignedᴿ? : ∀ {Δᴿ Δ} (ηᴿ : Δᴿ ↪ᵗ Δ) (Z : TyVar Δ)
    → Dec (Σ[ Zᴿ ∈ TyVar Δᴿ ] toRenameᵗ ηᴿ Zᴿ ≡ Z)
  alignedᴿ? empty Z = no λ { (() , eq) }
  alignedᴿ? (keep ηᴿ) Fin.zero = yes (Fin.zero , refl)
  alignedᴿ? (keep ηᴿ) (Fin.suc Z) with alignedᴿ? ηᴿ Z
  alignedᴿ? (keep ηᴿ) (Fin.suc Z) | yes (Zᴿ , eq) =
    yes (Fin.suc Zᴿ , cong Fin.suc eq)
  alignedᴿ? (keep ηᴿ) (Fin.suc Z) | no unaligned =
    no λ
      { (Fin.zero , ())
      ; (Fin.suc Zᴿ , eq) → unaligned (Zᴿ , fin-suc-injective eq)
      }
  alignedᴿ? (skip ηᴿ) Fin.zero = no λ { (Zᴿ , ()) }
  alignedᴿ? (skip ηᴿ) (Fin.suc Z) with alignedᴿ? ηᴿ Z
  alignedᴿ? (skip ηᴿ) (Fin.suc Z) | yes (Zᴿ , eq) =
    yes (Zᴿ , cong Fin.suc eq)
  alignedᴿ? (skip ηᴿ) (Fin.suc Z) | no unaligned =
    no λ { (Zᴿ , eq) → unaligned (Zᴿ , fin-suc-injective eq) }

alignedAtᴸ? : ∀ {Δᴸ Δᴿ Δ} (W : World Δᴸ Δᴿ Δ)
    (Xᴸ : TyVar Δᴸ)
  → (Σ[ Zᴿ ∈ TyVar Δᴿ ]
       toRenameᵗ (ηᴿʷ W) Zᴿ ≡ toRenameᵗ (ηᴸʷ W) Xᴸ)
    ⊎ (∀ Zᴿ →
       toRenameᵗ (ηᴿʷ W) Zᴿ ≢ toRenameᵗ (ηᴸʷ W) Xᴸ)
alignedAtᴸ? W Xᴸ
    with alignedᴿ? (ηᴿʷ W) (toRenameᵗ (ηᴸʷ W) Xᴸ)
alignedAtᴸ? W Xᴸ | yes aligned = inj₁ aligned
alignedAtᴸ? W Xᴸ | no unaligned =
  inj₂ λ Zᴿ eq → unaligned (Zᴿ , eq)

------------------------------------------------------------------------
-- Fully dynamized worlds
------------------------------------------------------------------------

dynWorld : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → World Δᴸ Δᴿ Δ
dynWorld W =
  world (ηᴸʷ W) (ηᴿʷ W) (λ Z → WD.dynamizeVar (impEnvʷ W Z))
    (sourceStoreʷ W) (targetStoreʷ W)

dynWorld-decay : ∀ {Δᴸ Δᴿ Δ} (W : World Δᴸ Δᴿ Δ)
  → WD.EnvDecay W (dynWorld W)
dynWorld-decay W =
  WD.env-decay refl refl refl refl
    (λ Z eq → cong WD.dynamizeVar eq)
    (CTI2.alias-same
      (λ Z eq → cong WD.dynamizeVar eq)
      dynamize-alias-bwd)
  where
  dynamize-alias-bwd : ∀ Z {T}
    → WD.dynamizeVar (impEnvʷ W Z) ≡ X⊑ᵗ T
    → impEnvʷ W Z ≡ X⊑ᵗ T
  dynamize-alias-bwd Z eq with impEnvʷ W Z
  dynamize-alias-bwd Z () | X⊑X
  dynamize-alias-bwd Z () | X⊑★
  dynamize-alias-bwd Z refl | X⊑ᵗ T = refl

private
  dynamize-not-precise : ∀ {Δ} (v : VarImp Δ)
    → WD.dynamizeVar v ≡ X⊑X
    → ⊥
  dynamize-not-precise X⊑X ()
  dynamize-not-precise X⊑★ ()
  dynamize-not-precise (X⊑ᵗ T) ()

dynWorld-WF : ∀ {Δᴸ Δᴿ Δ} (W : World Δᴸ Δᴿ Δ)
  → CTI2.WFWorld (dynWorld W)
dynWorld-WF W Xᴸ precise =
  ⊥-elim (dynamize-not-precise _ precise)

-- Dynamization stars every non-alias mark; an alias survives, so the
-- mark statement is conditional on the original mode.

dynWorld-mark : ∀ {Δᴸ Δᴿ Δ} (W : World Δᴸ Δᴿ Δ)
    (Z : TyVar Δ)
  → (∀ {T} → impEnvʷ W Z ≡ X⊑ᵗ T → ⊥)
  → impEnvʷ (dynWorld W) Z ≡ X⊑★
dynWorld-mark W Z not-alias with impEnvʷ W Z in w-eq
dynWorld-mark W Z not-alias | X⊑X = refl
dynWorld-mark W Z not-alias | X⊑★ = refl
dynWorld-mark W Z not-alias | X⊑ᵗ T =
  ⊥-elim (not-alias refl)

------------------------------------------------------------------------
-- Consistency at a source variable
------------------------------------------------------------------------

private
  consistency-variable-nonvar-occurs⊥ : ∀ {Δ} {ν : Env∼ Δ}
      {Z Y : TyVar Δ} {R : Ty Δ}
    → ν ⊢ (＇ Z) ∼ R
    → NonVar R
    → Y ∈ᵗ R
    → ⊥
  consistency-variable-nonvar-occurs⊥ (id (＇ Z)) () var-∈
  consistency-variable-nonvar-occurs⊥
      (_! c) nonvar-star ()
  consistency-variable-nonvar-occurs⊥
      (gen_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c R≢★) nonvar-all (∈-all Y∈B) =
    consistency-variable-nonvar-occurs⊥ c Bnv zero∈B

var-consistency-view : ∀ {Δ} {ν : Env∼ Δ} {Z : TyVar Δ}
    {R : Ty Δ}
  → ν ⊢ (＇ Z) ∼ R
  → (R ≡ ＇ Z) ⊎ (R ≡ ★)
var-consistency-view (id (＇ Z)) = inj₁ refl
var-consistency-view (_! c) = inj₂ refl
var-consistency-view
    (gen_ ⦃ Bnv ⦄ ⦃ zero∈B ⦄ c R≢★) =
  ⊥-elim (consistency-variable-nonvar-occurs⊥ c Bnv zero∈B)
