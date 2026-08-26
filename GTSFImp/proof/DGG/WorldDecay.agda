module proof.DGG.WorldDecay where

-- File Charter:
--   * Defines monotonic decay of local-world imprecision marks toward X⊑★.
--   * Transports type and context imprecision obligations across decay.
--   * Blends premise worlds with decayed conclusion-world marks.
--   * Honestifies worlds by dynamizing centers without a target alignment.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
import Data.Fin as Fin
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
open import Relation.Nullary using (Dec; yes; no)

open import Types
open import Consistency using (_↪ᵗ_; empty; keep; skip; toRenameᵗ)
open import Imprecision
import proof.DGG.CtxImp as CTI2
open import proof.ImprecisionConsistency using (imp-env-weaken)
open CTI2 using
  (World;
   _⊑ᵂ⟨_⟩_;
   CtxImp;
   ctx-imp;
   _∋ʷ_⦂_;
   Zʷ;
   Sʷ;
   SameCtx;
   same-[];
   same-∷)

------------------------------------------------------------------------
-- Type-level environment monotonicity
------------------------------------------------------------------------

⊑-env-mono : ∀ {Δ} {μ μᵈ : ImpEnv Δ} {A B : Ty Δ}
  → (∀ Z → μ Z ≡ X⊑★ → μᵈ Z ≡ X⊑★)
  → (∀ Z {T} → μ Z ≡ X⊑ᵗ T → μᵈ Z ≡ X⊑ᵗ T)
  → μ ⊢ A ⊑ B
  → μᵈ ⊢ A ⊑ B
⊑-env-mono = imp-env-weaken

record EnvDecay {Δᴸ Δᴿ Δ} (W Wᵈ : World Δᴸ Δᴿ Δ) : Set where
  constructor env-decay
  field
    ηᴸ-same : CTI2.ηᴸʷ Wᵈ ≡ CTI2.ηᴸʷ W
    ηᴿ-same : CTI2.ηᴿʷ Wᵈ ≡ CTI2.ηᴿʷ W
    sourceStore-same :
      CTI2.sourceStoreʷ Wᵈ ≡ CTI2.sourceStoreʷ W
    targetStore-same :
      CTI2.targetStoreʷ Wᵈ ≡ CTI2.targetStoreʷ W
    env-mono : ∀ Z
      → CTI2.impEnvʷ W Z ≡ X⊑★
      → CTI2.impEnvʷ Wᵈ Z ≡ X⊑★
    env-alias : CTI2.AliasSame (CTI2.impEnvʷ W)
      (CTI2.impEnvʷ Wᵈ)

open EnvDecay public

decay⊑ᵂ : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : World Δᴸ Δᴿ Δ}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → EnvDecay W Wᵈ
  → A ⊑ᵂ⟨ W ⟩ B
  → A ⊑ᵂ⟨ Wᵈ ⟩ B
decay⊑ᵂ
    {W = CTI2.world ηL ηR μ ΣL ΣR}
    {Wᵈ = CTI2.world ηL′ ηR′ μᵈ ΣL′ ΣR′}
    (env-decay refl refl refl refl mono al) p =
  ⊑-env-mono mono (CTI2.alias-fwd al) p

decay-refl : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → EnvDecay W W
decay-refl =
  env-decay refl refl refl refl (λ Z eq → eq)
    CTI2.alias-same-refl

------------------------------------------------------------------------
-- Context decay
------------------------------------------------------------------------

decayCtx : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : World Δᴸ Δᴿ Δ}
  → (dec : EnvDecay W Wᵈ)
  → CtxImp W
  → CtxImp Wᵈ
decayCtx dec [] = []
decayCtx dec (ctx-imp A B p ∷ γ) =
  ctx-imp A B (decay⊑ᵂ dec p) ∷ decayCtx dec γ

decay∋ʷ : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : World Δᴸ Δᴿ Δ}
    {γ : CtxImp W} {x A B} {p : A ⊑ᵂ⟨ W ⟩ B}
  → (dec : EnvDecay W Wᵈ)
  → γ ∋ʷ x ⦂ ctx-imp A B p
  → decayCtx dec γ ∋ʷ x ⦂ ctx-imp A B (decay⊑ᵂ dec p)
decay∋ʷ dec Zʷ = Zʷ
decay∋ʷ dec (Sʷ x∈) = Sʷ (decay∋ʷ dec x∈)

decaySameCtx : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W Wᵈ : World Δᴸ Δᴿ Δ}
    {W′ W′ᵈ : World Δᴸ Δᴿ Δ′}
    {γ : CtxImp W} {γ′ : CtxImp W′}
  → (dec : EnvDecay W Wᵈ)
  → (dec′ : EnvDecay W′ W′ᵈ)
  → SameCtx γ γ′
  → SameCtx (decayCtx dec γ) (decayCtx dec′ γ′)
decaySameCtx dec dec′ same-[] = same-[]
decaySameCtx dec dec′ (same-∷ same) =
  same-∷ (decaySameCtx dec dec′ same)

------------------------------------------------------------------------
-- Blending premise-world marks with a decayed conclusion world
------------------------------------------------------------------------

blendVar : ∀ {Δ} → VarImp Δ → VarImp Δ → VarImp Δ
blendVar X⊑★ v = X⊑★
blendVar X⊑X v = v
blendVar (X⊑ᵗ T) v = X⊑ᵗ T

blendWorld : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → World Δᴸ Δᴿ Δ
  → World Δᴸ Δᴿ Δ
blendWorld W′ Wᵈ =
  CTI2.world (CTI2.ηᴸʷ W′) (CTI2.ηᴿʷ W′)
    (λ Z → blendVar (CTI2.impEnvʷ W′ Z) (CTI2.impEnvʷ Wᵈ Z))
    (CTI2.sourceStoreʷ W′) (CTI2.targetStoreʷ W′)

private
  blend-left-mono : ∀ {Δ} {v vᵈ : VarImp Δ}
    → v ≡ X⊑★
    → blendVar v vᵈ ≡ X⊑★
  blend-left-mono refl = refl

  blend-left-alias : ∀ {Δ} {v vᵈ : VarImp Δ} {T}
    → v ≡ X⊑ᵗ T
    → blendVar v vᵈ ≡ X⊑ᵗ T
  blend-left-alias refl = refl

  blend-alias-reflect : ∀ {Δᴸ Δᴿ Δ}
      {W′ Wᵈ : World Δᴸ Δᴿ Δ}
    → CTI2.AliasSame (CTI2.impEnvʷ W′) (CTI2.impEnvʷ Wᵈ)
    → ∀ Z {T}
    → CTI2.impEnvʷ (blendWorld W′ Wᵈ) Z ≡ X⊑ᵗ T
    → CTI2.impEnvʷ W′ Z ≡ X⊑ᵗ T
  blend-alias-reflect {W′ = W′} {Wᵈ = Wᵈ} agree Z eq
      with CTI2.impEnvʷ W′ Z in w′-eq
  blend-alias-reflect agree Z () | X⊑★
  blend-alias-reflect {W′ = W′} {Wᵈ = Wᵈ} agree Z eq | X⊑X
      with trans (sym w′-eq) (CTI2.alias-bwd agree Z eq)
  blend-alias-reflect agree Z eq | X⊑X | ()
  blend-alias-reflect agree Z refl | X⊑ᵗ T = refl

-- Blending is a decay of the premise world only when the premise and
-- decayed worlds assign the same aliases; the hypothesis is the
-- composition of the wrapper rule's alias agreement with the decay's.

blend-decay : ∀ {Δᴸ Δᴿ Δ}
    {W′ Wᵈ : World Δᴸ Δᴿ Δ}
  → CTI2.AliasSame (CTI2.impEnvʷ W′) (CTI2.impEnvʷ Wᵈ)
  → EnvDecay W′ (blendWorld W′ Wᵈ)
blend-decay {W′ = W′} {Wᵈ = Wᵈ} agree =
  env-decay refl refl refl refl
    (λ Z eq → blend-left-mono eq)
    (CTI2.alias-same (λ Z eq → blend-left-alias eq)
      (blend-alias-reflect {W′ = W′} {Wᵈ = Wᵈ} agree))

-- Blending keeps the decayed world's dynamic marks and the premise
-- world's aliases.  The first hypothesis says the premise world's
-- aliases are already aliases of the decayed world; at the use site it
-- is the composition of the wrapper rule's alias agreement with the
-- decay's alias preservation.

blend-mono : ∀ {Δᴸ Δᴿ Δ}
    {W′ Wᵈ : World Δᴸ Δᴿ Δ}
  → CTI2.AliasSame (CTI2.impEnvʷ W′) (CTI2.impEnvʷ Wᵈ)
  → CTI2.ImpEnvMono Wᵈ (blendWorld W′ Wᵈ)
blend-mono {W′ = W′} {Wᵈ = Wᵈ} agree =
  CTI2.imp-env-mono star
    (CTI2.alias-same alias-fwdʹ alias-bwdʹ)
  where
  star : ∀ Z
    → CTI2.impEnvʷ Wᵈ Z ≡ X⊑★
    → CTI2.impEnvʷ (blendWorld W′ Wᵈ) Z ≡ X⊑★
  star Z eq with CTI2.impEnvʷ W′ Z in w′-eq
  star Z eq | X⊑★ = refl
  star Z eq | X⊑X = eq
  star Z eq | X⊑ᵗ T
      with trans (sym eq) (CTI2.alias-fwd agree Z w′-eq)
  star Z eq | X⊑ᵗ T | ()
  alias-fwdʹ : ∀ Z {T}
    → CTI2.impEnvʷ Wᵈ Z ≡ X⊑ᵗ T
    → CTI2.impEnvʷ (blendWorld W′ Wᵈ) Z ≡ X⊑ᵗ T
  alias-fwdʹ Z eq with CTI2.impEnvʷ W′ Z in w′-eq
  alias-fwdʹ Z eq | X⊑X = eq
  alias-fwdʹ Z eq | X⊑★
      with trans (sym (CTI2.alias-bwd agree Z eq)) w′-eq
  alias-fwdʹ Z eq | X⊑★ | ()
  alias-fwdʹ Z eq | X⊑ᵗ T′
      with trans (sym (CTI2.alias-fwd agree Z w′-eq)) eq
  alias-fwdʹ Z eq | X⊑ᵗ T′ | refl = refl
  alias-bwdʹ : ∀ Z {T}
    → CTI2.impEnvʷ (blendWorld W′ Wᵈ) Z ≡ X⊑ᵗ T
    → CTI2.impEnvʷ Wᵈ Z ≡ X⊑ᵗ T
  alias-bwdʹ Z eq with CTI2.impEnvʷ W′ Z in w′-eq
  alias-bwdʹ Z () | X⊑★
  alias-bwdʹ Z eq | X⊑X = eq
  alias-bwdʹ Z refl | X⊑ᵗ T =
    CTI2.alias-fwd agree Z w′-eq

------------------------------------------------------------------------
-- Honest worlds
------------------------------------------------------------------------

private
  fin-suc-injective : ∀ {n} {X Y : Fin n}
    → Fin.suc X ≡ Fin.suc Y
    → X ≡ Y
  fin-suc-injective refl = refl

alignedᴿ? : ∀ {Δᴿ Δ} (ηᴿ : Δᴿ ↪ᵗ Δ) (Z : TyVar Δ)
  → Dec (Σ[ Xᴿ ∈ TyVar Δᴿ ] toRenameᵗ ηᴿ Xᴿ ≡ Z)
alignedᴿ? empty Z = no λ { (() , eq) }
alignedᴿ? (keep ηᴿ) Fin.zero = yes (Fin.zero , refl)
alignedᴿ? (keep ηᴿ) (Fin.suc Z) with alignedᴿ? ηᴿ Z
alignedᴿ? (keep ηᴿ) (Fin.suc Z) | yes (Xᴿ , eq) =
  yes (Fin.suc Xᴿ , cong Fin.suc eq)
alignedᴿ? (keep ηᴿ) (Fin.suc Z) | no unaligned =
  no λ
    { (Fin.zero , ())
    ; (Fin.suc Xᴿ , eq) → unaligned (Xᴿ , fin-suc-injective eq)
    }
alignedᴿ? (skip ηᴿ) Fin.zero = no λ { (Xᴿ , ()) }
alignedᴿ? (skip ηᴿ) (Fin.suc Z) with alignedᴿ? ηᴿ Z
alignedᴿ? (skip ηᴿ) (Fin.suc Z) | yes (Xᴿ , eq) =
  yes (Xᴿ , cong Fin.suc eq)
alignedᴿ? (skip ηᴿ) (Fin.suc Z) | no unaligned =
  no λ { (Xᴿ , eq) → unaligned (Xᴿ , fin-suc-injective eq) }

-- Honestification forgets stale precise marks; aliases are not marks
-- and survive it unchanged.

dynamizeVar : ∀ {Δ} → VarImp Δ → VarImp Δ
dynamizeVar X⊑X = X⊑★
dynamizeVar X⊑★ = X⊑★
dynamizeVar (X⊑ᵗ T) = X⊑ᵗ T

honestEnv : ∀ {Δᴿ Δ} → (Δᴿ ↪ᵗ Δ) → ImpEnv Δ → ImpEnv Δ
honestEnv ηᴿ μ Z with alignedᴿ? ηᴿ Z
honestEnv ηᴿ μ Z | yes aligned = μ Z
honestEnv ηᴿ μ Z | no unaligned = dynamizeVar (μ Z)

honestify : ∀ {Δᴸ Δᴿ Δ}
  → World Δᴸ Δᴿ Δ
  → World Δᴸ Δᴿ Δ
honestify W =
  CTI2.world (CTI2.ηᴸʷ W) (CTI2.ηᴿʷ W)
    (honestEnv (CTI2.ηᴿʷ W) (CTI2.impEnvʷ W))
    (CTI2.sourceStoreʷ W) (CTI2.targetStoreʷ W)

private
  honestEnv-mono : ∀ {Δᴿ Δ} (ηᴿ : Δᴿ ↪ᵗ Δ)
      (μ : ImpEnv Δ) (Z : TyVar Δ)
    → μ Z ≡ X⊑★
    → honestEnv ηᴿ μ Z ≡ X⊑★
  honestEnv-mono ηᴿ μ Z eq with alignedᴿ? ηᴿ Z
  honestEnv-mono ηᴿ μ Z eq | yes aligned = eq
  honestEnv-mono ηᴿ μ Z eq | no unaligned rewrite eq = refl

  honestEnv-alias : ∀ {Δᴿ Δ} (ηᴿ : Δᴿ ↪ᵗ Δ)
      (μ : ImpEnv Δ) (Z : TyVar Δ) {T : Ty Δ}
    → μ Z ≡ X⊑ᵗ T
    → honestEnv ηᴿ μ Z ≡ X⊑ᵗ T
  honestEnv-alias ηᴿ μ Z eq with alignedᴿ? ηᴿ Z
  honestEnv-alias ηᴿ μ Z eq | yes aligned = eq
  honestEnv-alias ηᴿ μ Z eq | no unaligned rewrite eq = refl

  honestEnv-alias-bwd : ∀ {Δᴿ Δ} (ηᴿ : Δᴿ ↪ᵗ Δ)
      (μ : ImpEnv Δ) (Z : TyVar Δ) {T : Ty Δ}
    → honestEnv ηᴿ μ Z ≡ X⊑ᵗ T
    → μ Z ≡ X⊑ᵗ T
  honestEnv-alias-bwd ηᴿ μ Z eq with alignedᴿ? ηᴿ Z
  honestEnv-alias-bwd ηᴿ μ Z eq | yes aligned = eq
  honestEnv-alias-bwd ηᴿ μ Z eq | no unaligned
      with μ Z in μ-eq
  honestEnv-alias-bwd ηᴿ μ Z () | no unaligned | X⊑X
  honestEnv-alias-bwd ηᴿ μ Z () | no unaligned | X⊑★
  honestEnv-alias-bwd ηᴿ μ Z refl | no unaligned | X⊑ᵗ T =
    refl

honestify-decay : ∀ {Δᴸ Δᴿ Δ} {W : World Δᴸ Δᴿ Δ}
  → EnvDecay W (honestify W)
honestify-decay {W = W} =
  env-decay refl refl refl refl
    (honestEnv-mono (CTI2.ηᴿʷ W) (CTI2.impEnvʷ W))
    (CTI2.alias-same
      (honestEnv-alias (CTI2.ηᴿʷ W) (CTI2.impEnvʷ W))
      (honestEnv-alias-bwd (CTI2.ηᴿʷ W) (CTI2.impEnvʷ W)))

honestify-WF : ∀ {Δᴸ Δᴿ Δ} (W : World Δᴸ Δᴿ Δ)
  → CTI2.WFWorld (honestify W)
honestify-WF W Xᴸ precise
    with alignedᴿ? (CTI2.ηᴿʷ W)
           (toRenameᵗ (CTI2.ηᴸʷ W) Xᴸ)
honestify-WF W Xᴸ precise | yes (Xᴿ , aligned) = Xᴿ , aligned
honestify-WF W Xᴸ precise | no unaligned =
  ⊥-elim (dynamize-not-precise _ precise)
  where
  dynamize-not-precise : ∀ {Δ} (v : VarImp Δ)
    → dynamizeVar v ≡ X⊑X
    → ⊥
  dynamize-not-precise X⊑X ()
  dynamize-not-precise X⊑★ ()
  dynamize-not-precise (X⊑ᵗ T) ()
