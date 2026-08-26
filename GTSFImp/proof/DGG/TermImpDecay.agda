module proof.DGG.TermImpDecay where

-- File Charter:
--   * Transports version-2 cast-term imprecision across world decay.
--   * Lifts decay through type binders and term-context lifting.
--   * Decays pivot-local rebasing and wrapper-rule premise worlds.
--   * Exports obligation-insensitive transport via proof irrelevance.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
import Data.Fin as Fin
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types
open import Consistency using (keep; skip; toRenameᵗ)
open import Conversion using (Conv↓)
open import CastTerms using (Term; ⟨_,_,_⟩; _⊢_⦂_)
open import Imprecision
import proof.DGG.CastTermImprecision as CTI2
import proof.DGG.CtxImp as CTX
open CTI2 using (_∣_⊢²_⊑_∶_)
import proof.DGG.SealPeelToolkit as SPT
open import proof.DGG.WorldDecay
import proof.Imprecision as PI
import proof.ImprecisionConsistency as PIC
open import proof.ImprecisionConsistency using (subst-⊑)

------------------------------------------------------------------------
-- Decay under type binders
------------------------------------------------------------------------

liftDecayBoth : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
  → (v : VarImp (suc Δ))
  → EnvDecay W Wᵈ
  → EnvDecay (CTX.liftWorldBoth v W) (CTX.liftWorldBoth v Wᵈ)
liftDecayBoth
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′}
    v
    (env-decay refl refl refl refl mono al) =
  env-decay refl refl refl refl lift-mono
    (CTX.alias-same-ext al)
  where
  lift-mono : ∀ Z
    → extendᵐ v μ Z ≡ X⊑★
    → extendᵐ v μᵈ Z ≡ X⊑★
  lift-mono Fin.zero eq = eq
  lift-mono (Fin.suc Z) eq =
    cong ⇑ᵛ (mono Z (lift-star-inv eq))

liftBothBinderDecay : ∀ {Δᴸ Δᴿ Δ} {W : CTX.World Δᴸ Δᴿ Δ}
  → EnvDecay
      (CTX.liftWorldBoth X⊑X W)
      (CTX.liftWorldBoth X⊑★ W)
liftBothBinderDecay =
  env-decay refl refl refl refl lift-mono
    (CTX.alias-same lift-alias lift-alias-bwd)
  where
  lift-mono : ∀ {Δ} {μ : ImpEnv Δ}
    → (Z : Fin.Fin (suc Δ))
    → extendᵐ X⊑X μ Z ≡ X⊑★
    → extendᵐ X⊑★ μ Z ≡ X⊑★
  lift-mono Fin.zero eq = refl
  lift-mono (Fin.suc Z) eq = eq
  lift-alias : ∀ {Δ} {μ : ImpEnv Δ}
    → (Z : Fin.Fin (suc Δ)) {T : Ty (suc Δ)}
    → extendᵐ X⊑X μ Z ≡ X⊑ᵗ T
    → extendᵐ X⊑★ μ Z ≡ X⊑ᵗ T
  lift-alias Fin.zero ()
  lift-alias (Fin.suc Z) eq = eq
  lift-alias-bwd : ∀ {Δ} {μ : ImpEnv Δ}
    → (Z : Fin.Fin (suc Δ)) {T : Ty (suc Δ)}
    → extendᵐ X⊑★ μ Z ≡ X⊑ᵗ T
    → extendᵐ X⊑X μ Z ≡ X⊑ᵗ T
  lift-alias-bwd Fin.zero ()
  lift-alias-bwd (Fin.suc Z) eq = eq

liftDecayLeft : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
  → (v : VarImp (suc Δ))
  → EnvDecay W Wᵈ
  → EnvDecay (CTX.liftWorldLeft v W) (CTX.liftWorldLeft v Wᵈ)
liftDecayLeft
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′}
    v
    (env-decay refl refl refl refl mono al) =
  env-decay refl refl refl refl lift-mono
    (CTX.alias-same-ext al)
  where
  lift-mono : ∀ Z
    → extendᵐ v μ Z ≡ X⊑★
    → extendᵐ v μᵈ Z ≡ X⊑★
  lift-mono Fin.zero eq = eq
  lift-mono (Fin.suc Z) eq =
    cong ⇑ᵛ (mono Z (lift-star-inv eq))

decayLiftCtx : ∀ {Δᴸ Δᴿ Δ} {v} {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W}
    {γ′ : CTX.CtxImp (CTX.liftWorldBoth v W)}
  → (dec : EnvDecay W Wᵈ)
  → CTX.LiftCtx v γ γ′
  → CTX.LiftCtx v (decayCtx dec γ)
      (decayCtx (liftDecayBoth v dec) γ′)
decayLiftCtx dec CTX.lift-[] = CTX.lift-[]
decayLiftCtx dec (CTX.lift-∷ liftγ) =
  CTX.lift-∷ (decayLiftCtx dec liftγ)

decayLiftCtxᴸ : ∀ {Δᴸ Δᴿ Δ} {v} {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W}
    {γ′ : CTX.CtxImp (CTX.liftWorldLeft v W)}
  → (dec : EnvDecay W Wᵈ)
  → CTX.LiftCtxᴸ v γ γ′
  → CTX.LiftCtxᴸ v (decayCtx dec γ)
      (decayCtx (liftDecayLeft v dec) γ′)
decayLiftCtxᴸ dec CTX.liftᴸ-[] = CTX.liftᴸ-[]
decayLiftCtxᴸ dec (CTX.liftᴸ-∷ liftγ) =
  CTX.liftᴸ-∷ (decayLiftCtxᴸ dec liftγ)

decaySmartLiftCtxᴸ : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {Wᵐ Wᵐᵈ : CTX.World (suc Δᴸ) Δᴿ Δᵐ}
    {γ : CTX.CtxImp W} {γᵐ : CTX.CtxImp Wᵐ}
  → (dec : EnvDecay W Wᵈ)
  → (decᵐ : EnvDecay Wᵐ Wᵐᵈ)
  → CTX.SmartLiftCtxᴸ γ γᵐ
  → CTX.SmartLiftCtxᴸ (decayCtx dec γ) (decayCtx decᵐ γᵐ)
decaySmartLiftCtxᴸ dec decᵐ CTX.smart-lift-[] = CTX.smart-lift-[]
decaySmartLiftCtxᴸ dec decᵐ (CTX.smart-lift-∷ liftγ) =
  CTX.smart-lift-∷ (decaySmartLiftCtxᴸ dec decᵐ liftγ)

rename-as-subst : ∀ {Δ Δ′}
  → (ρ : Δ ⇒ʳ Δ′)
  → (A : Ty Δ)
  → substᵗ (λ X → ＇ ρ X) A ≡ renameᵗ ρ A
rename-as-subst ρ (＇ X) = refl
rename-as-subst ρ (‵ ι) = refl
rename-as-subst ρ ★ = refl
rename-as-subst ρ (A ⇒ B)
    rewrite rename-as-subst ρ A | rename-as-subst ρ B =
  refl
rename-as-subst ρ (`∀ A) =
  cong `∀
    (trans (substᵗ-cong A exts-eq)
      (rename-as-subst (extᵗ ρ) A))
  where
  exts-eq : ∀ X
    → extsᵗ (λ Y → ＇ ρ Y) X ≡ ＇ extᵗ ρ X
  exts-eq Fin.zero = refl
  exts-eq (Fin.suc X) = refl

transport⊑ᵂ-by-subst : ∀ {Δᴸ Δᴿ Δ Δ′}
    {W : CTX.World Δᴸ Δᴿ Δ}
    {W′ : CTX.World Δᴸ Δᴿ Δ′}
    {A : Ty Δᴸ} {B : Ty Δᴿ}
  → (σ : Δ ⇒ˢ Δ′)
  → (∀ Z → CTX.impEnvʷ W Z ≡ X⊑★
      → CTX.impEnvʷ W′ ⊢ σ Z ⊑ ★)
  → PIC.SubstAliasMap (CTX.impEnvʷ W) (CTX.impEnvʷ W′) σ
  → (∀ C → substᵗ σ (CTX.embedᴸ W C) ≡ CTX.embedᴸ W′ C)
  → (∀ C → substᵗ σ (CTX.embedᴿ W C) ≡ CTX.embedᴿ W′ C)
  → A CTX.⊑ᵂ⟨ W ⟩ B
  → A CTX.⊑ᵂ⟨ W′ ⟩ B
transport⊑ᵂ-by-subst {W = W} {W′ = W′} {A = A} {B = B}
    σ star-map alias-map source-eq target-eq p =
  subst≡
    (λ L → CTX.impEnvʷ W′ ⊢ L ⊑ CTX.embedᴿ W′ B)
    (source-eq A)
    (subst≡
      (λ R → CTX.impEnvʷ W′ ⊢ substᵗ σ (CTX.embedᴸ W A) ⊑ R)
      (target-eq B)
      (subst-⊑ star-map alias-map p))

decaySmartFreshBehindGuard : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTX.World (suc Δᴸ) Δᴿ Δᵐ}
  → (dec : EnvDecay W Wᵈ)
  → CTX.SmartFreshBehindGuard W Wᵐ
  → CTX.SmartFreshBehindGuard Wᵈ (SPT.dynWorld Wᵐ)
decaySmartFreshBehindGuard
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {Δ = Δ} {Δᵐ = Δᵐ}
    {W = W} {Wᵈ = Wᵈ} {Wᵐ = Wᵐ}
    (env-decay refl refl refl refl mono al) guard =
  CTX.smart-fresh-behind-guard
    (CTX.SmartFreshBehindGuard.oldCenters guard)
    (CTX.SmartFreshBehindGuard.sourceStore-lifted guard)
    (CTX.SmartFreshBehindGuard.targetStore-same guard)
    transport′
    old-mark-mono′
    (CTX.SmartFreshBehindGuard.target-frozen guard)
    (CTX.SmartFreshBehindGuard.old-source-frozen guard)
    (CTX.SmartFreshBehindGuard.fresh-not-target guard)
    (cong dynamizeVar
      (CTX.SmartFreshBehindGuard.fresh-mark-dynamic guard))
    target-mark-mono′
    old-alias-frozen′
    old-alias-reflect′
    fresh-no-alias′
  where
  old = CTX.SmartFreshBehindGuard.oldCenters guard

  -- The decayed marks: a variable whose center image carries an alias
  -- in the merge world reflects to an alias of the original world and
  -- then, by decay, of the decayed world -- contradicting a dynamic
  -- mark.  Every other mode dynamizes to a dynamic mark.

  old-not-alias : ∀ Z {T}
    → CTX.impEnvʷ Wᵈ Z ≡ X⊑★
    → CTX.impEnvʷ Wᵐ (toRenameᵗ old Z) ≡ X⊑ᵗ T
    → ⊥
  old-not-alias Z star al-eq
      with CTX.SmartFreshBehindGuard.old-alias-reflect
             guard Z al-eq
  old-not-alias Z star al-eq | T₀ , w-eq , refl
      with trans (sym (CTX.alias-fwd al Z w-eq)) star
  old-not-alias Z star al-eq | T₀ , w-eq , refl | ()

  dynamize-star : ∀ {Δ†} (v : VarImp Δ†)
    → (∀ {T} → v ≡ X⊑ᵗ T → ⊥)
    → dynamizeVar v ≡ X⊑★
  dynamize-star X⊑X not-al = refl
  dynamize-star X⊑★ not-al = refl
  dynamize-star (X⊑ᵗ T) not-al = ⊥-elim (not-al refl)

  old-mark-mono′ : ∀ Z
    → CTX.impEnvʷ Wᵈ Z ≡ X⊑★
    → CTX.impEnvʷ (SPT.dynWorld Wᵐ) (toRenameᵗ old Z) ≡ X⊑★
  old-mark-mono′ Z star =
    dynamize-star (CTX.impEnvʷ Wᵐ (toRenameᵗ old Z))
      (old-not-alias Z star)

  target-mark-mono′ : ∀ Xᴿ
    → CTX.impEnvʷ Wᵈ (toRenameᵗ (CTX.ηᴿʷ Wᵈ) Xᴿ) ≡ X⊑★
    → CTX.impEnvʷ (SPT.dynWorld Wᵐ)
        (toRenameᵗ (CTX.ηᴿʷ (SPT.dynWorld Wᵐ)) Xᴿ) ≡ X⊑★
  target-mark-mono′ Xᴿ star =
    subst≡
      (λ V → dynamizeVar (CTX.impEnvʷ Wᵐ V) ≡ X⊑★)
      (sym (CTX.SmartFreshBehindGuard.target-frozen guard Xᴿ))
      (old-mark-mono′ (toRenameᵗ (CTX.ηᴿʷ W) Xᴿ) star)

  old-alias-frozen′ : ∀ Z {T}
    → CTX.impEnvʷ Wᵈ Z ≡ X⊑ᵗ T
    → CTX.impEnvʷ (SPT.dynWorld Wᵐ) (toRenameᵗ old Z)
      ≡ X⊑ᵗ (renameᵗ (toRenameᵗ old) T)
  old-alias-frozen′ Z eq =
    cong dynamizeVar
      (CTX.SmartFreshBehindGuard.old-alias-frozen guard Z
        (CTX.alias-bwd al Z eq))

  dynamize-alias-bwd : ∀ {Δ†} (v : VarImp Δ†) {T}
    → dynamizeVar v ≡ X⊑ᵗ T
    → v ≡ X⊑ᵗ T
  dynamize-alias-bwd X⊑X ()
  dynamize-alias-bwd X⊑★ ()
  dynamize-alias-bwd (X⊑ᵗ T) refl = refl

  old-alias-reflect′ : ∀ Z {T}
    → CTX.impEnvʷ (SPT.dynWorld Wᵐ) (toRenameᵗ old Z) ≡ X⊑ᵗ T
    → Σ[ T₀ ∈ Ty Δ ]
        ((CTX.impEnvʷ Wᵈ Z ≡ X⊑ᵗ T₀)
        × (T ≡ renameᵗ (toRenameᵗ old) T₀))
  old-alias-reflect′ Z eq
      with CTX.SmartFreshBehindGuard.old-alias-reflect guard Z
             (dynamize-alias-bwd
               (CTX.impEnvʷ Wᵐ (toRenameᵗ old Z)) eq)
  old-alias-reflect′ Z eq | T₀ , w-eq , T-eq =
    T₀ , CTX.alias-fwd al Z w-eq , T-eq

  fresh-no-alias′ : (∀ Z {T}
      → CTX.impEnvʷ Wᵈ Z ≡ X⊑ᵗ T → ⊥)
    → ∀ Z {T}
    → CTX.impEnvʷ (SPT.dynWorld Wᵐ) Z ≡ X⊑ᵗ T → ⊥
  fresh-no-alias′ naᵈ Z eq =
    CTX.SmartFreshBehindGuard.fresh-no-alias guard
      (λ Z′ eq′ → naᵈ Z′ (CTX.alias-fwd al Z′ eq′))
      Z (dynamize-alias-bwd (CTX.impEnvʷ Wᵐ Z) eq)

  smartSubst : suc Δ ⇒ˢ Δᵐ
  smartSubst Fin.zero =
    ＇ (toRenameᵗ (CTX.ηᴸʷ Wᵐ) Fin.zero)
  smartSubst (Fin.suc Z) = ＇ (toRenameᵗ old Z)

  smartStar : ∀ Z
    → CTX.impEnvʷ (CTX.liftWorldLeft X⊑★ Wᵈ) Z ≡ X⊑★
    → CTX.impEnvʷ (SPT.dynWorld Wᵐ) ⊢ smartSubst Z ⊑ ★
  smartStar Fin.zero star =
    X⊑★ (cong dynamizeVar
      (CTX.SmartFreshBehindGuard.fresh-mark-dynamic guard))
  smartStar (Fin.suc Z) star =
    X⊑★ (old-mark-mono′ Z (lift-star-inv star))

  smartAlias :
    PIC.SubstAliasMap
      (CTX.impEnvʷ (CTX.liftWorldLeft X⊑★ Wᵈ))
      (CTX.impEnvʷ (SPT.dynWorld Wᵐ))
      smartSubst
  smartAlias Fin.zero ()
  smartAlias (Fin.suc Z) eq with PI.lift-alias-inv eq
  smartAlias (Fin.suc Z) eq | T₀ , mode , refl =
    inj₂ (toRenameᵗ old Z , refl ,
      trans (old-alias-frozen′ Z mode)
        (cong X⊑ᵗ (sym (shift-subst-as-rename T₀))))
    where
    shift-subst-as-rename : ∀ (T₀ : Ty Δ)
      → substᵗ smartSubst (⇑ᵗ T₀)
        ≡ renameᵗ (toRenameᵗ old) T₀
    shift-subst-as-rename T₀ =
      trans (substᵗ-rename smartSubst Fin.suc T₀)
        (rename-as-subst (toRenameᵗ old) T₀)

  source-point : ∀ X
    → smartSubst (toRenameᵗ (keep (CTX.ηᴸʷ W)) X)
      ≡ ＇ (toRenameᵗ (CTX.ηᴸʷ Wᵐ) X)
  source-point Fin.zero = refl
  source-point (Fin.suc X) =
    cong ＇_ (sym (CTX.SmartFreshBehindGuard.old-source-frozen guard X))

  target-point : ∀ Y
    → smartSubst (toRenameᵗ (skip (CTX.ηᴿʷ W)) Y)
      ≡ ＇ (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y)
  target-point Y =
    cong ＇_ (sym (CTX.SmartFreshBehindGuard.target-frozen guard Y))

  source-eq : ∀ C
    → substᵗ smartSubst
        (CTX.embedᴸ (CTX.liftWorldLeft X⊑★ Wᵈ) C)
      ≡ CTX.embedᴸ (SPT.dynWorld Wᵐ) C
  source-eq C =
    trans (substᵗ-rename smartSubst
        (toRenameᵗ (keep (CTX.ηᴸʷ W))) C)
      (trans (substᵗ-cong C source-point)
        (rename-as-subst (toRenameᵗ (CTX.ηᴸʷ Wᵐ)) C))

  target-eq : ∀ C
    → substᵗ smartSubst
        (CTX.embedᴿ (CTX.liftWorldLeft X⊑★ Wᵈ) C)
      ≡ CTX.embedᴿ (SPT.dynWorld Wᵐ) C
  target-eq C =
    trans (substᵗ-rename smartSubst
        (toRenameᵗ (skip (CTX.ηᴿʷ W))) C)
      (trans (substᵗ-cong C target-point)
        (rename-as-subst (toRenameᵗ (CTX.ηᴿʷ Wᵐ)) C))

  transport′ : ∀ {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
    → A CTX.⊑ᵂ⟨ CTX.liftWorldLeft X⊑★ Wᵈ ⟩ B
    → A CTX.⊑ᵂ⟨ SPT.dynWorld Wᵐ ⟩ B
  transport′ =
    transport⊑ᵂ-by-subst
      {W = CTX.liftWorldLeft X⊑★ Wᵈ}
      {W′ = SPT.dynWorld Wᵐ}
      smartSubst smartStar smartAlias source-eq target-eq

decaySmartAliasMergeGuard : ∀ {Δᴸ Δᴿ Δ}
    {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTX.World (suc Δᴸ) Δᴿ Δ}
    {β α : TyVar Δᴿ}
  → (dec : EnvDecay W Wᵈ)
  → CTX.SmartAliasMergeGuard W Wᵐ β α
  → CTX.SmartAliasMergeGuard Wᵈ (SPT.dynWorld Wᵐ) β α
decaySmartAliasMergeGuard
    {Δᴸ = Δᴸ} {Δᴿ = Δᴿ} {Δ = Δ}
    {W = W} {Wᵈ = Wᵈ} {Wᵐ = Wᵐ} {β = β} {α = α}
    (env-decay refl refl refl refl mono al) guard =
  CTX.smart-alias-merge-guard
    (CTX.SmartAliasMergeGuard.β:=＇α guard)
    (CTX.SmartAliasMergeGuard.α:=★ guard)
    (CTX.SmartAliasMergeGuard.sourceStore-lifted guard)
    (CTX.SmartAliasMergeGuard.targetStore-same guard)
    transport′
    old-mark-monoᵐ
    (CTX.SmartAliasMergeGuard.target-frozen guard)
    (CTX.SmartAliasMergeGuard.pending-at-alias guard)
    (CTX.SmartAliasMergeGuard.old-source-frozen guard)
    (CTX.SmartAliasMergeGuard.no-old-source-at-alias guard)
    (cong dynamizeVar
      (CTX.SmartAliasMergeGuard.alias-mark-dynamic guard))
    (cong dynamizeVar
      (CTX.SmartAliasMergeGuard.name-mark-dynamic guard))
    target-mark-off-footprintᵐ
    old-alias-agreeᵐ
  where
  agree = CTX.SmartAliasMergeGuard.old-alias-agree guard

  dynamize-starᵐ : ∀ {Δ†} (v : VarImp Δ†)
    → (∀ {T} → v ≡ X⊑ᵗ T → ⊥)
    → dynamizeVar v ≡ X⊑★
  dynamize-starᵐ X⊑X not-al = refl
  dynamize-starᵐ X⊑★ not-al = refl
  dynamize-starᵐ (X⊑ᵗ T) not-al = ⊥-elim (not-al refl)

  dynamize-alias-bwdᵐ : ∀ {Δ†} (v : VarImp Δ†) {T}
    → dynamizeVar v ≡ X⊑ᵗ T
    → v ≡ X⊑ᵗ T
  dynamize-alias-bwdᵐ X⊑X ()
  dynamize-alias-bwdᵐ X⊑★ ()
  dynamize-alias-bwdᵐ (X⊑ᵗ T) refl = refl

  not-aliasᵐ : ∀ Z {T}
    → CTX.impEnvʷ Wᵈ Z ≡ X⊑★
    → CTX.impEnvʷ Wᵐ Z ≡ X⊑ᵗ T
    → ⊥
  not-aliasᵐ Z star al-eq
      with trans
        (sym (CTX.alias-fwd al Z (CTX.alias-bwd agree Z al-eq)))
        star
  not-aliasᵐ Z star al-eq | ()

  old-mark-monoᵐ : ∀ Z
    → CTX.impEnvʷ Wᵈ Z ≡ X⊑★
    → CTX.impEnvʷ (SPT.dynWorld Wᵐ) Z ≡ X⊑★
  old-mark-monoᵐ Z star =
    dynamize-starᵐ (CTX.impEnvʷ Wᵐ Z) (not-aliasᵐ Z star)

  target-mark-off-footprintᵐ : ∀ Xᴿ
    → Xᴿ ≢ β
    → Xᴿ ≢ α
    → CTX.impEnvʷ Wᵈ (toRenameᵗ (CTX.ηᴿʷ Wᵈ) Xᴿ) ≡ X⊑★
    → CTX.impEnvʷ (SPT.dynWorld Wᵐ)
        (toRenameᵗ (CTX.ηᴿʷ (SPT.dynWorld Wᵐ)) Xᴿ) ≡ X⊑★
  target-mark-off-footprintᵐ Xᴿ _ _ star =
    subst≡
      (λ V → dynamizeVar (CTX.impEnvʷ Wᵐ V) ≡ X⊑★)
      (sym (CTX.SmartAliasMergeGuard.target-frozen guard Xᴿ))
      (old-mark-monoᵐ (toRenameᵗ (CTX.ηᴿʷ W) Xᴿ) star)

  old-alias-agreeᵐ :
    CTX.AliasSame (CTX.impEnvʷ Wᵈ)
      (CTX.impEnvʷ (SPT.dynWorld Wᵐ))
  old-alias-agreeᵐ =
    CTX.alias-same
      (λ Z eq →
        cong dynamizeVar
          (CTX.alias-fwd agree Z (CTX.alias-bwd al Z eq)))
      (λ Z eq →
        CTX.alias-fwd al Z
          (CTX.alias-bwd agree Z
            (dynamize-alias-bwdᵐ (CTX.impEnvʷ Wᵐ Z) eq)))

  smartSubst : suc Δ ⇒ˢ Δ
  smartSubst Fin.zero = ＇ (toRenameᵗ (CTX.ηᴿʷ W) β)
  smartSubst (Fin.suc Z) = ＇ Z

  smartStar : ∀ Z
    → CTX.impEnvʷ (CTX.liftWorldLeft X⊑★ Wᵈ) Z ≡ X⊑★
    → CTX.impEnvʷ (SPT.dynWorld Wᵐ) ⊢ smartSubst Z ⊑ ★
  smartStar Fin.zero star =
    X⊑★ (cong dynamizeVar
      (CTX.SmartAliasMergeGuard.alias-mark-dynamic guard))
  smartStar (Fin.suc Z) star =
    X⊑★ (old-mark-monoᵐ Z (lift-star-inv star))

  smartAlias :
    PIC.SubstAliasMap
      (CTX.impEnvʷ (CTX.liftWorldLeft X⊑★ Wᵈ))
      (CTX.impEnvʷ (SPT.dynWorld Wᵐ))
      smartSubst
  smartAlias Fin.zero ()
  smartAlias (Fin.suc Z) eq with PI.lift-alias-inv eq
  smartAlias (Fin.suc Z) eq | T₀ , mode , refl =
    inj₂ (Z , refl ,
      trans (CTX.alias-fwd old-alias-agreeᵐ Z mode)
        (cong X⊑ᵗ (sym (shift-subst-id T₀))))
    where
    shift-subst-id : ∀ (T₀ : Ty Δ)
      → substᵗ smartSubst (⇑ᵗ T₀) ≡ T₀
    shift-subst-id T₀ =
      trans (substᵗ-rename smartSubst Fin.suc T₀)
        (trans (substᵗ-cong T₀ (λ X → refl))
          (substᵗ-id T₀))

  source-point : ∀ X
    → smartSubst (toRenameᵗ (keep (CTX.ηᴸʷ W)) X)
      ≡ ＇ (toRenameᵗ (CTX.ηᴸʷ Wᵐ) X)
  source-point Fin.zero =
    cong ＇_ (sym (CTX.SmartAliasMergeGuard.pending-at-alias guard))
  source-point (Fin.suc X) =
    cong ＇_ (sym (CTX.SmartAliasMergeGuard.old-source-frozen guard X))

  target-point : ∀ Y
    → smartSubst (toRenameᵗ (skip (CTX.ηᴿʷ W)) Y)
      ≡ ＇ (toRenameᵗ (CTX.ηᴿʷ Wᵐ) Y)
  target-point Y =
    cong ＇_ (sym (CTX.SmartAliasMergeGuard.target-frozen guard Y))

  source-eq : ∀ C
    → substᵗ smartSubst
        (CTX.embedᴸ (CTX.liftWorldLeft X⊑★ Wᵈ) C)
      ≡ CTX.embedᴸ (SPT.dynWorld Wᵐ) C
  source-eq C =
    trans (substᵗ-rename smartSubst
        (toRenameᵗ (keep (CTX.ηᴸʷ W))) C)
      (trans (substᵗ-cong C source-point)
        (rename-as-subst (toRenameᵗ (CTX.ηᴸʷ Wᵐ)) C))

  target-eq : ∀ C
    → substᵗ smartSubst
        (CTX.embedᴿ (CTX.liftWorldLeft X⊑★ Wᵈ) C)
      ≡ CTX.embedᴿ (SPT.dynWorld Wᵐ) C
  target-eq C =
    trans (substᵗ-rename smartSubst
        (toRenameᵗ (skip (CTX.ηᴿʷ W))) C)
      (trans (substᵗ-cong C target-point)
        (rename-as-subst (toRenameᵗ (CTX.ηᴿʷ Wᵐ)) C))

  transport′ : ∀ {A : Ty (suc Δᴸ)} {B : Ty Δᴿ}
    → A CTX.⊑ᵂ⟨ CTX.liftWorldLeft X⊑★ Wᵈ ⟩ B
    → A CTX.⊑ᵂ⟨ SPT.dynWorld Wᵐ ⟩ B
  transport′ =
    transport⊑ᵂ-by-subst
      {W = CTX.liftWorldLeft X⊑★ Wᵈ}
      {W′ = SPT.dynWorld Wᵐ}
      smartSubst smartStar smartAlias source-eq target-eq

decaySmartCommaLiftᴸ : ∀ {Δᴸ Δᴿ Δ Δᵐ}
    {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {Wᵐ : CTX.World (suc Δᴸ) Δᴿ Δᵐ}
  → (dec : EnvDecay W Wᵈ)
  → CTX.SmartCommaLiftᴸ W Wᵐ
  → CTX.SmartCommaLiftᴸ Wᵈ (SPT.dynWorld Wᵐ)
decaySmartCommaLiftᴸ dec (CTX.smart-fresh-behind guard) =
  CTX.smart-fresh-behind (decaySmartFreshBehindGuard dec guard)
decaySmartCommaLiftᴸ dec (CTX.smart-merge-alias guard) =
  CTX.smart-merge-alias (decaySmartAliasMergeGuard dec guard)

decayCtx-tgt : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
  → (dec : EnvDecay W Wᵈ)
  → (γ : CTX.CtxImp W)
  → CTX.tgtCtxʷ (decayCtx dec γ) ≡ CTX.tgtCtxʷ γ
decayCtx-tgt dec [] = refl
decayCtx-tgt dec (CTX.ctx-imp A B p ∷ γ) =
  cong (_ ∷_) (decayCtx-tgt dec γ)

------------------------------------------------------------------------
-- Decay of pivot-local rebasing
------------------------------------------------------------------------

decayRebaseAt : ∀ {Δᴸ Δᴿ Δ}
    {W₁ W₁ᵈ W₂ W₂ᵈ : CTX.World Δᴸ Δᴿ Δ} {Xᴸ Xᴿ}
  → (dec₁ : EnvDecay W₁ W₁ᵈ)
  → (dec₂ : EnvDecay W₂ W₂ᵈ)
  → CTX.RebaseAt W₁ W₂ Xᴸ Xᴿ
  → CTX.RebaseAt W₁ᵈ W₂ᵈ Xᴸ Xᴿ
decayRebaseAt
    {W₁ = CTX.world ηL₁ ηR₁ μ₁ ΣL₁ ΣR₁}
    {W₁ᵈ = CTX.world ηL₁′ ηR₁′ μ₁ᵈ ΣL₁′ ΣR₁′}
    {W₂ = CTX.world ηL₂ ηR₂ μ₂ ΣL₂ ΣR₂}
    {W₂ᵈ = CTX.world ηL₂′ ηR₂′ μ₂ᵈ ΣL₂′ ΣR₂′}
    (env-decay refl refl refl refl mono₁ al₁)
    dec₂@(env-decay refl refl refl refl mono₂ al₂)
    (CTX.rebase-at (CTX.same-runtime source-eq target-eq)
      offL frozenR aligned (CTX.store-rep-imp represented)) =
  CTX.rebase-at (CTX.same-runtime source-eq target-eq)
    offL frozenR aligned
    (CTX.store-rep-imp (decay⊑ᵂ dec₂ represented))

------------------------------------------------------------------------
-- Term-imprecision decay
------------------------------------------------------------------------

private
  decayRep★PartnerOK : ∀ {Δᴸ Δᴿ Δ}
      {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ} {P Xᴿ? M′}
    → EnvDecay W Wᵈ
    → CTX.Rep★PartnerOK W X P Xᴿ? M′
    → CTX.Rep★PartnerOK Wᵈ X P Xᴿ? M′
  decayRep★PartnerOK (env-decay refl refl refl refl mono al)
      (CTX.rep★-untagged nt) =
    CTX.rep★-untagged nt
  decayRep★PartnerOK (env-decay refl refl refl refl mono al)
      (CTX.rep★-nonvar-tag Gnv) =
    CTX.rep★-nonvar-tag Gnv
  decayRep★PartnerOK (env-decay refl refl refl refl mono al)
      (CTX.rep★-var-tag aligned) =
    CTX.rep★-var-tag aligned
  decayRep★PartnerOK (env-decay refl refl refl refl mono al)
      (CTX.rep★-matched-inner-tags X₂≢X aligned) =
    CTX.rep★-matched-inner-tags X₂≢X aligned
  decayRep★PartnerOK dec (CTX.rep★-round-trip ok) =
    CTX.rep★-round-trip (decayRep★PartnerOK dec ok)

  decayNoTargetOccupantAtSource : ∀ {Δᴸ Δᴿ Δ}
      {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
      {X : TyVar Δᴸ}
    → EnvDecay W Wᵈ
    → CTX.NoTargetOccupantAtSource W X
    → CTX.NoTargetOccupantAtSource Wᵈ X
  decayNoTargetOccupantAtSource
      (env-decay refl refl refl refl mono al) no-target =
    no-target

  decaySourceConcealOK : ∀ {Δᴸ Δᴿ Δ}
      {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
      {M : Term Δᴸ} {A A′ : Ty Δᴸ}
      {c : Conv↓ Δᴸ A A′} {Xᴿ? M′}
    → EnvDecay W Wᵈ
    → CTX.SourceConcealOK W M c Xᴿ? M′
    → CTX.SourceConcealOK Wᵈ M c Xᴿ? M′
  decaySourceConcealOK dec
      (CTX.seal-nonstar-unmatched-ok {X = X} Rns no-target) =
    CTX.seal-nonstar-unmatched-ok Rns
      (decayNoTargetOccupantAtSource {X = X} dec no-target)
  decaySourceConcealOK (env-decay refl refl refl refl mono al)
      (CTX.seal-nonstar-name-protected-ok Rns aligned) =
    CTX.seal-nonstar-name-protected-ok Rns aligned
  decaySourceConcealOK dec CTX.fun-conceal-ok =
    CTX.fun-conceal-ok
  decaySourceConcealOK dec CTX.all-conceal-ok =
    CTX.all-conceal-ok
  decaySourceConcealOK dec CTX.id-conceal-ok =
    CTX.id-conceal-ok

  decayMatchedConcealPartnerOK : ∀ {Δᴸ Δᴿ Δ}
      {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
      {M : Term Δᴸ} {A A′ : Ty Δᴸ}
      {c : Conv↓ Δᴸ A A′} {Y M′}
    → EnvDecay W Wᵈ
    → CTX.MatchedConcealPartnerOK W M c Y M′
    → CTX.MatchedConcealPartnerOK Wᵈ M c Y M′
  decayMatchedConcealPartnerOK dec
      (CTX.matched-seal-star-partner ok) =
    CTX.matched-seal-star-partner (decayRep★PartnerOK dec ok)
  decayMatchedConcealPartnerOK dec (CTX.matched-seal-nonstar Rns) =
    CTX.matched-seal-nonstar Rns
  decayMatchedConcealPartnerOK dec CTX.matched-fun-conceal-target =
    CTX.matched-fun-conceal-target
  decayMatchedConcealPartnerOK dec CTX.matched-all-conceal-target =
    CTX.matched-all-conceal-target
  decayMatchedConcealPartnerOK dec CTX.matched-id-conceal-target =
    CTX.matched-id-conceal-target

⊢²-decay : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W} {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A CTX.⊑ᵂ⟨ W ⟩ B}
  → (dec : EnvDecay W Wᵈ)
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → Wᵈ ∣ decayCtx dec γ ⊢² M ⊑ M′ ∶ decay⊑ᵂ dec p
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.x⊑x² x∈) =
  CTI2.x⊑x² (decay∋ʷ dec x∈)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.ƛ⊑ƛ² M⊑M′) =
  CTI2.ƛ⊑ƛ² (⊢²-decay dec M⊑M′)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.·⊑·² L⊑L′ M⊑M′) =
  CTI2.·⊑·² (⊢²-decay dec L⊑L′) (⊢²-decay dec M⊑M′)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.Λ⊑Λ² liftγ vV vV′ V⊑V′ q) =
  CTI2.Λ⊑Λ² (decayLiftCtx dec liftγ) vV vV′
    (⊢²-decay (liftDecayBoth X⊑X dec) V⊑V′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    {γ = γ}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.Λ⊑² Anv zero∈A liftγ vV M′⊢ V⊑M′ q) =
  CTI2.Λ⊑² Anv zero∈A (decayLiftCtxᴸ dec liftγ) vV
    (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
      (sym (decayCtx-tgt dec γ)) M′⊢)
    (⊢²-decay (liftDecayLeft X⊑★ dec) V⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    {γ = γ}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.Λ⊑²-smart-comma {Wᵐ = Wᵐ} Anv zero∈A liftW
      liftγ vV M′⊢ V⊑M′ q) =
  CTI2.Λ⊑²-smart-comma Anv zero∈A
    (decaySmartCommaLiftᴸ dec liftW)
    (decaySmartLiftCtxᴸ dec (SPT.dynWorld-decay Wᵐ) liftγ) vV
    (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
      (sym (decayCtx-tgt dec γ)) M′⊢)
    (⊢²-decay (SPT.dynWorld-decay Wᵐ) V⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.•⊑•² p∀ M⊑M′ q r) =
  CTI2.•⊑•² (decay⊑ᵂ dec p∀) (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q) (decay⊑ᵂ dec r)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.•⊑² p∀ M⊑M′ q r) =
  CTI2.•⊑² (decay⊑ᵂ dec p∀) (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q) (decay⊑ᵂ dec r)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.κ⊑κ² κ p) =
  CTI2.κ⊑κ² κ (decay⊑ᵂ dec p)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.cast⊑cast² c c′ M⊑M′ q) =
  CTI2.cast⊑cast² c c′ (⊢²-decay dec M⊑M′) (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.⊑cast² c′ M⊑M′ q) =
  CTI2.⊑cast² c′ (⊢²-decay dec M⊑M′) (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.cast⊑² c M⊑M′ q) =
  CTI2.cast⊑² c (⊢²-decay dec M⊑M′) (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.⊑reveal² rule-mono CTX.rebase-idᴿ sc
      c′⊢ M⊑M′ q) =
  CTI2.⊑reveal² CTX.idᵉᵐ CTX.rebase-idᴿ
    (decaySameCtx dec dec sc) c′⊢ (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.⊑reveal² {W′ = W′} rule-mono
      (CTX.rebase-varᴿ rb) sc c′⊢ M⊑M′ q) =
  CTI2.⊑reveal²
    (blend-mono {W′ = W′} {Wᵈ = Wᵈ} agreeʹ)
    (CTX.rebase-varᴿ
      (decayRebaseAt dec
        (blend-decay {W′ = W′} {Wᵈ = Wᵈ} agreeʹ) rb))
    (decaySameCtx dec
      (blend-decay {W′ = W′} {Wᵈ = Wᵈ} agreeʹ) sc)
    c′⊢
    (⊢²-decay (blend-decay {W′ = W′} {Wᵈ = Wᵈ} agreeʹ) M⊑M′)
    (decay⊑ᵂ dec q)
  where
  agreeʹ = CTX.alias-same-trans
    (CTX.alias-same-sym (CTX.aliasAgree rule-mono)) al
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.⊑conceal² rule-mono CTX.rebase-idᴿ sc
      c′⊢ M⊑M′ q) =
  CTI2.⊑conceal² CTX.idᵉᵐ CTX.rebase-idᴿ
    (decaySameCtx dec dec sc) c′⊢ (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.⊑conceal² {W′ = W′} rule-mono
      (CTX.rebase-varᴿ rb) sc c′⊢ M⊑M′ q) =
  CTI2.⊑conceal²
    (blend-mono {W′ = W′} {Wᵈ = Wᵈ} agreeʹ)
    (CTX.rebase-varᴿ
      (decayRebaseAt
        (blend-decay {W′ = W′} {Wᵈ = Wᵈ} agreeʹ) dec rb))
    (decaySameCtx dec
      (blend-decay {W′ = W′} {Wᵈ = Wᵈ} agreeʹ) sc)
    c′⊢
    (⊢²-decay (blend-decay {W′ = W′} {Wᵈ = Wᵈ} agreeʹ) M⊑M′)
    (decay⊑ᵂ dec q)
  where
  agreeʹ = CTX.alias-same-trans
    (CTX.alias-same-sym (CTX.aliasAgree rule-mono)) al
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.reveal⊑² rule-mono CTX.rebase-idᴸ sc
      c⊢ M⊑M′ q) =
  CTI2.reveal⊑² CTX.idᵉᵐ CTX.rebase-idᴸ
    (decaySameCtx dec dec sc) c⊢ (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.reveal⊑² {W′ = W′} rule-mono
      (CTX.rebase-varᴸ rb) sc c⊢ M⊑M′ q) =
  CTI2.reveal⊑²
    (blend-mono {W′ = W′} {Wᵈ = Wᵈ} agreeʹ)
    (CTX.rebase-varᴸ
      (decayRebaseAt dec
        (blend-decay {W′ = W′} {Wᵈ = Wᵈ} agreeʹ) rb))
    (decaySameCtx dec
      (blend-decay {W′ = W′} {Wᵈ = Wᵈ} agreeʹ) sc)
    c⊢
    (⊢²-decay (blend-decay {W′ = W′} {Wᵈ = Wᵈ} agreeʹ) M⊑M′)
    (decay⊑ᵂ dec q)
  where
  agreeʹ = CTX.alias-same-trans
    (CTX.alias-same-sym (CTX.aliasAgree rule-mono)) al
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.reveal⊑² rule-mono
      (CTX.rebase-onlyᴸ to-star disaligned represented)
      sc c⊢ M⊑M′ q) =
  CTI2.reveal⊑² CTX.idᵉᵐ
    (CTX.rebase-onlyᴸ (mono _ to-star) disaligned
      (decay⊑ᵂ dec represented))
    (decaySameCtx dec dec sc) c⊢ (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.conceal⊑²-seal-star-open no-target rule-mono
      (CTX.tag-rebase-onlyᴸ to-star disaligned represented)
      sc c⊢ M⊑M′ q) =
  CTI2.conceal⊑²-seal-star-open
    (decayNoTargetOccupantAtSource dec no-target)
    CTX.idᵉᵐ
    (CTX.tag-rebase-onlyᴸ (mono _ to-star) disaligned
      (decay⊑ᵂ dec represented))
    (decaySameCtx dec dec sc) c⊢ (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.conceal⊑²-source-ok ok rule-mono CTX.tag-rebase-idᴸ
      sc c⊢ M⊑M′ q) =
  CTI2.conceal⊑²-source-ok (decaySourceConcealOK dec ok)
    CTX.idᵉᵐ CTX.tag-rebase-idᴸ
    (decaySameCtx dec dec sc) c⊢ (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.conceal⊑²-source-ok {W′ = W′} ok rule-mono
      (CTX.tag-rebase-varᴸ rb) sc c⊢ M⊑M′ q) =
  CTI2.conceal⊑²-source-ok
    (decaySourceConcealOK
      (blend-decay {W′ = W′} {Wᵈ = Wᵈ} agreeʹ) ok)
    (blend-mono {W′ = W′} {Wᵈ = Wᵈ} agreeʹ)
    (CTX.tag-rebase-varᴸ
      (decayRebaseAt
        (blend-decay {W′ = W′} {Wᵈ = Wᵈ} agreeʹ) dec rb))
    (decaySameCtx dec
      (blend-decay {W′ = W′} {Wᵈ = Wᵈ} agreeʹ) sc)
    c⊢
    (⊢²-decay (blend-decay {W′ = W′} {Wᵈ = Wᵈ} agreeʹ) M⊑M′)
    (decay⊑ᵂ dec q)
  where
  agreeʹ = CTX.alias-same-trans
    (CTX.alias-same-sym (CTX.aliasAgree rule-mono)) al
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.conceal⊑²-source-ok ok rule-mono
      (CTX.tag-rebase-onlyᴸ to-star disaligned represented)
      sc c⊢ M⊑M′ q) =
  CTI2.conceal⊑²-source-ok (decaySourceConcealOK dec ok)
    CTX.idᵉᵐ
    (CTX.tag-rebase-onlyᴸ (mono _ to-star) disaligned
      (decay⊑ᵂ dec represented))
    (decaySameCtx dec dec sc) c⊢ (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec q)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.reveal⊑reveal² {Wᵖ = Wᵖ} rule-mono rb sc
      c⊢ c′⊢ M⊑M′ q) =
  CTI2.reveal⊑reveal²
    (blend-mono {W′ = Wᵖ} {Wᵈ = Wᵈ} agreeʹ)
    (decayRebaseAt dec
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ} agreeʹ) rb)
    (decaySameCtx dec
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ} agreeʹ) sc)
    c⊢ c′⊢
    (⊢²-decay (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ} agreeʹ) M⊑M′)
    (decay⊑ᵂ dec q)
  where
  agreeʹ = CTX.alias-same-trans
    (CTX.alias-same-sym (CTX.aliasAgree rule-mono)) al
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.conceal⊑conceal² {Wᵖ = Wᵖ} ok rule-mono rb sc
      c⊢ c′⊢ M⊑M′ q) =
  CTI2.conceal⊑conceal²
    (decayMatchedConcealPartnerOK
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ} agreeʹ) ok)
    (blend-mono {W′ = Wᵖ} {Wᵈ = Wᵈ} agreeʹ)
    (decayRebaseAt
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ} agreeʹ) dec rb)
    (decaySameCtx dec
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ} agreeʹ) sc)
    c⊢ c′⊢
    (⊢²-decay (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ} agreeʹ) M⊑M′)
    (decay⊑ᵂ dec q)
  where
  agreeʹ = CTX.alias-same-trans
    (CTX.alias-same-sym (CTX.aliasAgree rule-mono)) al
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.packaged-seal-star² {Wᵖ = Wᵖ} ok rule-mono rb sc
      c⊢ c′⊢ M⊑M′ sourcePrem q) =
  CTI2.packaged-seal-star²
    (decayMatchedConcealPartnerOK
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ} agreeʹ) ok)
    (blend-mono {W′ = Wᵖ} {Wᵈ = Wᵈ} agreeʹ)
    (decayRebaseAt
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ} agreeʹ) dec rb)
    (decaySameCtx dec
      (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ} agreeʹ) sc)
    c⊢ c′⊢
    (⊢²-decay (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ} agreeʹ) M⊑M′)
    (⊢²-decay (blend-decay {W′ = Wᵖ} {Wᵈ = Wᵈ} agreeʹ) sourcePrem)
    (decay⊑ᵂ dec q)
  where
  agreeʹ = CTX.alias-same-trans
    (CTX.alias-same-sym (CTX.aliasAgree rule-mono)) al
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.blame⊑² M′⊢ p) =
  CTI2.blame⊑²
    (subst≡ (λ Γ → ⟨ _ , _ , Γ ⟩ ⊢ _ ⦂ _)
      (sym (decayCtx-tgt dec _)) M′⊢)
    (decay⊑ᵂ dec p)
⊢²-decay
    {W = CTX.world ηL ηR μ ΣL ΣR}
    {Wᵈ = Wᵈ@(CTX.world ηL′ ηR′ μᵈ ΣL′ ΣR′)}
    dec@(env-decay refl refl refl refl mono al)
    (CTI2.⊕⊑⊕² op L⊑L′ M⊑M′ r) =
  CTI2.⊕⊑⊕² op (⊢²-decay dec L⊑L′) (⊢²-decay dec M⊑M′)
    (decay⊑ᵂ dec r)

⊢²-decay-at : ∀ {Δᴸ Δᴿ Δ} {W Wᵈ : CTX.World Δᴸ Δᴿ Δ}
    {γ : CTX.CtxImp W} {M : Term Δᴸ} {M′ : Term Δᴿ}
    {A : Ty Δᴸ} {B : Ty Δᴿ} {p : A CTX.⊑ᵂ⟨ W ⟩ B}
  → (dec : EnvDecay W Wᵈ)
  → W ∣ γ ⊢² M ⊑ M′ ∶ p
  → (pᵈ : A CTX.⊑ᵂ⟨ Wᵈ ⟩ B)
  → Wᵈ ∣ decayCtx dec γ ⊢² M ⊑ M′ ∶ pᵈ
⊢²-decay-at {Wᵈ = Wᵈ} {γ = γ} {M = M} {M′ = M′} {p = p}
    dec M⊑M′ pᵈ =
  subst≡ (λ q → Wᵈ ∣ decayCtx dec γ ⊢² M ⊑ M′ ∶ q)
    (PI.⊑-unique (decay⊑ᵂ dec p) pᵈ) (⊢²-decay dec M⊑M′)
