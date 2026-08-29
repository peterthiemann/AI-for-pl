module proof.LR-narrow.ImpreciseReveal where

-- File Charter:
--   * The imprecise-side one-sided structural reveal and conceal
--     (Finding I item 2 of REPLACEMENT-CLOSURE-DESIGN.md): when the
--     paired slot's center variable does not occur in the precise
--     endpoint of a derivation, wrapping only the imprecise endpoint
--     in the slot conversion exchanges the derivation for its
--     right-replaced form.  The precise endpoint and its term are
--     untouched.
--   * Every case produces the clause at the canonical replaced
--     derivation built by `replace★-⊑` (the left endpoint fixed by
--     `replaceTy-absent`) and reindexes to the caller's derivation.
--   * The avoidance premise is the ★-right-exempt `AliasAvoid★ᵖ`:
--     exempted alias leaves have ★ on the right, where the wrapper
--     is an identity, so the strong component is only consulted at
--     the fun- and ∀-shaped types.
--   * The `∀⊑` source case conses the imprecise-only wrapper onto
--     the stored right-universal family and reindexes the clause to
--     the replaced derivation; no recursion into the reveal
--     induction is involved, so the cons lives outside the mutual
--     block.

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using
  (n≤1+n; ≤-trans; ≤-refl; m≤m+n; m≤n+m)
open import Data.Unit.Polymorphic.Base using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (False)
open import Data.Fin.Properties using (_≟_)

open import Types
open import TyStore
open import CastTerms
open import Conversion using
  (Conv↑; Conv↓; id↑; id↓; _↦↑_; _↦↓_; replaceTy; 〖_,_↑_〗;
   makeConceal)
open import Consistency using (toRenameᵗ)
import Imprecision as I
import proof.Imprecision as PI
open import Reduction
import Eval as E
open import Interpreter
open import proof.ImprecisionConsistency using
  (toRenameᵗ-injective; renameᵗ-injective; ext-injective;
   fin-suc-injective; ty-all-injective)
open import proof.TypeSafety.Progress using (no-bot-value)
open import proof.TypeSafety.Preservation using
  (structural-reveal-typing; structural-conceal-typing)
open import LR-narrow.World
open import LR-narrow.SlotSequence
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.Closure using (value-imprecision-downward-to)
import proof.LR-narrow.Closure as ClosureProof
open import proof.LR-narrow.ImmediateReturn using
  (related-values-return)
open import proof.LR-narrow.KeepStepExpansion using
  (related-imprecise-keep-step-expand)
open import proof.LR-narrow.RevealSteps
open import proof.LR-narrow.RevealLifting using
  (PairedSlot; paired-slot; center; atom; entry-eq; mode-eq;
   slot-future; renameᵗ-replaceTy; alias-avoid★-lift-body)
open import proof.LR-narrow.StarNoOccurrence using
  (replaceTy-absent; renameᵗ-∉ᵗ; renameᵗ-reflects-∉ᵗ)
open import proof.LR-narrow.CastComposition using
  (computations-related-future-compose)
open import proof.LR-narrow.FramePhases using (Frame)
open import proof.LR-narrow.FrameComposition
open import proof.LR-narrow.RevealFrames using
  (revealFrame; concealFrame; RevealFrm; reveal-frm; ConcealFrm;
   conceal-frm)
open import proof.LR-narrow.ArgumentFrame using
  (related-application-computation)
open import proof.LR-narrow.SlotLifting using
  (slotXᴾ; slotXᴵ; slotRᴾ; slotRᴵ;
   transported-reveal-eq; transported-conceal-eq;
   lifted-reveal-imprecise; lifted-conceal-imprecise;
   liftImpreciseTy-arrow; liftImpreciseTy-universal;
   slot-imprecise-variable-lift; slot-imprecise-rep-lift;
   replace-imprecise-lift)
open import proof.LR-narrow.UniversalReveal using
  (liftImpreciseBody-replace; post-bind-weaken)
open import proof.LR-narrow.ImprecisionSize using
  (sizeᵖ; lift-center-size)
open import proof.LR-narrow.AliasAvoid using
  (AliasAvoid★ᵖ; alias-avoid★-any)
open import proof.LR-narrow.RevealLifting using
  (alias-avoid★-lift-center; alias-avoid★-lift-dynamic-body;
   liftImpreciseTy-replace; shift-replace)
open import proof.LR-narrow.ReplaceImprecision using
  (replace★-⊑; replace-alias-not-self★)
open import proof.LR-narrow.PreciseReveal using
  (no-precise-bottom-value)

open ImpreciseComposition revealFrame using () renaming
  (imprecise-frame-computations-related to
    reveal-imprecise-composition;
   ImprecisePlugValues to RevealImprecisePlugValues)
open ImpreciseComposition concealFrame using () renaming
  (imprecise-frame-computations-related to
    conceal-imprecise-composition;
   ImprecisePlugValues to ConcealImprecisePlugValues)

------------------------------------------------------------------------
-- The statements
------------------------------------------------------------------------

ImpreciseRevealAt : ℕ → Set
ImpreciseRevealAt k = ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W) {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → AliasAvoid★ᵖ (center s) p
  → center s ∉ᵗ Aᴾ
  → embedImprecise (core W) Bᴵ ≡ Aᴵ
  → ∀ {Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Aᴾ ⊑ Cᴵ)
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
      ≡ Cᴵ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation q) k
      (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗) Vᴾ

ImpreciseConcealAt : ℕ → Set
ImpreciseConcealAt k = ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W) {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → AliasAvoid★ᵖ (center s) p
  → center s ∉ᵗ Aᴾ
  → embedImprecise (core W) Bᴵ ≡ Aᴵ
  → ∀ {Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Aᴾ ⊑ Cᴵ)
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
      ≡ Cᴵ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W q k Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation p) k
      (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ) Vᴾ

------------------------------------------------------------------------
-- Endpoint typings of an imprecise-side wrapper
------------------------------------------------------------------------

imp-reveal-endpoints : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W) {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → embedImprecise (core W) Bᴵ ≡ Aᴵ
  → ∀ {Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Aᴾ ⊑ Cᴵ)
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
      ≡ Cᴵ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → TypedEndpoints W p Vᴵ Vᴾ
  → Value (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗)
  → TypedEndpoints W q
      (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗) Vᴾ
imp-reveal-endpoints W s {Bᴵ = Bᴵ} p sourceᴵ q targetᴵ
    endpoints vᴵ =
  typed-endpoints _ _ targetᴵ (preciseEmbedded endpoints)
    vᴵ (precise-value endpoints)
    (⊢reveal (structural-reveal-typing Bᴵ (impreciseBound (atom s)))
      Vᴵ⊢Bᴵ)
    (precise-typed endpoints)
  where
  Vᴵ⊢Bᴵ = subst≡
    (λ A → ⟨ _ , impreciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    (renameᵗ-injective
      (toRenameᵗ-injective (impreciseEmbedding (core W)))
      (trans (impreciseEmbedded endpoints) (sym sourceᴵ)))
    (imprecise-typed endpoints)

imp-conceal-endpoints : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W) {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → embedImprecise (core W) Bᴵ ≡ Aᴵ
  → ∀ {Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Aᴾ ⊑ Cᴵ)
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
      ≡ Cᴵ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → TypedEndpoints W q Vᴵ Vᴾ
  → Value (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ)
  → TypedEndpoints W p
      (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ) Vᴾ
imp-conceal-endpoints W s {Bᴵ = Bᴵ} p sourceᴵ q targetᴵ
    endpoints vᴵ =
  typed-endpoints _ _ sourceᴵ (preciseEmbedded endpoints)
    vᴵ (precise-value endpoints)
    (⊢conceal
      (structural-conceal-typing Bᴵ (impreciseBound (atom s)))
      Vᴵ⊢Bᴵʳ)
    (precise-typed endpoints)
  where
  Vᴵ⊢Bᴵʳ = subst≡
    (λ A → ⟨ _ , impreciseStore (core W) , [] ⟩ ⊢ _ ⦂ A)
    (renameᵗ-injective
      (toRenameᵗ-injective (impreciseEmbedding (core W)))
      (trans (impreciseEmbedded endpoints) (sym targetᴵ)))
    (imprecise-typed endpoints)

------------------------------------------------------------------------
-- A paired variable on the right forces the same variable on the left
------------------------------------------------------------------------

-- Under derivation-restricted avoidance, the only derivations whose
-- right endpoint is a paired-mode variable start at that variable:
-- alias detours are cut off by the avoidance and right-universal
-- sources by their non-variable body.

paired-var-right-⊑ : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ}
    {Z : TyVar Δ}
  → μ Z ≡ I.X⊑X
  → (r : I._⊢_⊑_ μ A B)
  → B ≡ ＇ Z
  → AliasAvoid★ᵖ Z r
  → A ≡ ＇ Z
paired-var-right-⊑ mode I.★⊑★ () avoid
paired-var-right-⊑ mode I.ι⊑ι () avoid
paired-var-right-⊑ mode I.X⊑X refl avoid = refl
paired-var-right-⊑ mode (I.⇒⊑⇒ r₁ r₂) () avoid
paired-var-right-⊑ mode (I.∀⊑∀ r) () avoid
paired-var-right-⊑ mode (I.⇒⊑★ r₁ r₂) () avoid
paired-var-right-⊑ mode I.ι⊑★ () avoid
paired-var-right-⊑ mode (I.X⊑★ eq) () avoid
paired-var-right-⊑ {μ = μ} {Z = Z} mode
    (I.∀⊑ {A = A₀} nonvar occurs r) refl avoid
    with paired-var-right-⊑ {μ = I.instᵐ μ} {Z = Fin.suc Z}
           (I.ext-mode-paired {μ = μ} {v = I.X⊑★} mode)
           r refl avoid
paired-var-right-⊑ {Z = Z} mode
    (I.∀⊑ nonvar occurs r) refl avoid
    | refl with nonvar
paired-var-right-⊑ {Z = Z} mode
    (I.∀⊑ nonvar occurs r) refl avoid
    | refl | ()
paired-var-right-⊑ mode I.∀★⊑★ () avoid
paired-var-right-⊑ mode (I.∀⊑★ nonstar r) () avoid
paired-var-right-⊑ mode I.bot-elim () avoid
paired-var-right-⊑ mode I.bot⊑★ () avoid
paired-var-right-⊑ {Z = Z} mode
    (I.alias {X = X} {T = T} eq r) refl (inj₁ star-eq , avoid)
    with star-eq
paired-var-right-⊑ {Z = Z} mode
    (I.alias {X = X} {T = T} eq r) refl (inj₁ star-eq , avoid)
    | ()
paired-var-right-⊑ {Z = Z} mode
    (I.alias {X = X} {T = T} eq r) refl (inj₂ Z∉T , avoid)
    with paired-var-right-⊑ mode r refl avoid
paired-var-right-⊑ mode (I.alias eq r) refl (inj₂ Z∉T , avoid)
    | refl = ⊥-elim (PI.∈∉-⊥ Z∉T var-∈)

------------------------------------------------------------------------
-- Occurrence and size bookkeeping
------------------------------------------------------------------------

sizeᵖ-bound-left : ∀ {a b n} → suc (a + b) ≤ suc n → a ≤ n
sizeᵖ-bound-left {a} {b} {n} (s≤s a+b≤n) =
  ≤-trans (m≤m+n a b) a+b≤n

sizeᵖ-bound-right : ∀ {a b n} → suc (a + b) ≤ suc n → b ≤ n
sizeᵖ-bound-right {a} {b} {n} (s≤s a+b≤n) =
  ≤-trans (m≤n+m b a) a+b≤n

-- Center-variable non-occurrence transports along futures, at a type
-- and under one binder.

lift-center-∉ᵗ : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {c : TyVar Δᶜ} {A : Ty Δᶜ}
  → c ∉ᵗ A
  → liftCenterVariable W≼W′ c ∉ᵗ liftCenterTy W≼W′ A
lift-center-∉ᵗ future-refl no-occur = no-occur
lift-center-∉ᵗ (future-paired W≼W′ r) no-occur =
  renameᵗ-∉ᵗ Fin.suc fin-suc-injective (lift-center-∉ᵗ W≼W′ no-occur)
lift-center-∉ᵗ (future-precise W≼W′ r) no-occur =
  renameᵗ-∉ᵗ Fin.suc fin-suc-injective (lift-center-∉ᵗ W≼W′ no-occur)
lift-center-∉ᵗ (future-alias W≼W′) no-occur =
  renameᵗ-∉ᵗ Fin.suc fin-suc-injective (lift-center-∉ᵗ W≼W′ no-occur)
lift-center-∉ᵗ (future-imprecise W≼W′) no-occur =
  renameᵗ-∉ᵗ Fin.suc fin-suc-injective (lift-center-∉ᵗ W≼W′ no-occur)

lift-center-body-∉ᵗ : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {c : TyVar Δᶜ} {A : Ty (suc Δᶜ)}
  → Fin.suc c ∉ᵗ A
  → Fin.suc (liftCenterVariable W≼W′ c) ∉ᵗ liftCenterBody W≼W′ A
lift-center-body-∉ᵗ future-refl no-occur = no-occur
lift-center-body-∉ᵗ (future-paired W≼W′ r) no-occur =
  renameᵗ-∉ᵗ (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (lift-center-body-∉ᵗ W≼W′ no-occur)
lift-center-body-∉ᵗ (future-precise W≼W′ r) no-occur =
  renameᵗ-∉ᵗ (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (lift-center-body-∉ᵗ W≼W′ no-occur)
lift-center-body-∉ᵗ (future-alias W≼W′) no-occur =
  renameᵗ-∉ᵗ (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (lift-center-body-∉ᵗ W≼W′ no-occur)
lift-center-body-∉ᵗ (future-imprecise W≼W′) no-occur =
  renameᵗ-∉ᵗ (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (lift-center-body-∉ᵗ W≼W′ no-occur)

------------------------------------------------------------------------
-- The commutation of the imprecise embedding with the replacement
------------------------------------------------------------------------

embI-replace-eq : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W) (Bᴵ : Ty Δᴵ)
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
      ≡ replaceTy (center s)
          (embedImprecise (core W) (slotRᴵ s))
          (embedImprecise (core W) Bᴵ)
embI-replace-eq W s Bᴵ = trans
  (renameᵗ-replaceTy (toRenameᵗ (impreciseEmbedding (core W)))
    (toRenameᵗ-injective (impreciseEmbedding (core W)))
    (slotXᴵ s) (slotRᴵ s) Bᴵ)
  (cong
    (λ Z → replaceTy Z (embedImprecise (core W) (slotRᴵ s))
      (embedImprecise (core W) Bᴵ))
    (impreciseAligned (atom s)))

------------------------------------------------------------------------
-- Rebuilding an alias holding with a wrapped imprecise endpoint
------------------------------------------------------------------------

alias-holds-imp-map : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {Wc : CoreWorld Δᴾ Δᴵ Δᶜ} {Z : TyVar Δᶜ} {T B B′ : Ty Δᶜ}
    {ℛ ℛ′ : PayloadRelation Wc}
    {p : impEnv Wc I.⊢ T ⊑ B} {p′ : impEnv Wc I.⊢ T ⊑ B′}
    {Vᴵ Vᴵ′ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    (entry : SemanticEntry Wc Z mode) (eq : mode ≡ I.X⊑ᵗ T)
  → (∀ {Uᴾ : Term Δᴾ} → ℛ p Vᴵ Uᴾ → ℛ′ p′ Vᴵ′ Uᴾ)
  → AliasAtomHolds ℛ entry eq p Vᴵ Vᴾ
  → AliasAtomHolds ℛ′ entry eq p′ Vᴵ′ Vᴾ
alias-holds-imp-map (paired-entry a) eq f ()
alias-holds-imp-map (dynamic-entry a) () f holds
alias-holds-imp-map (target-entry a) () f holds
alias-holds-imp-map (alias-entry a) refl f
    (alias-holds Uᴾ shape rel) =
  alias-holds Uᴾ shape (f rel)

------------------------------------------------------------------------
-- Identity wrappers step away on the imprecise endpoint
------------------------------------------------------------------------

imp-identity-reveal : ∀ {j} {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    {Aᴾ Aᴵ Cᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    (q : impEnv (core W) I.⊢ Aᴾ ⊑ Cᴵ)
  → Aᴵ ≡ Cᴵ
  → (Bᴵ : Ty Δᴵ)
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p j Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation q) j
      (Vᴵ ↑ id↑ Bᴵ) Vᴾ
imp-identity-reveal {j = j} W p q eq Bᴵ related
    with reveal-id-step-question {Σ = impreciseStore (core W)} Bᴵ
           (imprecise-value
             (ClosureProof.value-imprecision-endpoints related))
imp-identity-reveal {j = j} W p q eq Bᴵ related | vVᴵ , step-eq =
  related-imprecise-keep-step-expand (λ ())
    (reveal-id-value-none Bᴵ vVᴵ) (pure-step (id-reveal vVᴵ)) step-eq
    (ClosureProof.computations-related-reindex p q refl eq refl refl
      (related-values-return
        vVᴵ
        (precise-value
          (ClosureProof.value-imprecision-endpoints related))
        (λ i i≤j → value-imprecision-downward-to i≤j related)))

imp-identity-conceal : ∀ {j} {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    {Aᴾ Aᴵ Cᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    (q : impEnv (core W) I.⊢ Aᴾ ⊑ Cᴵ)
  → Aᴵ ≡ Cᴵ
  → (Bᴵ : Ty Δᴵ)
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W q j Vᴵ Vᴾ
  → ComputationsRelated W (FutureValueRelation p) j
      (Vᴵ ↓ id↓ Bᴵ) Vᴾ
imp-identity-conceal {j = j} W p q eq Bᴵ related
    with conceal-id-step-question {Σ = impreciseStore (core W)} Bᴵ
           (imprecise-value
             (ClosureProof.value-imprecision-endpoints related))
imp-identity-conceal {j = j} W p q eq Bᴵ related | vVᴵ , step-eq =
  related-imprecise-keep-step-expand (λ ())
    (conceal-id-value-none Bᴵ vVᴵ) (pure-step (id-conceal vVᴵ))
    step-eq
    (ClosureProof.computations-related-reindex q p refl (sym eq)
      refl refl
      (related-values-return
        vVᴵ
        (precise-value
          (ClosureProof.value-imprecision-endpoints related))
        (λ i i≤j → value-imprecision-downward-to i≤j related)))

------------------------------------------------------------------------
-- The imprecise embedding commutes with body-level replacement
------------------------------------------------------------------------

embI-replace-body-eq : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W) (B : Ty (suc Δᴵ))
  → embedImpreciseBody (core W)
      (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B)
    ≡ replaceTy (Fin.suc (center s))
        (⇑ᵗ (embedImprecise (core W) (slotRᴵ s)))
        (embedImpreciseBody (core W) B)
embI-replace-body-eq W s B = trans
  (renameᵗ-replaceTy
    (extᵗ (toRenameᵗ (impreciseEmbedding (core W))))
    (ext-injective
      (toRenameᵗ-injective (impreciseEmbedding (core W))))
    (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B)
  (cong₂
    (λ Z R → replaceTy Z R (embedImpreciseBody (core W) B))
    (cong Fin.suc (impreciseAligned (atom s)))
    (renameᵗ-shift
      (toRenameᵗ (impreciseEmbedding (core W))) (slotRᴵ s)))

------------------------------------------------------------------------
-- At a fun- or ∀-shaped type the ★ exemption is vacuous
------------------------------------------------------------------------

shape-star-∉ : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    {Bᴵ : Ty Δᴵ} {Aᴵ : Ty Δᶜ} {P : Set}
  → UniShape Bᴵ
  → embedImprecise (core W) Bᴵ ≡ Aᴵ
  → (Aᴵ ≡ ★) ⊎ P
  → P
shape-star-∉ W shape-fun sourceᴵ (inj₁ star-eq)
    with trans sourceᴵ star-eq
shape-star-∉ W shape-fun sourceᴵ (inj₁ star-eq) | ()
shape-star-∉ W shape-all sourceᴵ (inj₁ star-eq)
    with trans sourceᴵ star-eq
shape-star-∉ W shape-all sourceᴵ (inj₁ star-eq) | ()
shape-star-∉ W shape sourceᴵ (inj₂ x) = x

------------------------------------------------------------------------
-- The canonical right-replaced derivations
------------------------------------------------------------------------

replace-right-⊑ : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W) {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → AliasAvoid★ᵖ (center s) p
  → center s ∉ᵗ Aᴾ
  → impEnv (core W) I.⊢ Aᴾ ⊑
      replaceTy (center s)
        (embedImprecise (core W) (slotRᴵ s)) Aᴵ
replace-right-⊑ W s p avoid no-occur =
  subst≡ (λ L → impEnv (core W) I.⊢ L ⊑ _)
    (replaceTy-absent (center s) _ no-occur)
    (replace★-⊑ (center s) (mode-eq s) (rep-related (atom s))
      p avoid)

replace-right-body-⊑ : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W) {Ac Bc : Ty (suc Δᶜ)}
    (p₀ : I.extᵐ (impEnv (core W)) I.⊢ Ac ⊑ Bc)
  → AliasAvoid★ᵖ (Fin.suc (center s)) p₀
  → Fin.suc (center s) ∉ᵗ Ac
  → I.extᵐ (impEnv (core W)) I.⊢ Ac ⊑
      replaceTy (Fin.suc (center s))
        (⇑ᵗ (embedImprecise (core W) (slotRᴵ s))) Bc
replace-right-body-⊑ W s p₀ avoid no-occur =
  subst≡ (λ L → I.extᵐ (impEnv (core W)) I.⊢ L ⊑ _)
    (replaceTy-absent (Fin.suc (center s)) _ no-occur)
    (replace★-⊑ (Fin.suc (center s))
      (I.ext-mode-paired {μ = impEnv (core W)} {v = I.X⊑X}
        {Z = center s} (mode-eq s))
      (shift-⊑ I.X⊑X (rep-related (atom s)))
      p₀ avoid)

replace-right-inst-body-⊑ : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (s : PairedSlot W) {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
  → AliasAvoid★ᵖ (Fin.suc (center s)) p₀
  → Fin.suc (center s) ∉ᵗ Ac
  → I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑
      ⇑ᵗ (replaceTy (center s)
        (embedImprecise (core W) (slotRᴵ s)) Bc)
replace-right-inst-body-⊑ W s {Ac = Ac} {Bc = Bc} p₀ avoid
    no-occur =
  subst≡ (λ L → I.instᵐ (impEnv (core W)) I.⊢ L ⊑ _)
    (replaceTy-absent (Fin.suc (center s)) _ no-occur)
    (subst≡ (λ R → I.instᵐ (impEnv (core W)) I.⊢
        replaceTy (Fin.suc (center s))
          (⇑ᵗ (embedPrecise (core W) (slotRᴾ s))) Ac ⊑ R)
      (sym (shift-replace (center s)
        (embedImprecise (core W) (slotRᴵ s)) Bc))
      (replace★-⊑ (Fin.suc (center s))
        (I.ext-mode-paired {μ = impEnv (core W)} {v = I.X⊑★}
          {Z = center s} (mode-eq s))
        (shift-⊑ I.X⊑★ (rep-related (atom s)))
        p₀ avoid))

------------------------------------------------------------------------
-- The right-universal cons
------------------------------------------------------------------------

-- A `∀⊑` source stores a replacement-closed right-universal family;
-- wrapping the imprecise endpoint conses the imprecise-only wrapper
-- onto the stored family and reindexes the clause to the replaced
-- derivation.  No recursion into the reveal induction is involved:
-- the wrapper's peels are discharged by the family itself.

imp-right-universal-value : ∀ (j : ℕ)
    {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
    {B₀ᴵ : Ty Δᴵ} {Acᵈ : Ty (suc Δᶜ)}
    {nonvar : NonVar Acᵈ} {occurs : Fin.zero ∈ᵗ Acᵈ}
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Acᵈ
      ⊑ ⇑ᵗ (embedImprecise (core W) B₀ᴵ))
  → AliasAvoid★ᵖ (Fin.suc (center s)) p₀
  → center s ∉ᵗ `∀ Acᵈ
  → UniShape B₀ᴵ
  → ∀ {Cᴵ : Ty Δᶜ}
      (q : impEnv (core W) I.⊢ `∀ Acᵈ ⊑ Cᴵ)
  → embedImprecise (core W)
      (replaceTy (slotXᴵ s) (slotRᴵ s) B₀ᴵ) ≡ Cᴵ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W (I.∀⊑ nonvar occurs p₀) j Vᴵ Vᴾ
  → ValueImprecision W q j
      (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ B₀ᴵ 〗) Vᴾ
imp-right-universal-value zero W s {nonvar = nonvar}
    {occurs = occurs} p₀ avoid no-occur shape q targetᴵ related =
  imp-reveal-endpoints W s (I.∀⊑ nonvar occurs p₀) refl q targetᴵ
    related (imprecise-value related ↑ reveal-value-of shape)
imp-right-universal-value (suc m) W s {B₀ᴵ = B₀ᴵ} {Acᵈ = Acᵈ}
    {nonvar = nonvar} {occurs = occurs}
    p₀ avoid (∉-all ∉ᵇ) shape q targetᴵ
    related@(endpointsₚ , Bᴾ* , Bᴵ* , embP* , embI* , fam)
    with renameᵗ-injective
           (toRenameᵗ-injective (impreciseEmbedding (core W)))
           embI*
imp-right-universal-value (suc m) W s {B₀ᴵ = B₀ᴵ} {Acᵈ = Acᵈ}
    {nonvar = nonvar} {occurs = occurs}
    p₀ avoid (∉-all ∉ᵇ) shape q targetᴵ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
    related@(endpointsₚ , Bᴾ* , .B₀ᴵ , embP* , embI* , fam)
    | refl =
  ClosureProof.value-imprecision-reindex q q̂c refl
    (trans (sym targetᴵ) ty-eq)
    (imp-reveal-endpoints W s (I.∀⊑ nonvar occurs p₀) refl q̂c
      ty-eq endpointsₚ
      (imprecise-value endpointsₚ ↑ reveal-value-of shape) ,
    Bᴾ* ,
    replaceTy (slotXᴵ s) (slotRᴵ s) B₀ᴵ ,
    embP* , ty-eq ,
    (λ {_} {_} {_} {W₂} W≼W₂ {B₂} {C₂} σ′ →
      fam-out {W′ = W₂} W≼W₂ {Bᴾ′ = B₂} {Bᴵ′ = C₂} σ′))
  where
  q̂₀ = replace-right-inst-body-⊑ W s p₀ avoid ∉ᵇ
  q̂c = I.∀⊑ nonvar occurs q̂₀
  ty-eq = embI-replace-eq W s B₀ᴵ

  Ac-eq : embedPreciseBody (core W) Bᴾ* ≡ Acᵈ
  Ac-eq = ty-all-injective embP*

  fam-out : RightUniversalFamily W q̂₀ Bᴾ*
      (replaceTy (slotXᴵ s) (slotRᴵ s) B₀ᴵ) (suc m)
      (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ B₀ᴵ 〗) Vᴾ
  fam-out {W′ = W′} W≼W′ {Bᴾ′ = Bᴾ′} {Bᴵ′ = Bᴵ′} σ =
    ClosureProof.right-universals-phantom
      (liftCenterDynamicBodyImprecision W≼W′ p₀)
      (liftCenterDynamicBodyImprecision W≼W′ q̂₀)
      (ClosureProof.right-universals-related-transport
        {W = W′} {p = liftCenterDynamicBodyImprecision W≼W′ p₀}
        {Bᴾ = Bᴾ′} {k = suc m}
        refl termᴵ-eq termᴾ-eq
        (fam W≼W′ (w ∷ σ‡)))
    where
    s′ = slot-future s W≼W′
    B₀ᴵ′ = liftImpreciseTy W≼W′ B₀ᴵ
    Bᴾ*′ = liftPreciseBody W≼W′ Bᴾ*

    imprecise-eq : liftImpreciseTy W≼W′
        (replaceTy (slotXᴵ s) (slotRᴵ s) B₀ᴵ)
        ≡ replaceTy (slotXᴵ s′) (slotRᴵ s′) B₀ᴵ′
    imprecise-eq = trans
      (liftImpreciseTy-replace W≼W′ (slotXᴵ s) (slotRᴵ s) B₀ᴵ)
      (cong₂ (λ Xv R → replaceTy Xv R B₀ᴵ′)
        (sym (slot-imprecise-variable-lift s W≼W′))
        (sym (slot-imprecise-rep-lift s W≼W′)))

    ∉ᵇ′ : Fin.suc (center s′) ∉ᵗ
        embedPreciseBody (core W′) Bᴾ*′
    ∉ᵇ′ = subst≡ (Fin.suc (center s′) ∉ᵗ_)
      (sym (embedPreciseBody-lift W≼W′ Bᴾ*))
      (lift-center-body-∉ᵗ W≼W′
        (subst≡ (Fin.suc (center s) ∉ᵗ_) (sym Ac-eq) ∉ᵇ))

    base-imp : BodyImprecision W Bᴾ*
        (replaceTy (slotXᴵ s) (slotRᴵ s) B₀ᴵ)
    base-imp = body-imprecision-of nonvar occurs q̂₀ embP* ty-eq

    av-fn : (j′ : BodyImprecision W′ Bᴾ*′ B₀ᴵ′)
      → AliasAvoid★ᵖ (Fin.suc (center s′)) (bodyP j′)
    av-fn j′ = alias-avoid★-any
      (liftCenterDynamicBodyImprecision W≼W′ p₀) (bodyP j′)
      (trans (cong (liftCenterBody W≼W′) (sym Ac-eq))
        (sym (embedPreciseBody-lift W≼W′ Bᴾ*)))
      (trans (liftCenterBody-shift W≼W′
        (embedImprecise (core W) B₀ᴵ))
        (cong ⇑ᵗ (sym (embedImprecise-lift W≼W′ B₀ᴵ))))
      (alias-avoid★-lift-dynamic-body W≼W′ (center s) p₀ avoid)

    w : UniWrap W′ Bᴾ*′ B₀ᴵ′ Bᴾ*′
        (replaceTy (slotXᴵ s′) (slotRᴵ s′) B₀ᴵ′)
    w = reveal-imprecise s′ Bᴾ*′ B₀ᴵ′ (shape-lift W≼W′ shape)
      ∉ᵇ′
      (body-imprecision-subst-imp imprecise-eq
        (body-imprecision-future W≼W′ base-imp))
      av-fn

    σ‡ : UniWraps W′ Bᴾ*′
        (replaceTy (slotXᴵ s′) (slotRᴵ s′) B₀ᴵ′) Bᴾ′ Bᴵ′
    σ‡ = subst≡
      (λ C → UniWraps W′ Bᴾ*′ C Bᴾ′ Bᴵ′) imprecise-eq σ

    termᴾ-eq : wrapTermᴾ (w ∷ σ‡) (liftPreciseTerm W≼W′ Vᴾ)
        ≡ wrapTermᴾ σ (liftPreciseTerm W≼W′ Vᴾ)
    termᴾ-eq = wrapTermᴾ-subst-imp imprecise-eq σ
      (liftPreciseTerm W≼W′ Vᴾ)

    termᴵ-eq : wrapTermᴵ (w ∷ σ‡) (liftImpreciseTerm W≼W′ Vᴵ)
        ≡ wrapTermᴵ σ (liftImpreciseTerm W≼W′
            (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ B₀ᴵ 〗))
    termᴵ-eq = trans
      (wrapTermᴵ-subst-imp imprecise-eq σ
        (liftImpreciseTerm W≼W′ Vᴵ
          ↑ 〖 slotXᴵ s′ , slotRᴵ s′ ↑ B₀ᴵ′ 〗))
      (cong (wrapTermᴵ σ)
        (sym (lifted-reveal-imprecise s W≼W′ Vᴵ B₀ᴵ)))

imp-conceal-right-universal-value : ∀ (j : ℕ)
    {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
    {B₀ᴵ : Ty Δᴵ} {Acᵈ : Ty (suc Δᶜ)}
    {nonvar : NonVar Acᵈ} {occurs : Fin.zero ∈ᵗ Acᵈ}
    (p₀ : I.instᵐ (impEnv (core W)) I.⊢ Acᵈ
      ⊑ ⇑ᵗ (embedImprecise (core W) B₀ᴵ))
  → AliasAvoid★ᵖ (Fin.suc (center s)) p₀
  → center s ∉ᵗ `∀ Acᵈ
  → UniShape B₀ᴵ
  → ∀ {Cᴵ : Ty Δᶜ}
      (q : impEnv (core W) I.⊢ `∀ Acᵈ ⊑ Cᴵ)
  → embedImprecise (core W)
      (replaceTy (slotXᴵ s) (slotRᴵ s) B₀ᴵ) ≡ Cᴵ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W q j Vᴵ Vᴾ
  → ValueImprecision W (I.∀⊑ nonvar occurs p₀) j
      (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) B₀ᴵ) Vᴾ
imp-conceal-right-universal-value zero W s {nonvar = nonvar}
    {occurs = occurs} p₀ avoid no-occur shape q targetᴵ related =
  imp-conceal-endpoints W s (I.∀⊑ nonvar occurs p₀) refl q
    targetᴵ related
    (imprecise-value related ↓ conceal-value-of shape)
imp-conceal-right-universal-value (suc m) W s {B₀ᴵ = B₀ᴵ}
    {Acᵈ = Acᵈ} {nonvar = nonvar} {occurs = occurs}
    p₀ avoid (∉-all ∉ᵇ) shape q targetᴵ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    with ClosureProof.value-imprecision-reindex
           (I.∀⊑ nonvar occurs
             (replace-right-inst-body-⊑ W s p₀ avoid ∉ᵇ))
           q refl
           (trans (sym (embI-replace-eq W s B₀ᴵ)) targetᴵ)
           related
imp-conceal-right-universal-value (suc m) W s {B₀ᴵ = B₀ᴵ}
    {Acᵈ = Acᵈ} {nonvar = nonvar} {occurs = occurs}
    p₀ avoid (∉-all ∉ᵇ) shape q targetᴵ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    | (endpointsʳ , Bᴾ* , Bᴵ*ʳ , embP* , embI*ʳ , fam-r)
    with renameᵗ-injective
           (toRenameᵗ-injective (impreciseEmbedding (core W)))
           (trans embI*ʳ (sym (embI-replace-eq W s B₀ᴵ)))
imp-conceal-right-universal-value (suc m) W s {B₀ᴵ = B₀ᴵ}
    {Acᵈ = Acᵈ} {nonvar = nonvar} {occurs = occurs}
    p₀ avoid (∉-all ∉ᵇ) shape q targetᴵ
    {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
    | (endpointsʳ , Bᴾ* ,
       .(replaceTy (slotXᴵ s) (slotRᴵ s) B₀ᴵ) ,
       embP* , embI*ʳ , fam-r)
    | refl =
  imp-conceal-endpoints W s (I.∀⊑ nonvar occurs p₀) refl q
    targetᴵ
    (ClosureProof.value-imprecision-endpoints
      {W = W} {p = q} {k = suc m} related)
    (imprecise-value
      (ClosureProof.value-imprecision-endpoints
        {W = W} {p = q} {k = suc m} related)
      ↓ conceal-value-of shape) ,
  Bᴾ* , B₀ᴵ , embP* , refl ,
  (λ {_} {_} {_} {W₂} W≼W₂ {B₂} {C₂} σ′ →
    fam-out {W′ = W₂} W≼W₂ {Bᴾ′ = B₂} {Bᴵ′ = C₂} σ′)
  where
  q̂₀ = replace-right-inst-body-⊑ W s p₀ avoid ∉ᵇ
  ty-eq = embI-replace-eq W s B₀ᴵ

  Ac-eq : embedPreciseBody (core W) Bᴾ* ≡ Acᵈ
  Ac-eq = ty-all-injective embP*

  fam-out : RightUniversalFamily W p₀ Bᴾ* B₀ᴵ (suc m)
      (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) B₀ᴵ) Vᴾ
  fam-out {W′ = W′} W≼W′ {Bᴾ′ = Bᴾ′} {Bᴵ′ = Bᴵ′} σ =
    ClosureProof.right-universals-phantom
      (liftCenterDynamicBodyImprecision W≼W′ q̂₀)
      (liftCenterDynamicBodyImprecision W≼W′ p₀)
      (ClosureProof.right-universals-related-transport
        {W = W′} {p = liftCenterDynamicBodyImprecision W≼W′ q̂₀}
        {Bᴾ = Bᴾ′} {k = suc m}
        refl termᴵ-eq termᴾ-eq
        (fam-r W≼W′ σ†))
    where
    s′ = slot-future s W≼W′
    B₀ᴵ′ = liftImpreciseTy W≼W′ B₀ᴵ
    Bᴾ*′ = liftPreciseBody W≼W′ Bᴾ*

    imprecise-eq : liftImpreciseTy W≼W′
        (replaceTy (slotXᴵ s) (slotRᴵ s) B₀ᴵ)
        ≡ replaceTy (slotXᴵ s′) (slotRᴵ s′) B₀ᴵ′
    imprecise-eq = trans
      (liftImpreciseTy-replace W≼W′ (slotXᴵ s) (slotRᴵ s) B₀ᴵ)
      (cong₂ (λ Xv R → replaceTy Xv R B₀ᴵ′)
        (sym (slot-imprecise-variable-lift s W≼W′))
        (sym (slot-imprecise-rep-lift s W≼W′)))

    ∉ᵇ′ : Fin.suc (center s′) ∉ᵗ
        embedPreciseBody (core W′) Bᴾ*′
    ∉ᵇ′ = subst≡ (Fin.suc (center s′) ∉ᵗ_)
      (sym (embedPreciseBody-lift W≼W′ Bᴾ*))
      (lift-center-body-∉ᵗ W≼W′
        (subst≡ (Fin.suc (center s) ∉ᵗ_) (sym Ac-eq) ∉ᵇ))

    base-imp : BodyImprecision W Bᴾ* B₀ᴵ
    base-imp = body-imprecision-of nonvar occurs p₀ embP* refl

    av-fn : (j′ : BodyImprecision W′ Bᴾ*′ B₀ᴵ′)
      → AliasAvoid★ᵖ (Fin.suc (center s′)) (bodyP j′)
    av-fn j′ = alias-avoid★-any
      (liftCenterDynamicBodyImprecision W≼W′ p₀) (bodyP j′)
      (trans (cong (liftCenterBody W≼W′) (sym Ac-eq))
        (sym (embedPreciseBody-lift W≼W′ Bᴾ*)))
      (trans (liftCenterBody-shift W≼W′
        (embedImprecise (core W) B₀ᴵ))
        (cong ⇑ᵗ (sym (embedImprecise-lift W≼W′ B₀ᴵ))))
      (alias-avoid★-lift-dynamic-body W≼W′ (center s) p₀ avoid)

    w : UniWrap W′ Bᴾ*′
        (replaceTy (slotXᴵ s′) (slotRᴵ s′) B₀ᴵ′) Bᴾ*′ B₀ᴵ′
    w = conceal-imprecise s′ Bᴾ*′ B₀ᴵ′ (shape-lift W≼W′ shape)
      ∉ᵇ′ (body-imprecision-future W≼W′ base-imp) av-fn

    σ† : UniWraps W′ Bᴾ*′
        (liftImpreciseTy W≼W′
          (replaceTy (slotXᴵ s) (slotRᴵ s) B₀ᴵ)) Bᴾ′ Bᴵ′
    σ† = subst≡
      (λ C → UniWraps W′ Bᴾ*′ C Bᴾ′ Bᴵ′)
      (sym imprecise-eq) (w ∷ σ)

    termᴾ-eq : wrapTermᴾ σ† (liftPreciseTerm W≼W′ Vᴾ)
        ≡ wrapTermᴾ σ (liftPreciseTerm W≼W′ Vᴾ)
    termᴾ-eq = wrapTermᴾ-subst-imp (sym imprecise-eq) (w ∷ σ)
      (liftPreciseTerm W≼W′ Vᴾ)

    termᴵ-eq : wrapTermᴵ σ† (liftImpreciseTerm W≼W′ Vᴵ)
        ≡ wrapTermᴵ σ (liftImpreciseTerm W≼W′
            (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) B₀ᴵ))
    termᴵ-eq = trans
      (wrapTermᴵ-subst-imp (sym imprecise-eq) (w ∷ σ)
        (liftImpreciseTerm W≼W′ Vᴵ))
      (cong (wrapTermᴵ σ)
        (sym (lifted-conceal-imprecise s W≼W′ Vᴵ B₀ᴵ)))

------------------------------------------------------------------------
-- The one-sided imprecise reveal and conceal
------------------------------------------------------------------------

-- The recursion is by the derivation size: the alias case unfolds to
-- its premise, the arrow case to its components, and the lifted
-- Kripke re-entries preserve the size.

mutual
  imp-reveal-go : ∀ (fuel j : ℕ)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
      {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → AliasAvoid★ᵖ (center s) p
    → sizeᵖ p ≤ fuel
    → center s ∉ᵗ Aᴾ
    → embedImprecise (core W) Bᴵ ≡ Aᴵ
    → ∀ {Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Aᴾ ⊑ Cᴵ)
    → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
        ≡ Cᴵ
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W p j Vᴵ Vᴾ
    → ComputationsRelated W (FutureValueRelation q) j
        (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗) Vᴾ
  imp-reveal-go fuel j W s {Bᴵ = ＇ Y} p avoid size no-occur
      sourceᴵ q targetᴵ related with slotXᴵ s ≟ Y
  imp-reveal-go fuel j W s {Bᴵ = ＇ Y} p avoid size no-occur
      sourceᴵ q targetᴵ related | no _ =
    imp-identity-reveal W p q (trans (sym sourceᴵ) targetᴵ)
      (＇ Y) related
  imp-reveal-go fuel j W s {Bᴵ = ＇ Y} p avoid size no-occur
      sourceᴵ q targetᴵ related | yes refl
      with sourceᴵ
  imp-reveal-go fuel j W s {Bᴵ = ＇ Y} I.X⊑X avoid size
      (∉-var neq) sourceᴵ q targetᴵ related | yes refl | refl =
    ⊥-elim (≢ᶠ→≢ neq (sym (impreciseAligned (atom s))))
  imp-reveal-go fuel j W s {Bᴵ = ＇ Y}
      (I.alias eq′ p′) (inj₁ star-eq , av′) size
      no-occur sourceᴵ q targetᴵ related | yes refl | refl
      with star-eq
  imp-reveal-go fuel j W s {Bᴵ = ＇ Y}
      (I.alias eq′ p′) (inj₁ star-eq , av′) size
      no-occur sourceᴵ q targetᴵ related | yes refl | refl | ()
  imp-reveal-go fuel j W s {Bᴵ = ＇ Y}
      (I.alias eq′ p′) (inj₂ c∉T , av′) size
      no-occur sourceᴵ q targetᴵ related | yes refl | refl =
    ⊥-elim (PI.∈∉-⊥
      (subst≡ (λ T′ → center s ∉ᵗ T′)
        (paired-var-right-⊑ (mode-eq s) p′
          (cong ＇_ (impreciseAligned (atom s))) av′)
        c∉T)
      var-∈)
  imp-reveal-go fuel j W s {Bᴵ = ＇ Y}
      (I.∀⊑ nonvar occurs p₀) avoid size
      no-occur sourceᴵ q targetᴵ related | yes refl | refl
      with paired-var-right-⊑ (mode-eq s)
             (I.∀⊑ nonvar occurs p₀)
             (cong ＇_ (impreciseAligned (atom s))) avoid
  imp-reveal-go fuel j W s {Bᴵ = ＇ Y}
      (I.∀⊑ nonvar occurs p₀) avoid size
      no-occur sourceᴵ q targetᴵ related | yes refl | refl | ()
  imp-reveal-go fuel j W s {Bᴵ = ‵ ι} p avoid size no-occur
      sourceᴵ q targetᴵ related =
    imp-identity-reveal W p q (trans (sym sourceᴵ) targetᴵ)
      (‵ ι) related
  imp-reveal-go fuel j W s {Bᴵ = ★} p avoid size no-occur
      sourceᴵ q targetᴵ related =
    imp-identity-reveal W p q (trans (sym sourceᴵ) targetᴵ)
      ★ related
  imp-reveal-go fuel j W s {Bᴵ = A₀ᴵ ⇒ B₀ᴵ} p avoid size
      no-occur sourceᴵ q targetᴵ related =
    related-values-return
      (imprecise-value endpoints ↑ reveal-value-of shape-fun)
      (precise-value endpoints)
      (λ i i≤j → imp-value-go fuel i W s shape-fun p avoid
        size no-occur sourceᴵ q targetᴵ
        (value-imprecision-downward-to i≤j related))
    where
    endpoints = ClosureProof.value-imprecision-endpoints related
  imp-reveal-go fuel j W s {Bᴵ = `∀ B₀ᴵ} p avoid size
      no-occur sourceᴵ q targetᴵ related =
    related-values-return
      (imprecise-value endpoints ↑ reveal-value-of shape-all)
      (precise-value endpoints)
      (λ i i≤j → imp-value-go fuel i W s shape-all p avoid
        size no-occur sourceᴵ q targetᴵ
        (value-imprecision-downward-to i≤j related))
    where
    endpoints = ClosureProof.value-imprecision-endpoints related

  imp-conceal-go : ∀ (fuel j : ℕ)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
      {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → AliasAvoid★ᵖ (center s) p
    → sizeᵖ p ≤ fuel
    → center s ∉ᵗ Aᴾ
    → embedImprecise (core W) Bᴵ ≡ Aᴵ
    → ∀ {Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Aᴾ ⊑ Cᴵ)
    → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
        ≡ Cᴵ
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W q j Vᴵ Vᴾ
    → ComputationsRelated W (FutureValueRelation p) j
        (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ) Vᴾ
  imp-conceal-go fuel j W s {Bᴵ = ＇ Y} p avoid size no-occur
      sourceᴵ q targetᴵ related with slotXᴵ s ≟ Y
  imp-conceal-go fuel j W s {Bᴵ = ＇ Y} p avoid size no-occur
      sourceᴵ q targetᴵ related | no _ =
    imp-identity-conceal W p q (trans (sym sourceᴵ) targetᴵ)
      (＇ Y) related
  imp-conceal-go fuel j W s {Bᴵ = ＇ Y} p avoid size no-occur
      sourceᴵ q targetᴵ related | yes refl
      with sourceᴵ
  imp-conceal-go fuel j W s {Bᴵ = ＇ Y} I.X⊑X avoid size
      (∉-var neq) sourceᴵ q targetᴵ related | yes refl | refl =
    ⊥-elim (≢ᶠ→≢ neq (sym (impreciseAligned (atom s))))
  imp-conceal-go fuel j W s {Bᴵ = ＇ Y}
      (I.alias eq′ p′) (inj₁ star-eq , av′) size
      no-occur sourceᴵ q targetᴵ related | yes refl | refl
      with star-eq
  imp-conceal-go fuel j W s {Bᴵ = ＇ Y}
      (I.alias eq′ p′) (inj₁ star-eq , av′) size
      no-occur sourceᴵ q targetᴵ related | yes refl | refl | ()
  imp-conceal-go fuel j W s {Bᴵ = ＇ Y}
      (I.alias eq′ p′) (inj₂ c∉T , av′) size
      no-occur sourceᴵ q targetᴵ related | yes refl | refl =
    ⊥-elim (PI.∈∉-⊥
      (subst≡ (λ T′ → center s ∉ᵗ T′)
        (paired-var-right-⊑ (mode-eq s) p′
          (cong ＇_ (impreciseAligned (atom s))) av′)
        c∉T)
      var-∈)
  imp-conceal-go fuel j W s {Bᴵ = ＇ Y}
      (I.∀⊑ nonvar occurs p₀) avoid size
      no-occur sourceᴵ q targetᴵ related | yes refl | refl
      with paired-var-right-⊑ (mode-eq s)
             (I.∀⊑ nonvar occurs p₀)
             (cong ＇_ (impreciseAligned (atom s))) avoid
  imp-conceal-go fuel j W s {Bᴵ = ＇ Y}
      (I.∀⊑ nonvar occurs p₀) avoid size
      no-occur sourceᴵ q targetᴵ related | yes refl | refl | ()
  imp-conceal-go fuel j W s {Bᴵ = ‵ ι} p avoid size no-occur
      sourceᴵ q targetᴵ related =
    imp-identity-conceal W p q (trans (sym sourceᴵ) targetᴵ)
      (‵ ι) related
  imp-conceal-go fuel j W s {Bᴵ = ★} p avoid size no-occur
      sourceᴵ q targetᴵ related =
    imp-identity-conceal W p q (trans (sym sourceᴵ) targetᴵ)
      ★ related
  imp-conceal-go fuel j W s {Bᴵ = A₀ᴵ ⇒ B₀ᴵ} p avoid size
      no-occur sourceᴵ q targetᴵ related =
    related-values-return
      (imprecise-value endpoints ↓ conceal-value-of shape-fun)
      (precise-value endpoints)
      (λ i i≤j → imp-conceal-value-go fuel i W s shape-fun p
        avoid size no-occur sourceᴵ q targetᴵ
        (value-imprecision-downward-to i≤j related))
    where
    endpoints = ClosureProof.value-imprecision-endpoints related
  imp-conceal-go fuel j W s {Bᴵ = `∀ B₀ᴵ} p avoid size
      no-occur sourceᴵ q targetᴵ related =
    related-values-return
      (imprecise-value endpoints ↓ conceal-value-of shape-all)
      (precise-value endpoints)
      (λ i i≤j → imp-conceal-value-go fuel i W s shape-all p
        avoid size no-occur sourceᴵ q targetᴵ
        (value-imprecision-downward-to i≤j related))
    where
    endpoints = ClosureProof.value-imprecision-endpoints related

  imp-value-go : ∀ (fuel j : ℕ)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
      {Bᴵ : Ty Δᴵ} (shape : UniShape Bᴵ) {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → AliasAvoid★ᵖ (center s) p
    → sizeᵖ p ≤ fuel
    → center s ∉ᵗ Aᴾ
    → embedImprecise (core W) Bᴵ ≡ Aᴵ
    → ∀ {Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Aᴾ ⊑ Cᴵ)
    → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
        ≡ Cᴵ
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W p j Vᴵ Vᴾ
    → ValueImprecision W q j
        (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗) Vᴾ
  imp-value-go fuel zero W s shape p avoid size no-occur
      sourceᴵ q targetᴵ related =
    imp-reveal-endpoints W s p sourceᴵ q targetᴵ related
      (imprecise-value related ↑ reveal-value-of shape)
  imp-value-go (suc fuel) (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      (I.⇒⊑⇒ p₁ p₂) (avoid₁ , avoid₂) size (∉-fun ∉₁ ∉₂)
      sourceᴵ q targetᴵ related with sourceᴵ
  imp-value-go (suc fuel) (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      (I.⇒⊑⇒ p₁ p₂) (avoid₁ , avoid₂) size (∉-fun ∉₁ ∉₂)
      sourceᴵ q targetᴵ related | refl =
    imp-arrow-value fuel (suc m) W s p₁ p₂ avoid₁ avoid₂
      (sizeᵖ-bound-left size) (sizeᵖ-bound-right size) ∉₁ ∉₂
      q targetᴵ related
  imp-value-go zero (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      (I.⇒⊑⇒ p₁ p₂) avoid () no-occur sourceᴵ q targetᴵ related
  imp-value-go (suc fuel) (suc m) W s shape
      (I.alias eq′ {notSelf} p′) (leaf , av′) (s≤s size′) no-occur
      sourceᴵ q targetᴵ related =
    imp-alias-value fuel (suc m) W s shape eq′ {notSelf} p′
      leaf av′ size′ sourceᴵ q targetᴵ related
  imp-value-go zero (suc m) W s shape
      (I.alias eq′ p′) avoid () no-occur sourceᴵ q targetᴵ related
  imp-value-go fuel (suc m) W s shape
      (I.∀⊑ nonvar occurs p₀) avoid size no-occur
      sourceᴵ q targetᴵ related
      with sourceᴵ
  imp-value-go fuel (suc m) W s shape
      (I.∀⊑ nonvar occurs p₀) avoid size no-occur
      sourceᴵ q targetᴵ related | refl =
    imp-right-universal-value (suc m) W s p₀ avoid no-occur
      shape q targetᴵ related
  imp-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      (I.∀⊑∀ p₀) avoid size no-occur sourceᴵ q targetᴵ related
      with sourceᴵ
  imp-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      (I.∀⊑∀ p₀) avoid size no-occur sourceᴵ q targetᴵ related
      | refl =
    imp-universal-value (suc m) W s p₀ avoid no-occur
      q targetᴵ related
  imp-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      I.bot-elim avoid size no-occur sourceᴵ q targetᴵ related =
    ⊥-elim (no-precise-bottom-value {p = I.bot-elim} {k = suc m}
      related)
  imp-value-go fuel (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      I.★⊑★ avoid size no-occur () q targetᴵ related
  imp-value-go fuel (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      I.ι⊑ι avoid size no-occur () q targetᴵ related
  imp-value-go fuel (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      I.X⊑X avoid size no-occur () q targetᴵ related
  imp-value-go fuel (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      (I.∀⊑∀ p₀) avoid size no-occur () q targetᴵ related
  imp-value-go fuel (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      (I.⇒⊑★ p₀₁ p₀₂) avoid size no-occur () q targetᴵ related
  imp-value-go fuel (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      I.ι⊑★ avoid size no-occur () q targetᴵ related
  imp-value-go fuel (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      (I.X⊑★ mode) avoid size no-occur () q targetᴵ related
  imp-value-go fuel (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      I.∀★⊑★ avoid size no-occur () q targetᴵ related
  imp-value-go fuel (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      (I.∀⊑★ nonstar p₀) avoid size no-occur () q targetᴵ related
  imp-value-go fuel (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      I.bot-elim avoid size no-occur () q targetᴵ related
  imp-value-go fuel (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      I.bot⊑★ avoid size no-occur () q targetᴵ related
  imp-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      I.★⊑★ avoid size no-occur () q targetᴵ related
  imp-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      I.ι⊑ι avoid size no-occur () q targetᴵ related
  imp-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      I.X⊑X avoid size no-occur () q targetᴵ related
  imp-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      (I.⇒⊑⇒ p₀₁ p₀₂) avoid size no-occur () q targetᴵ related
  imp-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      (I.⇒⊑★ p₀₁ p₀₂) avoid size no-occur () q targetᴵ related
  imp-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      I.ι⊑★ avoid size no-occur () q targetᴵ related
  imp-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      (I.X⊑★ mode) avoid size no-occur () q targetᴵ related
  imp-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      I.∀★⊑★ avoid size no-occur () q targetᴵ related
  imp-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      (I.∀⊑★ nonstar p₀) avoid size no-occur () q targetᴵ related
  imp-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      I.bot⊑★ avoid size no-occur () q targetᴵ related

  -- The wrapped function value: the imprecise endpoint redistributes
  -- the wrapper over the application.

  imp-arrow-value : ∀ (fuel j : ℕ)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
      {A₀ᴵ B₀ᴵ : Ty Δᴵ} {P₁ P₂ : Ty Δᶜ}
      (p₁ : impEnv (core W) I.⊢ P₁
        ⊑ embedImprecise (core W) A₀ᴵ)
      (p₂ : impEnv (core W) I.⊢ P₂
        ⊑ embedImprecise (core W) B₀ᴵ)
    → AliasAvoid★ᵖ (center s) p₁
    → AliasAvoid★ᵖ (center s) p₂
    → sizeᵖ p₁ ≤ fuel
    → sizeᵖ p₂ ≤ fuel
    → center s ∉ᵗ P₁
    → center s ∉ᵗ P₂
    → ∀ {Cᴵ : Ty Δᶜ}
      (q : impEnv (core W) I.⊢ (P₁ ⇒ P₂) ⊑ Cᴵ)
    → embedImprecise (core W)
        (replaceTy (slotXᴵ s) (slotRᴵ s) (A₀ᴵ ⇒ B₀ᴵ)) ≡ Cᴵ
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W (I.⇒⊑⇒ p₁ p₂) j Vᴵ Vᴾ
    → ValueImprecision W q j
        (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ A₀ᴵ ⇒ B₀ᴵ 〗) Vᴾ
  imp-arrow-value fuel zero W s p₁ p₂ avoid₁ avoid₂
      size₁ size₂ ∉₁ ∉₂ q targetᴵ related =
    imp-reveal-endpoints W s (I.⇒⊑⇒ p₁ p₂) refl q targetᴵ related
      (imprecise-value related ↑ reveal-value-of shape-fun)
  imp-arrow-value fuel (suc i) W s {A₀ᴵ = A₀ᴵ} {B₀ᴵ = B₀ᴵ}
      p₁ p₂ avoid₁ avoid₂ size₁ size₂ ∉₁ ∉₂
      q targetᴵ {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related =
    ClosureProof.value-imprecision-reindex q q̂c refl
      (trans (sym targetᴵ) (embI-replace-eq W s (A₀ᴵ ⇒ B₀ᴵ)))
      (imp-reveal-endpoints W s (I.⇒⊑⇒ p₁ p₂) refl q̂c
        (embI-replace-eq W s (A₀ᴵ ⇒ B₀ᴵ)) endpointsₚ
        (imprecise-value endpointsₚ ↑ reveal-value-of shape-fun) ,
      functions (suc i) ≤-refl related)
    where
    q̂₁ = replace-right-⊑ W s p₁ avoid₁ ∉₁
    q̂₂ = replace-right-⊑ W s p₂ avoid₂ ∉₂
    q̂c = I.⇒⊑⇒ q̂₁ q̂₂

    endpointsₚ = ClosureProof.value-imprecision-endpoints
      {W = W} {p = I.⇒⊑⇒ p₁ p₂} {k = suc i}
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related

    functions : ∀ (n : ℕ) → n ≤ suc i
      → ValueImprecision W (I.⇒⊑⇒ p₁ p₂) n Vᴵ Vᴾ
      → FunctionsRelated W q̂₁ q̂₂ n
          (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ A₀ᴵ ⇒ B₀ᴵ 〗) Vᴾ
    functions zero n≤ rel = tt
    functions (suc n) sn≤ rel =
      (λ W′ W≼W′ argument-related →
        imp-arrow-head fuel n W s p₁ p₂ avoid₁ avoid₂
          size₁ size₂ ∉₁ ∉₂ q̂₁ q̂₂
          (embI-replace-eq W s A₀ᴵ) (embI-replace-eq W s B₀ᴵ)
          rel W′ W≼W′ argument-related) ,
      functions n (≤-trans (n≤1+n n) sn≤)
        (value-imprecision-downward-to
          {W = W} {p = I.⇒⊑⇒ p₁ p₂} {j = n} {k = suc n}
          {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (n≤1+n n) rel)

  -- One head of the wrapped function value.

  imp-arrow-head : ∀ (fuel m : ℕ)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
      {A₀ᴵ B₀ᴵ : Ty Δᴵ} {P₁ P₂ : Ty Δᶜ}
      (p₁ : impEnv (core W) I.⊢ P₁
        ⊑ embedImprecise (core W) A₀ᴵ)
      (p₂ : impEnv (core W) I.⊢ P₂
        ⊑ embedImprecise (core W) B₀ᴵ)
    → AliasAvoid★ᵖ (center s) p₁
    → AliasAvoid★ᵖ (center s) p₂
    → sizeᵖ p₁ ≤ fuel
    → sizeᵖ p₂ ≤ fuel
    → center s ∉ᵗ P₁
    → center s ∉ᵗ P₂
    → ∀ {Cᴵ₁ Cᴵ₂ : Ty Δᶜ}
      (q₁ : impEnv (core W) I.⊢ P₁ ⊑ Cᴵ₁)
      (q₂ : impEnv (core W) I.⊢ P₂ ⊑ Cᴵ₂)
    → embedImprecise (core W)
        (replaceTy (slotXᴵ s) (slotRᴵ s) A₀ᴵ) ≡ Cᴵ₁
    → embedImprecise (core W)
        (replaceTy (slotXᴵ s) (slotRᴵ s) B₀ᴵ) ≡ Cᴵ₂
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W (I.⇒⊑⇒ p₁ p₂) (suc m) Vᴵ Vᴾ
    → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
        (W≼W′ : Future W W′) {Uᴵ : Term Δᴵ′} {Uᴾ : Term Δᴾ′}
    → ValueImprecision W′ (liftCenterImprecision W≼W′ q₁) (suc m)
        Uᴵ Uᴾ
    → ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₂))
        (suc m)
        (liftImpreciseTerm W≼W′
          (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ A₀ᴵ ⇒ B₀ᴵ 〗) · Uᴵ)
        (liftPreciseTerm W≼W′ Vᴾ · Uᴾ)
  imp-arrow-head fuel m W s {A₀ᴵ = A₀ᴵ} {B₀ᴵ = B₀ᴵ}
      p₁ p₂ avoid₁ avoid₂ size₁ size₂ ∉₁ ∉₂
      q₁ q₂ target₁ target₂ {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} function-related
      W′ W≼W′ {Uᴵ = Uᴵ} {Uᴾ = Uᴾ} argument-related =
    ClosureProof.computations-related-reindex
      (liftCenterImprecision W≼W′ q₂) (liftCenterImprecision W≼W′ q₂)
      refl refl (sym imprecise-redex-eq) refl expanded
    where
    s′ = slot-future s W≼W′
    A′ = liftImpreciseTy W≼W′ A₀ᴵ
    B′ = liftImpreciseTy W≼W′ B₀ᴵ
    cᴵ = makeConceal (slotXᴵ s′) (slotRᴵ s′) A′
    dᴵ = 〖 slotXᴵ s′ , slotRᴵ s′ ↑ B′ 〗
    Vᴵ′ = liftImpreciseTerm W≼W′ Vᴵ
    Vᴾ′ = liftPreciseTerm W≼W′ Vᴾ

    imprecise-redex-eq :
        liftImpreciseTerm W≼W′
          (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ A₀ᴵ ⇒ B₀ᴵ 〗) · Uᴵ
        ≡ (Vᴵ′ ↑ (cᴵ ↦↑ dᴵ)) · Uᴵ
    imprecise-redex-eq
        rewrite lifted-reveal-imprecise s W≼W′ Vᴵ (A₀ᴵ ⇒ B₀ᴵ)
              | liftImpreciseTy-arrow W≼W′ A₀ᴵ B₀ᴵ = refl

    argument-endpoints =
      ClosureProof.value-imprecision-endpoints argument-related

    lifted-function : ValueImprecision W′
        (I.⇒⊑⇒ (liftCenterImprecision W≼W′ p₁)
          (liftCenterImprecision W≼W′ p₂)) (suc m) Vᴵ′ Vᴾ′
    lifted-function = ClosureProof.value-imprecision-reindex
      (I.⇒⊑⇒ (liftCenterImprecision W≼W′ p₁)
        (liftCenterImprecision W≼W′ p₂))
      (liftCenterImprecision W≼W′ (I.⇒⊑⇒ p₁ p₂))
      (sym (liftCenterTy-arrow W≼W′ _ _))
      (sym (liftCenterTy-arrow W≼W′ _ _))
      (ClosureProof.value-imprecision-future
        {W = W} {p = I.⇒⊑⇒ p₁ p₂} {k = suc m} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
        W≼W′ function-related)

    concealed : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ p₁))
        (suc m) (Uᴵ ↓ cᴵ) Uᴾ
    concealed = imp-conceal-go fuel (suc m) W′ s′
      (liftCenterImprecision W≼W′ p₁)
      (alias-avoid★-lift-center W≼W′ (center s) p₁ avoid₁)
      (subst≡ (_≤ fuel) (sym (lift-center-size W≼W′ p₁)) size₁)
      (lift-center-∉ᵗ W≼W′ ∉₁)
      (embedImprecise-lift W≼W′ A₀ᴵ)
      (liftCenterImprecision W≼W′ q₁)
      (trans
        (cong (embedImprecise (core W′))
          (replace-imprecise-lift s W≼W′ A₀ᴵ))
        (trans
          (embedImprecise-lift W≼W′
            (replaceTy (slotXᴵ s) (slotRᴵ s) A₀ᴵ))
          (cong (liftCenterTy W≼W′) target₁)))
      argument-related

    applied : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ p₂))
        (suc m) (Vᴵ′ · (Uᴵ ↓ cᴵ)) (Vᴾ′ · Uᴾ)
    applied = related-application-computation lifted-function
      concealed

    framed : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₂))
        (suc m) ((Vᴵ′ · (Uᴵ ↓ cᴵ)) ↑ dᴵ) (Vᴾ′ · Uᴾ)
    framed = imp-revealed-computations fuel (suc m) W′ s′
      (liftCenterImprecision W≼W′ p₂)
      (alias-avoid★-lift-center W≼W′ (center s) p₂ avoid₂)
      (subst≡ (_≤ fuel) (sym (lift-center-size W≼W′ p₂)) size₂)
      (lift-center-∉ᵗ W≼W′ ∉₂)
      (embedImprecise-lift W≼W′ B₀ᴵ)
      (liftCenterImprecision W≼W′ q₂)
      (trans
        (cong (embedImprecise (core W′))
          (replace-imprecise-lift s W≼W′ B₀ᴵ))
        (trans
          (embedImprecise-lift W≼W′
            (replaceTy (slotXᴵ s) (slotRᴵ s) B₀ᴵ))
          (cong (liftCenterTy W≼W′) target₂)))
      applied

    expanded : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₂))
        (suc m)
        ((Vᴵ′ ↑ (cᴵ ↦↑ dᴵ)) · Uᴵ) (Vᴾ′ · Uᴾ)
    expanded
        with reveal-fun-app-step-question
               {Σ = impreciseStore (core W′)} cᴵ dᴵ
               (imprecise-value function-endpoints)
               (imprecise-value argument-endpoints)
      where
      function-endpoints = ClosureProof.value-imprecision-endpoints
        {W = W′}
        {p = I.⇒⊑⇒ (liftCenterImprecision W≼W′ p₁)
          (liftCenterImprecision W≼W′ p₂)}
        {k = suc m} {Vᴵ = Vᴵ′} {Vᴾ = Vᴾ′} lifted-function
    expanded | vVᴵ , vUᴵ , step-eqᴵ =
      related-imprecise-keep-step-expand (λ ())
        (reveal-fun-app-value-none cᴵ dᴵ)
        (pure-step (β-reveal-⇒ vVᴵ vUᴵ)) step-eqᴵ framed

  -- The alias source: unfold the payload, wrap it, and rebuild the
  -- holding at the replaced premise.

  imp-alias-value : ∀ (fuel j : ℕ)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
      {Bᴵ : Ty Δᴵ} (shape : UniShape Bᴵ)
      {X : TyVar Δᶜ} {T Aᴵ : Ty Δᶜ}
      (eq′ : impEnv (core W) X ≡ I.X⊑ᵗ T)
      {notSelf : False (isVar? X Aᴵ)}
      (p′ : impEnv (core W) I.⊢ T ⊑ Aᴵ)
    → (Aᴵ ≡ ★) ⊎ (center s ∉ᵗ T)
    → AliasAvoid★ᵖ (center s) p′
    → sizeᵖ p′ ≤ fuel
    → embedImprecise (core W) Bᴵ ≡ Aᴵ
    → ∀ {Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ ＇ X ⊑ Cᴵ)
    → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
        ≡ Cᴵ
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W (I.alias eq′ {notSelf = notSelf} p′) j
        Vᴵ Vᴾ
    → ValueImprecision W q j
        (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗) Vᴾ
  imp-alias-value fuel zero W s shape eq′ {notSelf} p′
      leaf av′ size′ sourceᴵ q targetᴵ related =
    imp-reveal-endpoints W s (I.alias eq′ {notSelf = notSelf} p′)
      sourceᴵ q targetᴵ related
      (imprecise-value related ↑ reveal-value-of shape)
  imp-alias-value fuel (suc m) W s {Bᴵ = Bᴵ} shape
      {X = X} {Aᴵ = Aᴵ} eq′ {notSelf} p′ leaf av′ size′ sourceᴵ
      q targetᴵ (endpointsₚ , holds) =
    ClosureProof.value-imprecision-reindex q q̂c refl
      (trans (sym targetᴵ) target-eq)
      (imp-reveal-endpoints W s
        (I.alias eq′ {notSelf = notSelf} p′) sourceᴵ q̂c
        target-eq endpointsₚ
        (imprecise-value endpointsₚ ↑ reveal-value-of shape) ,
      alias-holds-imp-map (semanticEntry W X) eq′
        (λ {Uᴾ} rel →
          imp-value-go fuel (suc m) W s shape p′ av′ size′
            c∉T sourceᴵ q̂′ target-eq rel)
        holds)
    where
    c∉T = shape-star-∉ W shape sourceᴵ leaf

    q̂′ = replace-right-⊑ W s p′ av′ c∉T
    q̂c = I.alias eq′
      {notSelf = replace-alias-not-self★ (center s)
        (embedImprecise (core W) (slotRᴵ s)) c∉T p′ av′ notSelf}
      q̂′

    target-eq : embedImprecise (core W)
        (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
        ≡ replaceTy (center s)
            (embedImprecise (core W) (slotRᴵ s)) Aᴵ
    target-eq = trans (embI-replace-eq W s Bᴵ)
      (cong
        (replaceTy (center s)
          (embedImprecise (core W) (slotRᴵ s)))
        sourceᴵ)

  -- The two-sided universal source: cons the imprecise-only wrapper
  -- onto the stored family.

  imp-universal-value : ∀ (j : ℕ)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
      {B₀ᴵ : Ty (suc Δᴵ)} {Acᵇ : Ty (suc Δᶜ)}
      (p₀ : I.extᵐ (impEnv (core W)) I.⊢ Acᵇ
        ⊑ embedImpreciseBody (core W) B₀ᴵ)
    → AliasAvoid★ᵖ (Fin.suc (center s)) p₀
    → center s ∉ᵗ `∀ Acᵇ
    → ∀ {Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ `∀ Acᵇ ⊑ Cᴵ)
    → embedImprecise (core W)
        (replaceTy (slotXᴵ s) (slotRᴵ s) (`∀ B₀ᴵ)) ≡ Cᴵ
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W (I.∀⊑∀ p₀) j Vᴵ Vᴾ
    → ValueImprecision W q j
        (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ `∀ B₀ᴵ 〗) Vᴾ
  imp-universal-value zero W s p₀ avoid no-occur q targetᴵ
      related =
    imp-reveal-endpoints W s (I.∀⊑∀ p₀) refl q targetᴵ related
      (imprecise-value related ↑ reveal-value-of shape-all)
  imp-universal-value (suc m) W s {B₀ᴵ = B₀ᴵ} {Acᵇ = Acᵇ}
      p₀ avoid (∉-all ∉ᵇ) q targetᴵ
      related@(endpointsₚ , Bᴾ* , Bᴵ* , embP* , embI* , fam)
      with ty-all-injective
             (renameᵗ-injective
               (toRenameᵗ-injective (impreciseEmbedding (core W)))
               embI*)
  imp-universal-value (suc m) W s {B₀ᴵ = B₀ᴵ} {Acᵇ = Acᵇ}
      p₀ avoid (∉-all ∉ᵇ) q targetᴵ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
      related@(endpointsₚ , Bᴾ* , .B₀ᴵ , embP* , embI* , fam)
      | refl =
    ClosureProof.value-imprecision-reindex q q̂c refl
      (trans (sym targetᴵ) (cong (λ Bʳ → `∀ Bʳ) body-eq))
      (imp-reveal-endpoints W s (I.∀⊑∀ p₀) refl q̂c
        (cong (λ Bʳ → `∀ Bʳ) body-eq) endpointsₚ
        (imprecise-value endpointsₚ ↑ reveal-value-of shape-all) ,
      Bᴾ* ,
      replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ ,
      embP* , cong (λ Bʳ → `∀ Bʳ) body-eq ,
      (λ {_} {_} {_} {W₂} W≼W₂ {B₂} {C₂} σᵇ →
        fam-out {W′ = W₂} W≼W₂ {Bᴾ′ = B₂} {Bᴵ′ = C₂} σᵇ))
    where
    q̂₀ = replace-right-body-⊑ W s p₀ avoid ∉ᵇ
    q̂c = I.∀⊑∀ q̂₀
    body-eq = embI-replace-body-eq W s B₀ᴵ

    Ac-eq : embedPreciseBody (core W) Bᴾ* ≡ Acᵇ
    Ac-eq = ty-all-injective embP*

    fam-out : UniversalFamily W q̂₀ Bᴾ*
        (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ)
        (suc m)
        (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ `∀ B₀ᴵ 〗) Vᴾ
    fam-out {W′ = W′} W≼W′ {Bᴾ′ = Bᴾ′} {Bᴵ′ = Bᴵ′} σ =
      ClosureProof.universals-phantom
          (liftCenterBodyImprecision W≼W′ p₀)
          (liftCenterBodyImprecision W≼W′ q̂₀)
          (ClosureProof.universals-related-transport
            {W = W′} {p = liftCenterBodyImprecision W≼W′ p₀}
            {Bᴾ = Bᴾ′} {k = suc m}
            termᴵ-eq termᴾ-eq (proj₁ base)) ,
        ClosureProof.pending-target-universals-related-transport
          termᴵ-eq termᴾ-eq (proj₂ base)
      where
      s′ = slot-future s W≼W′
      B₀ᴵ′ = liftImpreciseBody W≼W′ B₀ᴵ
      Bᴾ*′ = liftPreciseBody W≼W′ Bᴾ*

      imprecise-eq : liftImpreciseBody W≼W′
          (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ)
          ≡ replaceTy (Fin.suc (slotXᴵ s′)) (⇑ᵗ (slotRᴵ s′)) B₀ᴵ′
      imprecise-eq = trans
        (liftImpreciseBody-replace W≼W′ (slotXᴵ s) (slotRᴵ s) B₀ᴵ)
        (cong₂ (λ Xv R → replaceTy (Fin.suc Xv) (⇑ᵗ R) B₀ᴵ′)
          (sym (slot-imprecise-variable-lift s W≼W′))
          (sym (slot-imprecise-rep-lift s W≼W′)))

      ∉ᵇ′ : Fin.suc (center s′) ∉ᵗ
          embedPreciseBody (core W′) Bᴾ*′
      ∉ᵇ′ = subst≡ (Fin.suc (center s′) ∉ᵗ_)
        (sym (embedPreciseBody-lift W≼W′ Bᴾ*))
        (lift-center-body-∉ᵗ W≼W′
          (subst≡ (Fin.suc (center s) ∉ᵗ_) (sym Ac-eq) ∉ᵇ))

      base-impᵇ : BodyImprecisionᵇ W Bᴾ*
          (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ)
      base-impᵇ = body-imprecisionᵇ
        (subst≡
          (λ L → I.extᵐ (impEnv (core W)) I.⊢ L ⊑ _)
          (sym Ac-eq)
          (subst≡
            (λ R → I.extᵐ (impEnv (core W)) I.⊢ Acᵇ ⊑ R)
            (sym body-eq) q̂₀))

      av-fn : (j′ : BodyImprecisionᵇ W′ Bᴾ*′ B₀ᴵ′)
        → AliasAvoid★ᵖ (Fin.suc (center s′)) (bodyPᵇ j′)
      av-fn j′ = alias-avoid★-any
        (liftCenterBodyImprecision W≼W′ p₀) (bodyPᵇ j′)
        (trans (cong (liftCenterBody W≼W′) (sym Ac-eq))
          (sym (embedPreciseBody-lift W≼W′ Bᴾ*)))
        (sym (embedImpreciseBody-lift W≼W′ B₀ᴵ))
        (alias-avoid★-lift-body W≼W′ (center s) p₀ avoid)

      w : UniWrapᵇ W′ Bᴾ*′ B₀ᴵ′ Bᴾ*′
          (replaceTy (Fin.suc (slotXᴵ s′)) (⇑ᵗ (slotRᴵ s′)) B₀ᴵ′)
      w = reveal-impreciseᵇ s′ Bᴾ*′ B₀ᴵ′ ∉ᵇ′
        (body-imprecisionᵇ-subst-imp imprecise-eq
          (body-imprecisionᵇ-future W≼W′ base-impᵇ))
        av-fn

      σ‡ : UniWrapsᵇ W′ Bᴾ*′
          (replaceTy (Fin.suc (slotXᴵ s′)) (⇑ᵗ (slotRᴵ s′)) B₀ᴵ′)
          Bᴾ′ Bᴵ′
      σ‡ = subst≡
        (λ C → UniWrapsᵇ W′ Bᴾ*′ C Bᴾ′ Bᴵ′) imprecise-eq σ

      termᴾ-eq : wrapTermᴾᵇ (w ∷ σ‡) (liftPreciseTerm W≼W′ Vᴾ)
          ≡ wrapTermᴾᵇ σ (liftPreciseTerm W≼W′ Vᴾ)
      termᴾ-eq = wrapTermᴾᵇ-subst-imp imprecise-eq σ
        (liftPreciseTerm W≼W′ Vᴾ)

      termᴵ-eq : wrapTermᴵᵇ (w ∷ σ‡) (liftImpreciseTerm W≼W′ Vᴵ)
          ≡ wrapTermᴵᵇ σ (liftImpreciseTerm W≼W′
              (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ `∀ B₀ᴵ 〗))
      termᴵ-eq = trans
        (wrapTermᴵᵇ-subst-imp imprecise-eq σ
          (liftImpreciseTerm W≼W′ Vᴵ
            ↑ 〖 slotXᴵ s′ , slotRᴵ s′ ↑ `∀ B₀ᴵ′ 〗))
        (cong (wrapTermᴵᵇ σ)
          (trans
            (cong
              (λ T → liftImpreciseTerm W≼W′ Vᴵ
                ↑ 〖 slotXᴵ s′ , slotRᴵ s′ ↑ T 〗)
              (sym (liftImpreciseTy-universal W≼W′ B₀ᴵ)))
            (sym (lifted-reveal-imprecise s W≼W′ Vᴵ
              (`∀ B₀ᴵ)))))

      base = fam W≼W′ (w ∷ σ‡)

  -- Wrapping a related computation on the imprecise endpoint.

  imp-revealed-computations : ∀ (fuel j : ℕ)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
      {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → AliasAvoid★ᵖ (center s) p
    → sizeᵖ p ≤ fuel
    → center s ∉ᵗ Aᴾ
    → embedImprecise (core W) Bᴵ ≡ Aᴵ
    → ∀ {Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Aᴾ ⊑ Cᴵ)
    → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
        ≡ Cᴵ
    → ∀ {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
    → ComputationsRelated W (FutureValueRelation p) j Mᴵ Mᴾ
    → ComputationsRelated W (FutureValueRelation q) j
        (Mᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗) Mᴾ
  imp-revealed-computations fuel j W s {Bᴵ = Bᴵ} p avoid size
      no-occur sourceᴵ q targetᴵ {Mᴵ = Mᴵ} {Mᴾ = Mᴾ} related =
    reveal-imprecise-composition
      {R = FutureValueRelation p} {S = FutureValueRelation q}
      (reveal-frm 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗) j Mᴵ Mᴾ
      plug-values related
    where
    plug-values : RevealImprecisePlugValues W
        (FutureValueRelation p) (FutureValueRelation q) j
        (reveal-frm 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗)
    plug-values {W′ = W′} W≼W′ {χsᴾ = χsᴾ} {χsᴵ = χsᴵ}
        storeᴵ storeᴾ termsᴵ termsᴾ {j = i} i≤j
        {Vᴵ = Uᴵ} {Vᴾ = Uᴾ} value-related =
      computations-related-future-compose W≼W′ q
        (ClosureProof.computations-related-reindex
          (liftCenterImprecision W≼W′ q)
          (liftCenterImprecision W≼W′ q)
          refl refl
          (sym (transported-reveal-eq χsᴵ Mᴵ (slotXᴵ s)
            (slotRᴵ s) Bᴵ
            (trans
              (termsᴵ (Mᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗))
              (trans (lifted-reveal-imprecise s W≼W′ Mᴵ Bᴵ)
                (cong (λ M → M ↑ _) (sym (termsᴵ Mᴵ))))) Uᴵ))
          refl
          (imp-reveal-go fuel i W′ (slot-future s W≼W′)
            (liftCenterImprecision W≼W′ p)
            (alias-avoid★-lift-center W≼W′ (center s) p avoid)
            (subst≡ (_≤ fuel) (sym (lift-center-size W≼W′ p))
              size)
            (lift-center-∉ᵗ W≼W′ no-occur)
            (trans (embedImprecise-lift W≼W′ Bᴵ)
              (cong (liftCenterTy W≼W′) sourceᴵ))
            (liftCenterImprecision W≼W′ q)
            (trans
              (cong (embedImprecise (core W′))
                (replace-imprecise-lift s W≼W′ Bᴵ))
              (trans
                (embedImprecise-lift W≼W′
                  (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ))
                (cong (liftCenterTy W≼W′) targetᴵ)))
            value-related))

  imp-concealed-computations : ∀ (fuel j : ℕ)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
      {Bᴵ : Ty Δᴵ} {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → AliasAvoid★ᵖ (center s) p
    → sizeᵖ p ≤ fuel
    → center s ∉ᵗ Aᴾ
    → embedImprecise (core W) Bᴵ ≡ Aᴵ
    → ∀ {Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Aᴾ ⊑ Cᴵ)
    → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
        ≡ Cᴵ
    → ∀ {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
    → ComputationsRelated W (FutureValueRelation q) j Mᴵ Mᴾ
    → ComputationsRelated W (FutureValueRelation p) j
        (Mᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ) Mᴾ
  imp-concealed-computations fuel j W s {Bᴵ = Bᴵ} p avoid size
      no-occur sourceᴵ q targetᴵ {Mᴵ = Mᴵ} {Mᴾ = Mᴾ} related =
    conceal-imprecise-composition
      {R = FutureValueRelation q} {S = FutureValueRelation p}
      (conceal-frm (makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ)) j Mᴵ Mᴾ
      plug-values related
    where
    plug-values : ConcealImprecisePlugValues W
        (FutureValueRelation q) (FutureValueRelation p) j
        (conceal-frm (makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ))
    plug-values {W′ = W′} W≼W′ {χsᴾ = χsᴾ} {χsᴵ = χsᴵ}
        storeᴵ storeᴾ termsᴵ termsᴾ {j = i} i≤j
        {Vᴵ = Uᴵ} {Vᴾ = Uᴾ} value-related =
      computations-related-future-compose W≼W′ p
        (ClosureProof.computations-related-reindex
          (liftCenterImprecision W≼W′ p)
          (liftCenterImprecision W≼W′ p)
          refl refl
          (sym (transported-conceal-eq χsᴵ Mᴵ (slotXᴵ s)
            (slotRᴵ s) Bᴵ
            (trans
              (termsᴵ (Mᴵ ↓ makeConceal (slotXᴵ s)
                (slotRᴵ s) Bᴵ))
              (trans (lifted-conceal-imprecise s W≼W′ Mᴵ Bᴵ)
                (cong (λ M → M ↓ _) (sym (termsᴵ Mᴵ))))) Uᴵ))
          refl
          (imp-conceal-go fuel i W′ (slot-future s W≼W′)
            (liftCenterImprecision W≼W′ p)
            (alias-avoid★-lift-center W≼W′ (center s) p avoid)
            (subst≡ (_≤ fuel) (sym (lift-center-size W≼W′ p))
              size)
            (lift-center-∉ᵗ W≼W′ no-occur)
            (trans (embedImprecise-lift W≼W′ Bᴵ)
              (cong (liftCenterTy W≼W′) sourceᴵ))
            (liftCenterImprecision W≼W′ q)
            (trans
              (cong (embedImprecise (core W′))
                (replace-imprecise-lift s W≼W′ Bᴵ))
              (trans
                (embedImprecise-lift W≼W′
                  (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ))
                (cong (liftCenterTy W≼W′) targetᴵ)))
            value-related))

  imp-conceal-value-go : ∀ (fuel j : ℕ)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
      {Bᴵ : Ty Δᴵ} (shape : UniShape Bᴵ) {Aᴾ Aᴵ : Ty Δᶜ}
      (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
    → AliasAvoid★ᵖ (center s) p
    → sizeᵖ p ≤ fuel
    → center s ∉ᵗ Aᴾ
    → embedImprecise (core W) Bᴵ ≡ Aᴵ
    → ∀ {Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Aᴾ ⊑ Cᴵ)
    → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
        ≡ Cᴵ
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W q j Vᴵ Vᴾ
    → ValueImprecision W p j
        (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ) Vᴾ
  imp-conceal-value-go fuel zero W s shape p avoid size
      no-occur sourceᴵ q targetᴵ related =
    imp-conceal-endpoints W s p sourceᴵ q targetᴵ related
      (imprecise-value related ↓ conceal-value-of shape)
  imp-conceal-value-go (suc fuel) (suc m) W s
      (shape-fun {A₀ᴵ} {B₀ᴵ}) (I.⇒⊑⇒ p₁ p₂) (avoid₁ , avoid₂)
      size (∉-fun ∉₁ ∉₂) sourceᴵ q targetᴵ related with sourceᴵ
  imp-conceal-value-go (suc fuel) (suc m) W s
      (shape-fun {A₀ᴵ} {B₀ᴵ}) (I.⇒⊑⇒ p₁ p₂) (avoid₁ , avoid₂)
      size (∉-fun ∉₁ ∉₂) sourceᴵ q targetᴵ related | refl =
    imp-conceal-arrow-value fuel (suc m) W s p₁ p₂
      avoid₁ avoid₂ (sizeᵖ-bound-left size)
      (sizeᵖ-bound-right size) ∉₁ ∉₂ q targetᴵ related
  imp-conceal-value-go zero (suc m) W s
      (shape-fun {A₀ᴵ} {B₀ᴵ}) (I.⇒⊑⇒ p₁ p₂) avoid ()
      no-occur sourceᴵ q targetᴵ related
  imp-conceal-value-go (suc fuel) (suc m) W s shape
      (I.alias eq′ {notSelf} p′) (leaf , av′) (s≤s size′) no-occur
      sourceᴵ q targetᴵ related =
    imp-conceal-alias-value fuel (suc m) W s shape eq′
      {notSelf} p′ leaf av′ size′ sourceᴵ q targetᴵ related
  imp-conceal-value-go zero (suc m) W s shape
      (I.alias eq′ p′) avoid () no-occur sourceᴵ q targetᴵ
      related
  imp-conceal-value-go fuel (suc m) W s shape
      (I.∀⊑ nonvar occurs p₀) avoid size no-occur
      sourceᴵ q targetᴵ related
      with sourceᴵ
  imp-conceal-value-go fuel (suc m) W s shape
      (I.∀⊑ nonvar occurs p₀) avoid size no-occur
      sourceᴵ q targetᴵ related | refl =
    imp-conceal-right-universal-value (suc m) W s p₀ avoid
      no-occur shape q targetᴵ related
  imp-conceal-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      (I.∀⊑∀ p₀) avoid size no-occur sourceᴵ q targetᴵ related
      with sourceᴵ
  imp-conceal-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      (I.∀⊑∀ p₀) avoid size no-occur sourceᴵ q targetᴵ related
      | refl =
    imp-conceal-universal-value (suc m) W s p₀ avoid no-occur
      q targetᴵ related
  imp-conceal-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      I.bot-elim avoid size no-occur sourceᴵ q targetᴵ related =
    ⊥-elim (no-precise-bottom-value {p = q} {k = suc m} related)
  imp-conceal-value-go fuel (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      I.★⊑★ avoid size no-occur () q targetᴵ related
  imp-conceal-value-go fuel (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      I.ι⊑ι avoid size no-occur () q targetᴵ related
  imp-conceal-value-go fuel (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      I.X⊑X avoid size no-occur () q targetᴵ related
  imp-conceal-value-go fuel (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      (I.∀⊑∀ p₀) avoid size no-occur () q targetᴵ related
  imp-conceal-value-go fuel (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      (I.⇒⊑★ p₀₁ p₀₂) avoid size no-occur () q targetᴵ related
  imp-conceal-value-go fuel (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      I.ι⊑★ avoid size no-occur () q targetᴵ related
  imp-conceal-value-go fuel (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      (I.X⊑★ mode) avoid size no-occur () q targetᴵ related
  imp-conceal-value-go fuel (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      I.∀★⊑★ avoid size no-occur () q targetᴵ related
  imp-conceal-value-go fuel (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      (I.∀⊑★ nonstar p₀) avoid size no-occur () q targetᴵ related
  imp-conceal-value-go fuel (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      I.bot-elim avoid size no-occur () q targetᴵ related
  imp-conceal-value-go fuel (suc m) W s (shape-fun {A₀ᴵ} {B₀ᴵ})
      I.bot⊑★ avoid size no-occur () q targetᴵ related
  imp-conceal-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      I.★⊑★ avoid size no-occur () q targetᴵ related
  imp-conceal-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      I.ι⊑ι avoid size no-occur () q targetᴵ related
  imp-conceal-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      I.X⊑X avoid size no-occur () q targetᴵ related
  imp-conceal-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      (I.⇒⊑⇒ p₀₁ p₀₂) avoid size no-occur () q targetᴵ related
  imp-conceal-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      (I.⇒⊑★ p₀₁ p₀₂) avoid size no-occur () q targetᴵ related
  imp-conceal-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      I.ι⊑★ avoid size no-occur () q targetᴵ related
  imp-conceal-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      (I.X⊑★ mode) avoid size no-occur () q targetᴵ related
  imp-conceal-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      I.∀★⊑★ avoid size no-occur () q targetᴵ related
  imp-conceal-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      (I.∀⊑★ nonstar p₀) avoid size no-occur () q targetᴵ related
  imp-conceal-value-go fuel (suc m) W s (shape-all {B₀ᴵ})
      I.bot⊑★ avoid size no-occur () q targetᴵ related

  imp-conceal-arrow-value : ∀ (fuel j : ℕ)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
      {A₀ᴵ B₀ᴵ : Ty Δᴵ} {P₁ P₂ : Ty Δᶜ}
      (p₁ : impEnv (core W) I.⊢ P₁
        ⊑ embedImprecise (core W) A₀ᴵ)
      (p₂ : impEnv (core W) I.⊢ P₂
        ⊑ embedImprecise (core W) B₀ᴵ)
    → AliasAvoid★ᵖ (center s) p₁
    → AliasAvoid★ᵖ (center s) p₂
    → sizeᵖ p₁ ≤ fuel
    → sizeᵖ p₂ ≤ fuel
    → center s ∉ᵗ P₁
    → center s ∉ᵗ P₂
    → ∀ {Cᴵ : Ty Δᶜ}
      (q : impEnv (core W) I.⊢ (P₁ ⇒ P₂) ⊑ Cᴵ)
    → embedImprecise (core W)
        (replaceTy (slotXᴵ s) (slotRᴵ s) (A₀ᴵ ⇒ B₀ᴵ)) ≡ Cᴵ
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W q j Vᴵ Vᴾ
    → ValueImprecision W (I.⇒⊑⇒ p₁ p₂) j
        (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (A₀ᴵ ⇒ B₀ᴵ)) Vᴾ
  imp-conceal-arrow-value fuel zero W s p₁ p₂ avoid₁ avoid₂
      size₁ size₂ ∉₁ ∉₂ q targetᴵ related =
    imp-conceal-endpoints W s (I.⇒⊑⇒ p₁ p₂) refl q targetᴵ
      related
      (imprecise-value related ↓ conceal-value-of shape-fun)
  imp-conceal-arrow-value fuel (suc i) W s
      {A₀ᴵ = A₀ᴵ} {B₀ᴵ = B₀ᴵ}
      p₁ p₂ avoid₁ avoid₂ size₁ size₂ ∉₁ ∉₂
      q targetᴵ {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related =
    imp-conceal-endpoints W s (I.⇒⊑⇒ p₁ p₂) refl q targetᴵ
      endpoints-q
      (imprecise-value endpoints-q ↓ conceal-value-of shape-fun) ,
    functions (suc i) ≤-refl related′
    where
    q̂₁ = replace-right-⊑ W s p₁ avoid₁ ∉₁
    q̂₂ = replace-right-⊑ W s p₂ avoid₂ ∉₂
    q̂c = I.⇒⊑⇒ q̂₁ q̂₂

    endpoints-q = ClosureProof.value-imprecision-endpoints
      {W = W} {p = q} {k = suc i}
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related

    related′ : ValueImprecision W q̂c (suc i) Vᴵ Vᴾ
    related′ = ClosureProof.value-imprecision-reindex q̂c q refl
      (trans (sym (embI-replace-eq W s (A₀ᴵ ⇒ B₀ᴵ))) targetᴵ)
      related

    functions : ∀ (n : ℕ) → n ≤ suc i
      → ValueImprecision W q̂c n Vᴵ Vᴾ
      → FunctionsRelated W p₁ p₂ n
          (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (A₀ᴵ ⇒ B₀ᴵ))
          Vᴾ
    functions zero n≤ rel = tt
    functions (suc n) sn≤ rel =
      (λ W′ W≼W′ argument-related →
        imp-conceal-arrow-head fuel n W s p₁ p₂
          avoid₁ avoid₂ size₁ size₂ ∉₁ ∉₂ q̂₁ q̂₂
          (embI-replace-eq W s A₀ᴵ) (embI-replace-eq W s B₀ᴵ)
          rel W′ W≼W′ argument-related) ,
      functions n (≤-trans (n≤1+n n) sn≤)
        (value-imprecision-downward-to
          {W = W} {p = q̂c} {j = n} {k = suc n}
          {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} (n≤1+n n) rel)

  imp-conceal-arrow-head : ∀ (fuel m : ℕ)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
      {A₀ᴵ B₀ᴵ : Ty Δᴵ} {P₁ P₂ : Ty Δᶜ}
      (p₁ : impEnv (core W) I.⊢ P₁
        ⊑ embedImprecise (core W) A₀ᴵ)
      (p₂ : impEnv (core W) I.⊢ P₂
        ⊑ embedImprecise (core W) B₀ᴵ)
    → AliasAvoid★ᵖ (center s) p₁
    → AliasAvoid★ᵖ (center s) p₂
    → sizeᵖ p₁ ≤ fuel
    → sizeᵖ p₂ ≤ fuel
    → center s ∉ᵗ P₁
    → center s ∉ᵗ P₂
    → ∀ {Cᴵ₁ Cᴵ₂ : Ty Δᶜ}
      (q₁ : impEnv (core W) I.⊢ P₁ ⊑ Cᴵ₁)
      (q₂ : impEnv (core W) I.⊢ P₂ ⊑ Cᴵ₂)
    → embedImprecise (core W)
        (replaceTy (slotXᴵ s) (slotRᴵ s) A₀ᴵ) ≡ Cᴵ₁
    → embedImprecise (core W)
        (replaceTy (slotXᴵ s) (slotRᴵ s) B₀ᴵ) ≡ Cᴵ₂
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W (I.⇒⊑⇒ q₁ q₂) (suc m) Vᴵ Vᴾ
    → ∀ {Δᴾ′ Δᴵ′ Δᶜ′} (W′ : World Δᴾ′ Δᴵ′ Δᶜ′)
        (W≼W′ : Future W W′) {Uᴵ : Term Δᴵ′} {Uᴾ : Term Δᴾ′}
    → ValueImprecision W′ (liftCenterImprecision W≼W′ p₁) (suc m)
        Uᴵ Uᴾ
    → ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ p₂))
        (suc m)
        (liftImpreciseTerm W≼W′
          (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (A₀ᴵ ⇒ B₀ᴵ))
          · Uᴵ)
        (liftPreciseTerm W≼W′ Vᴾ · Uᴾ)
  imp-conceal-arrow-head fuel m W s {A₀ᴵ = A₀ᴵ} {B₀ᴵ = B₀ᴵ}
      p₁ p₂ avoid₁ avoid₂ size₁ size₂ ∉₁ ∉₂
      q₁ q₂ target₁ target₂ {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} function-related
      W′ W≼W′ {Uᴵ = Uᴵ} {Uᴾ = Uᴾ} argument-related =
    ClosureProof.computations-related-reindex
      (liftCenterImprecision W≼W′ p₂) (liftCenterImprecision W≼W′ p₂)
      refl refl (sym imprecise-redex-eq) refl expanded
    where
    s′ = slot-future s W≼W′
    A′ = liftImpreciseTy W≼W′ A₀ᴵ
    B′ = liftImpreciseTy W≼W′ B₀ᴵ
    cᴵ = 〖 slotXᴵ s′ , slotRᴵ s′ ↑ A′ 〗
    dᴵ = makeConceal (slotXᴵ s′) (slotRᴵ s′) B′
    Vᴵ′ = liftImpreciseTerm W≼W′ Vᴵ
    Vᴾ′ = liftPreciseTerm W≼W′ Vᴾ

    imprecise-redex-eq :
        liftImpreciseTerm W≼W′
          (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (A₀ᴵ ⇒ B₀ᴵ))
          · Uᴵ
        ≡ (Vᴵ′ ↓ (cᴵ ↦↓ dᴵ)) · Uᴵ
    imprecise-redex-eq
        rewrite lifted-conceal-imprecise s W≼W′ Vᴵ (A₀ᴵ ⇒ B₀ᴵ)
              | liftImpreciseTy-arrow W≼W′ A₀ᴵ B₀ᴵ = refl

    argument-endpoints =
      ClosureProof.value-imprecision-endpoints argument-related

    lifted-function : ValueImprecision W′
        (I.⇒⊑⇒ (liftCenterImprecision W≼W′ q₁)
          (liftCenterImprecision W≼W′ q₂)) (suc m) Vᴵ′ Vᴾ′
    lifted-function = ClosureProof.value-imprecision-reindex
      (I.⇒⊑⇒ (liftCenterImprecision W≼W′ q₁)
        (liftCenterImprecision W≼W′ q₂))
      (liftCenterImprecision W≼W′ (I.⇒⊑⇒ q₁ q₂))
      (sym (liftCenterTy-arrow W≼W′ _ _))
      (sym (liftCenterTy-arrow W≼W′ _ _))
      (ClosureProof.value-imprecision-future
        {W = W} {p = I.⇒⊑⇒ q₁ q₂} {k = suc m} {Vᴵ = Vᴵ} {Vᴾ = Vᴾ}
        W≼W′ function-related)

    revealed : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₁))
        (suc m) (Uᴵ ↑ cᴵ) Uᴾ
    revealed = imp-reveal-go fuel (suc m) W′ s′
      (liftCenterImprecision W≼W′ p₁)
      (alias-avoid★-lift-center W≼W′ (center s) p₁ avoid₁)
      (subst≡ (_≤ fuel) (sym (lift-center-size W≼W′ p₁)) size₁)
      (lift-center-∉ᵗ W≼W′ ∉₁)
      (embedImprecise-lift W≼W′ A₀ᴵ)
      (liftCenterImprecision W≼W′ q₁)
      (trans
        (cong (embedImprecise (core W′))
          (replace-imprecise-lift s W≼W′ A₀ᴵ))
        (trans
          (embedImprecise-lift W≼W′
            (replaceTy (slotXᴵ s) (slotRᴵ s) A₀ᴵ))
          (cong (liftCenterTy W≼W′) target₁)))
      argument-related

    applied : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ q₂))
        (suc m) (Vᴵ′ · (Uᴵ ↑ cᴵ)) (Vᴾ′ · Uᴾ)
    applied = related-application-computation lifted-function
      revealed

    framed : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ p₂))
        (suc m) ((Vᴵ′ · (Uᴵ ↑ cᴵ)) ↓ dᴵ) (Vᴾ′ · Uᴾ)
    framed = imp-concealed-computations fuel (suc m) W′ s′
      (liftCenterImprecision W≼W′ p₂)
      (alias-avoid★-lift-center W≼W′ (center s) p₂ avoid₂)
      (subst≡ (_≤ fuel) (sym (lift-center-size W≼W′ p₂)) size₂)
      (lift-center-∉ᵗ W≼W′ ∉₂)
      (embedImprecise-lift W≼W′ B₀ᴵ)
      (liftCenterImprecision W≼W′ q₂)
      (trans
        (cong (embedImprecise (core W′))
          (replace-imprecise-lift s W≼W′ B₀ᴵ))
        (trans
          (embedImprecise-lift W≼W′
            (replaceTy (slotXᴵ s) (slotRᴵ s) B₀ᴵ))
          (cong (liftCenterTy W≼W′) target₂)))
      applied

    expanded : ComputationsRelated W′
        (FutureValueRelation (liftCenterImprecision W≼W′ p₂))
        (suc m)
        ((Vᴵ′ ↓ (cᴵ ↦↓ dᴵ)) · Uᴵ) (Vᴾ′ · Uᴾ)
    expanded
        with conceal-fun-app-step-question
               {Σ = impreciseStore (core W′)} cᴵ dᴵ
               (imprecise-value function-endpoints)
               (imprecise-value argument-endpoints)
      where
      function-endpoints = ClosureProof.value-imprecision-endpoints
        {W = W′}
        {p = I.⇒⊑⇒ (liftCenterImprecision W≼W′ q₁)
          (liftCenterImprecision W≼W′ q₂)}
        {k = suc m} {Vᴵ = Vᴵ′} {Vᴾ = Vᴾ′} lifted-function
    expanded | vVᴵ , vUᴵ , step-eqᴵ =
      related-imprecise-keep-step-expand (λ ())
        (conceal-fun-app-value-none cᴵ dᴵ)
        (pure-step (β-conceal-⇒ vVᴵ vUᴵ)) step-eqᴵ framed

  imp-conceal-alias-value : ∀ (fuel j : ℕ)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
      {Bᴵ : Ty Δᴵ} (shape : UniShape Bᴵ)
      {X : TyVar Δᶜ} {T Aᴵ : Ty Δᶜ}
      (eq′ : impEnv (core W) X ≡ I.X⊑ᵗ T)
      {notSelf : False (isVar? X Aᴵ)}
      (p′ : impEnv (core W) I.⊢ T ⊑ Aᴵ)
    → (Aᴵ ≡ ★) ⊎ (center s ∉ᵗ T)
    → AliasAvoid★ᵖ (center s) p′
    → sizeᵖ p′ ≤ fuel
    → embedImprecise (core W) Bᴵ ≡ Aᴵ
    → ∀ {Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ ＇ X ⊑ Cᴵ)
    → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
        ≡ Cᴵ
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W q j Vᴵ Vᴾ
    → ValueImprecision W (I.alias eq′ {notSelf = notSelf} p′) j
        (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ) Vᴾ
  imp-conceal-alias-value fuel zero W s shape eq′ {notSelf}
      p′ leaf av′ size′ sourceᴵ q targetᴵ related =
    imp-conceal-endpoints W s
      (I.alias eq′ {notSelf = notSelf} p′) sourceᴵ q targetᴵ
      related
      (imprecise-value related ↓ conceal-value-of shape)
  imp-conceal-alias-value fuel (suc m) W s {Bᴵ = Bᴵ} shape
      {X = X} {Aᴵ = Aᴵ} eq′ {notSelf} p′ leaf av′ size′ sourceᴵ
      q targetᴵ related =
    imp-conceal-endpoints W s
      (I.alias eq′ {notSelf = notSelf} p′) sourceᴵ q targetᴵ
      endpoints-q
      (imprecise-value endpoints-q ↓ conceal-value-of shape) ,
    alias-holds-imp-map (semanticEntry W X) eq′
      (λ {Uᴾ} rel →
        imp-conceal-value-go fuel (suc m) W s shape p′ av′
          size′ c∉T sourceᴵ q̂′ target-eq rel)
      (proj₂ related′)
    where
    c∉T = shape-star-∉ W shape sourceᴵ leaf

    q̂′ = replace-right-⊑ W s p′ av′ c∉T
    q̂c = I.alias eq′
      {notSelf = replace-alias-not-self★ (center s)
        (embedImprecise (core W) (slotRᴵ s)) c∉T p′ av′ notSelf}
      q̂′

    target-eq : embedImprecise (core W)
        (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
        ≡ replaceTy (center s)
            (embedImprecise (core W) (slotRᴵ s)) Aᴵ
    target-eq = trans (embI-replace-eq W s Bᴵ)
      (cong
        (replaceTy (center s)
          (embedImprecise (core W) (slotRᴵ s)))
        sourceᴵ)

    related′ : ValueImprecision W q̂c (suc m) _ _
    related′ = ClosureProof.value-imprecision-reindex q̂c q refl
      (trans (sym target-eq) targetᴵ)
      related

    endpoints-q = ClosureProof.value-imprecision-endpoints
      {W = W} {p = q} {k = suc m} related

  imp-conceal-universal-value : ∀ (j : ℕ)
      {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
      {B₀ᴵ : Ty (suc Δᴵ)} {Acᵇ : Ty (suc Δᶜ)}
      (p₀ : I.extᵐ (impEnv (core W)) I.⊢ Acᵇ
        ⊑ embedImpreciseBody (core W) B₀ᴵ)
    → AliasAvoid★ᵖ (Fin.suc (center s)) p₀
    → center s ∉ᵗ `∀ Acᵇ
    → ∀ {Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ `∀ Acᵇ ⊑ Cᴵ)
    → embedImprecise (core W)
        (replaceTy (slotXᴵ s) (slotRᴵ s) (`∀ B₀ᴵ)) ≡ Cᴵ
    → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    → ValueImprecision W q j Vᴵ Vᴾ
    → ValueImprecision W (I.∀⊑∀ p₀) j
        (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (`∀ B₀ᴵ)) Vᴾ
  imp-conceal-universal-value zero W s p₀ avoid no-occur
      q targetᴵ related =
    imp-conceal-endpoints W s (I.∀⊑∀ p₀) refl q targetᴵ related
      (imprecise-value related ↓ conceal-value-of shape-all)
  imp-conceal-universal-value (suc m) W s {B₀ᴵ = B₀ᴵ}
      {Acᵇ = Acᵇ} p₀ avoid (∉-all ∉ᵇ) q targetᴵ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
      with ClosureProof.value-imprecision-reindex
             (I.∀⊑∀ (replace-right-body-⊑ W s p₀ avoid ∉ᵇ)) q refl
             (trans
               (sym (cong (λ Bʳ → `∀ Bʳ)
                 (embI-replace-body-eq W s B₀ᴵ)))
               targetᴵ)
             related
  imp-conceal-universal-value (suc m) W s {B₀ᴵ = B₀ᴵ}
      {Acᵇ = Acᵇ} p₀ avoid (∉-all ∉ᵇ) q targetᴵ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
      | (endpointsʳ , Bᴾ* , Bᴵ*ʳ , embP* , embI*ʳ , fam-r)
      with ty-all-injective
             (renameᵗ-injective
               (toRenameᵗ-injective (impreciseEmbedding (core W)))
               (trans embI*ʳ
                 (sym (cong (λ Bʳ → `∀ Bʳ)
                   (embI-replace-body-eq W s B₀ᴵ)))))
  imp-conceal-universal-value (suc m) W s {B₀ᴵ = B₀ᴵ}
      {Acᵇ = Acᵇ} p₀ avoid (∉-all ∉ᵇ) q targetᴵ
      {Vᴵ = Vᴵ} {Vᴾ = Vᴾ} related
      | (endpointsʳ ,
         Bᴾ* ,
         .(replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ) ,
         embP* , embI*ʳ , fam-r)
      | refl =
    imp-conceal-endpoints W s (I.∀⊑∀ p₀) refl q targetᴵ
      (ClosureProof.value-imprecision-endpoints
        {W = W} {p = q} {k = suc m} related)
      (imprecise-value
        (ClosureProof.value-imprecision-endpoints
          {W = W} {p = q} {k = suc m} related)
        ↓ conceal-value-of shape-all) ,
    Bᴾ* , B₀ᴵ , embP* , refl ,
    (λ {_} {_} {_} {W₂} W≼W₂ {B₂} {C₂} σᵇ →
      fam-out {W′ = W₂} W≼W₂ {Bᴾ′ = B₂} {Bᴵ′ = C₂} σᵇ)
    where
    q̂₀ = replace-right-body-⊑ W s p₀ avoid ∉ᵇ
    body-eq = embI-replace-body-eq W s B₀ᴵ

    Ac-eq : embedPreciseBody (core W) Bᴾ* ≡ Acᵇ
    Ac-eq = ty-all-injective embP*

    fam-out : UniversalFamily W p₀ Bᴾ* B₀ᴵ (suc m)
        (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (`∀ B₀ᴵ)) Vᴾ
    fam-out {W′ = W′} W≼W′ {Bᴾ′ = Bᴾ′} {Bᴵ′ = Bᴵ′} σ =
      ClosureProof.universals-phantom
          (liftCenterBodyImprecision W≼W′ q̂₀)
          (liftCenterBodyImprecision W≼W′ p₀)
          (ClosureProof.universals-related-transport
            {W = W′} {p = liftCenterBodyImprecision W≼W′ q̂₀}
            {Bᴾ = Bᴾ′} {k = suc m}
            termᴵ-eq termᴾ-eq (proj₁ base)) ,
        ClosureProof.pending-target-universals-related-transport
          termᴵ-eq termᴾ-eq (proj₂ base)
      where
      s′ = slot-future s W≼W′
      B₀ᴵ′ = liftImpreciseBody W≼W′ B₀ᴵ
      Bᴾ*′ = liftPreciseBody W≼W′ Bᴾ*

      imprecise-eq : liftImpreciseBody W≼W′
          (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ)
          ≡ replaceTy (Fin.suc (slotXᴵ s′)) (⇑ᵗ (slotRᴵ s′)) B₀ᴵ′
      imprecise-eq = trans
        (liftImpreciseBody-replace W≼W′ (slotXᴵ s) (slotRᴵ s)
          B₀ᴵ)
        (cong₂ (λ Xv R → replaceTy (Fin.suc Xv) (⇑ᵗ R) B₀ᴵ′)
          (sym (slot-imprecise-variable-lift s W≼W′))
          (sym (slot-imprecise-rep-lift s W≼W′)))

      ∉ᵇ′ : Fin.suc (center s′) ∉ᵗ
          embedPreciseBody (core W′) Bᴾ*′
      ∉ᵇ′ = subst≡ (Fin.suc (center s′) ∉ᵗ_)
        (sym (embedPreciseBody-lift W≼W′ Bᴾ*))
        (lift-center-body-∉ᵗ W≼W′
          (subst≡ (Fin.suc (center s) ∉ᵗ_) (sym Ac-eq) ∉ᵇ))

      base-impᵇ : BodyImprecisionᵇ W Bᴾ* B₀ᴵ
      base-impᵇ = body-imprecisionᵇ
        (subst≡
          (λ L → I.extᵐ (impEnv (core W)) I.⊢ L ⊑ _)
          (sym Ac-eq) p₀)

      av-fn : (j′ : BodyImprecisionᵇ W′ Bᴾ*′ B₀ᴵ′)
        → AliasAvoid★ᵖ (Fin.suc (center s′)) (bodyPᵇ j′)
      av-fn j′ = alias-avoid★-any
        (liftCenterBodyImprecision W≼W′ p₀) (bodyPᵇ j′)
        (trans (cong (liftCenterBody W≼W′) (sym Ac-eq))
          (sym (embedPreciseBody-lift W≼W′ Bᴾ*)))
        (sym (embedImpreciseBody-lift W≼W′ B₀ᴵ))
        (alias-avoid★-lift-body W≼W′ (center s) p₀ avoid)

      w : UniWrapᵇ W′ Bᴾ*′
          (replaceTy (Fin.suc (slotXᴵ s′)) (⇑ᵗ (slotRᴵ s′)) B₀ᴵ′)
          Bᴾ*′ B₀ᴵ′
      w = conceal-impreciseᵇ s′ Bᴾ*′ B₀ᴵ′ ∉ᵇ′
        (body-imprecisionᵇ-future W≼W′ base-impᵇ)
        av-fn

      σ† : UniWrapsᵇ W′ Bᴾ*′
          (liftImpreciseBody W≼W′
            (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) B₀ᴵ))
          Bᴾ′ Bᴵ′
      σ† = subst≡
        (λ C → UniWrapsᵇ W′ Bᴾ*′ C Bᴾ′ Bᴵ′)
        (sym imprecise-eq) (w ∷ σ)

      termᴾ-eq : wrapTermᴾᵇ σ† (liftPreciseTerm W≼W′ Vᴾ)
          ≡ wrapTermᴾᵇ σ (liftPreciseTerm W≼W′ Vᴾ)
      termᴾ-eq = wrapTermᴾᵇ-subst-imp (sym imprecise-eq) (w ∷ σ)
        (liftPreciseTerm W≼W′ Vᴾ)

      termᴵ-eq : wrapTermᴵᵇ σ† (liftImpreciseTerm W≼W′ Vᴵ)
          ≡ wrapTermᴵᵇ σ (liftImpreciseTerm W≼W′
              (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s)
                (`∀ B₀ᴵ)))
      termᴵ-eq = trans
        (wrapTermᴵᵇ-subst-imp (sym imprecise-eq) (w ∷ σ)
          (liftImpreciseTerm W≼W′ Vᴵ))
        (cong (wrapTermᴵᵇ σ)
          (trans
            (cong
              (λ T → liftImpreciseTerm W≼W′ Vᴵ
                ↓ makeConceal (slotXᴵ s′) (slotRᴵ s′) T)
              (sym (liftImpreciseTy-universal W≼W′ B₀ᴵ)))
            (sym (lifted-conceal-imprecise s W≼W′ Vᴵ
              (`∀ B₀ᴵ)))))

      base = fam-r W≼W′ σ†

------------------------------------------------------------------------
-- The one-sided imprecise reveal and conceal, with the fuel
-- instantiated
------------------------------------------------------------------------

imprecise-reveal : ∀ {k : ℕ} → ImpreciseRevealAt k
imprecise-reveal {k = k} W s {Bᴵ = Bᴵ} p avoid no-occur
    sourceᴵ q targetᴵ related =
  imp-reveal-go (sizeᵖ p) k W s p avoid ≤-refl no-occur
    sourceᴵ q targetᴵ related

imprecise-conceal : ∀ {k : ℕ} → ImpreciseConcealAt k
imprecise-conceal {k = k} W s {Bᴵ = Bᴵ} p avoid no-occur
    sourceᴵ q targetᴵ related =
  imp-conceal-go (sizeᵖ p) k W s p avoid ≤-refl no-occur
    sourceᴵ q targetᴵ related

imprecise-reveal-value : ∀ {k : ℕ}
    {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
    {Bᴵ : Ty Δᴵ} (shape : UniShape Bᴵ) {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → AliasAvoid★ᵖ (center s) p
  → center s ∉ᵗ Aᴾ
  → embedImprecise (core W) Bᴵ ≡ Aᴵ
  → ∀ {Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Aᴾ ⊑ Cᴵ)
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
      ≡ Cᴵ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W p k Vᴵ Vᴾ
  → ValueImprecision W q k
      (Vᴵ ↑ 〖 slotXᴵ s , slotRᴵ s ↑ Bᴵ 〗) Vᴾ
imprecise-reveal-value {k = k} W s shape p avoid no-occur
    sourceᴵ q targetᴵ related =
  imp-value-go (sizeᵖ p) k W s shape p avoid ≤-refl no-occur
    sourceᴵ q targetᴵ related

imprecise-conceal-value : ∀ {k : ℕ}
    {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) (s : PairedSlot W)
    {Bᴵ : Ty Δᴵ} (shape : UniShape Bᴵ) {Aᴾ Aᴵ : Ty Δᶜ}
    (p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ)
  → AliasAvoid★ᵖ (center s) p
  → center s ∉ᵗ Aᴾ
  → embedImprecise (core W) Bᴵ ≡ Aᴵ
  → ∀ {Cᴵ : Ty Δᶜ} (q : impEnv (core W) I.⊢ Aᴾ ⊑ Cᴵ)
  → embedImprecise (core W) (replaceTy (slotXᴵ s) (slotRᴵ s) Bᴵ)
      ≡ Cᴵ
  → ∀ {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → ValueImprecision W q k Vᴵ Vᴾ
  → ValueImprecision W p k
      (Vᴵ ↓ makeConceal (slotXᴵ s) (slotRᴵ s) Bᴵ) Vᴾ
imprecise-conceal-value {k = k} W s shape p avoid no-occur
    sourceᴵ q targetᴵ related =
  imp-conceal-value-go (sizeᵖ p) k W s shape p avoid ≤-refl
    no-occur sourceᴵ q targetᴵ related
