module proof.LR-narrow.FunctionSealRetraction where

-- File Charter:
--   * Retracts balanced conceal/reveal adapters around arbitrary functions.
--   * Transports matching seals through arbitrary body allocations, retaining
--     every name and every seal inside the returned value.
--   * Proves return/blame simulation, exact store actions, and relational
--     lifting of body results. No identity-body or compatibility assumption.
--   * A proof-local operational interface, not yet a live LR replacement.

open import Data.List using ([])
open import Data.Product using (_×_; _,_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym) renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import Reduction
open import Consistency using (_↪ᵗ_; toRenameᵗ)
open import proof.Reduction using (_++χ_; applyStores-++)
open import proof.LR-narrow.PrivateSealBehavior using
  (_—↠[_]⟨_⟩+_; reveal-keep-step)
open import proof.LR-narrow.SlotLifting using (rename↓-identity)
open import proof.LR-narrow.TypeRenamingComposition using (apply↓)

-- A computational retraction, not an identification of abstract names
-- with their representations. X and Y may represent arbitrary types.

roundtrip : ∀ {Δ} → TyVar Δ → Ty Δ → TyVar Δ → Ty Δ → Term Δ → Term Δ
roundtrip X A Y B F =
  (F ↓ (unseal X A ↦↓ seal Y B)) ↑ (seal X A ↦↑ unseal Y B)

roundtrip-value : ∀ {Δ} {F : Term Δ} X A Y B
  → Value F → Value (roundtrip X A Y B F)
roundtrip-value X A Y B vF = (vF ↓ fun) ↑ fun

roundtrip-typed : ∀ {Δ} {Σ : TyStore Δ} {X A Y B F}
  → Σ ∋ X ⦂ A → Σ ∋ Y ⦂ B
  → ⟨ Δ , Σ , [] ⟩ ⊢ F ⦂ (A ⇒ B)
  → ⟨ Δ , Σ , [] ⟩ ⊢ roundtrip X A Y B F ⦂ (A ⇒ B)
roundtrip-typed entryX entryY typed =
  ⊢reveal (⊢↑-⇒ (⊢↓-seal entryX) (⊢↑-unseal entryY))
    (⊢conceal (⊢↓-⇒ (⊢↑-unseal entryX) (⊢↓-seal entryY)) typed)

roundtrip-rename : ∀ {Δ Δ′} (ρ : Δ ↪ᵗ Δ′) X A Y B F
  → renameᵗᵐ ρ (roundtrip X A Y B F)
      ≡ roundtrip (toRenameᵗ ρ X) (renameᵗ (toRenameᵗ ρ) A)
          (toRenameᵗ ρ Y) (renameᵗ (toRenameᵗ ρ) B) (renameᵗᵐ ρ F)
roundtrip-rename ρ X A Y B F = refl

applyVars : ∀ {Δ Δ′} → StoreChanges Δ Δ′ → TyVar Δ → TyVar Δ′
applyVars [] X = X
applyVars (keep ∷ χs) X = applyVars χs X
applyVars (bind A ∷ χs) X = applyVars χs (Fin.suc X)

changed-entry : ∀ {Δ Δ′} {Σ : TyStore Δ} {X R}
  → (χs : StoreChanges Δ Δ′) → Σ ∋ X ⦂ R
  → χs ▶ˢ Σ ∋ applyVars χs X ⦂ χs ▶ᵗ R
changed-entry [] entry = entry
changed-entry (keep ∷ χs) entry = changed-entry χs entry
changed-entry (bind A ∷ χs) entry =
  changed-entry χs (S-bind∋ entry refl)

conceal-keep-step : ∀ {Δ} {M N : Term Δ} {A B} (c : Conv↓ Δ A B)
  → M —→[ keep ] N → M ↓ c —→[ keep ] N ↓ c
conceal-keep-step {M = M} {N = N} c step =
  subst≡ (λ P → M ↓ c —→[ keep ] P)
    (cong (apply↓ N) (rename↓-identity c)) (ξ-conceal step refl)

seal-trace : ∀ {Δ Δ′} {M : Term Δ} {N : Term Δ′} {χs}
  → (X : TyVar Δ) → (R : Ty Δ) → M —↠[ χs ] N
  → M ↓ seal X R —↠[ χs ] N ↓ seal (applyVars χs X) (χs ▶ᵗ R)
seal-trace {M = M} X R ↠-refl = (M ↓ seal X R) ∎[]
seal-trace {M = M} {N = P} {χs = keep ∷ χs} X R
    (↠-step {N = N} step rest) =
    M ↓ seal X R
  —→[ keep ]⟨ conceal-keep-step (seal X R) step ⟩
    N ↓ seal X R
  —↠[ χs ]⟨ seal-trace X R rest ⟩
    P ↓ seal (applyVars χs X) (χs ▶ᵗ R) ∎[]
seal-trace {M = M} {N = P} {χs = bind A ∷ χs} X R
    (↠-step {N = N} step rest) =
    M ↓ seal X R
  —→[ bind A ]⟨ ξ-conceal step refl ⟩
    N ↓ seal (Fin.suc X) (⇑ᵗ R)
  —↠[ χs ]⟨ seal-trace (Fin.suc X) (⇑ᵗ R) rest ⟩
    P ↓ seal (applyVars χs (Fin.suc X)) (χs ▶ᵗ (⇑ᵗ R)) ∎[]

unseal-trace : ∀ {Δ Δ′} {M : Term Δ} {N : Term Δ′} {χs}
  → (X : TyVar Δ) → (R : Ty Δ) → M —↠[ χs ] N
  → M ↑ unseal X R —↠[ χs ] N ↑ unseal (applyVars χs X) (χs ▶ᵗ R)
unseal-trace {M = M} X R ↠-refl = (M ↑ unseal X R) ∎[]
unseal-trace {M = M} {N = P} {χs = keep ∷ χs} X R
    (↠-step {N = N} step rest) =
    M ↑ unseal X R
  —→[ keep ]⟨ reveal-keep-step (unseal X R) step ⟩
    N ↑ unseal X R
  —↠[ χs ]⟨ unseal-trace X R rest ⟩
    P ↑ unseal (applyVars χs X) (χs ▶ᵗ R) ∎[]
unseal-trace {M = M} {N = P} {χs = bind A ∷ χs} X R
    (↠-step {N = N} step rest) =
    M ↑ unseal X R
  —→[ bind A ]⟨ ξ-reveal step refl ⟩
    N ↑ unseal (Fin.suc X) (⇑ᵗ R)
  —↠[ χs ]⟨ unseal-trace (Fin.suc X) (⇑ᵗ R) rest ⟩
    P ↑ unseal (applyVars χs (Fin.suc X)) (χs ▶ᵗ (⇑ᵗ R)) ∎[]

-- These three administrative steps use no information about the body of
-- F. Its computation is still unevaluated at the end of the prefix.

roundtrip-prefix : ∀ {Δ} {F V : Term Δ} X A Y B
  → Value F → Value V
  → roundtrip X A Y B F · V —↠[ keep ∷ keep ∷ keep ∷ [] ]
      ((F · V) ↓ seal Y B) ↑ unseal Y B
roundtrip-prefix {F = F} {V} X A Y B vF vV =
    roundtrip X A Y B F · V
  —→[ keep ]⟨ pure-step (β-reveal-⇒ (vF ↓ fun) vV) ⟩
    ((F ↓ (unseal X A ↦↓ seal Y B)) · (V ↓ seal X A)) ↑ unseal Y B
  —→[ keep ]⟨ reveal-keep-step (unseal Y B)
      (pure-step (β-conceal-⇒ vF (vV ↓ seal))) ⟩
    ((F · ((V ↓ seal X A) ↑ unseal X A)) ↓ seal Y B) ↑ unseal Y B
  —→[ keep ]⟨ reveal-keep-step (unseal Y B)
      (conceal-keep-step (seal Y B)
        (ξ-·₂ vF (pure-step (conceal-reveal vV)) refl)) ⟩
    ((F · V) ↓ seal Y B) ↑ unseal Y B ∎[]

roundtrip-return : ∀ {Δ Δ′} {F V : Term Δ} {U : Term Δ′}
    {χs : StoreChanges Δ Δ′} X A Y B
  → Value F → Value V → F · V —↠[ χs ] U → Value U
  → roundtrip X A Y B F · V
      —↠[ keep ∷ keep ∷ keep ∷ (χs ++χ (keep ∷ [])) ] U
roundtrip-return {F = F} {V} {U} {χs} X A Y B vF vV body vU =
    roundtrip X A Y B F · V
  —↠[ keep ∷ keep ∷ keep ∷ [] ]⟨ roundtrip-prefix X A Y B vF vV ⟩+
    ((F · V) ↓ seal Y B) ↑ unseal Y B
  —↠[ χs ]⟨ unseal-trace Y B (seal-trace Y B body) ⟩+
    (U ↓ seal (applyVars χs Y) (χs ▶ᵗ B))
      ↑ unseal (applyVars χs Y) (χs ▶ᵗ B)
  —→[ keep ]⟨ pure-step (conceal-reveal vU) ⟩
    U ∎[]

roundtrip-blame : ∀ {Δ Δ′} {F V : Term Δ} {χs : StoreChanges Δ Δ′}
    X A Y B
  → Value F → Value V → F · V —↠[ χs ] blame
  → roundtrip X A Y B F · V
      —↠[ keep ∷ keep ∷ keep ∷ (χs ++χ (keep ∷ keep ∷ [])) ] blame
roundtrip-blame {F = F} {V} {χs} X A Y B vF vV body =
    roundtrip X A Y B F · V
  —↠[ keep ∷ keep ∷ keep ∷ [] ]⟨ roundtrip-prefix X A Y B vF vV ⟩+
    ((F · V) ↓ seal Y B) ↑ unseal Y B
  —↠[ χs ]⟨ unseal-trace Y B (seal-trace Y B body) ⟩+
    (blame ↓ seal (applyVars χs Y) (χs ▶ᵗ B))
      ↑ unseal (applyVars χs Y) (χs ▶ᵗ B)
  —→[ keep ]⟨ reveal-keep-step (unseal (applyVars χs Y) (χs ▶ᵗ B))
      (pure-step blame-conceal) ⟩
    blame ↑ unseal (applyVars χs Y) (χs ▶ᵗ B)
  —→[ keep ]⟨ pure-step blame-reveal ⟩
    blame ∎[]

roundtrip-return-store : ∀ {Δ Δ′} (χs : StoreChanges Δ Δ′) (Σ : TyStore Δ)
  → (keep ∷ keep ∷ keep ∷ (χs ++χ (keep ∷ []))) ▶ˢ Σ ≡ χs ▶ˢ Σ
roundtrip-return-store χs Σ = sym (applyStores-++ χs (keep ∷ []) Σ)

roundtrip-blame-store : ∀ {Δ Δ′} (χs : StoreChanges Δ Δ′) (Σ : TyStore Δ)
  → (keep ∷ keep ∷ keep ∷ (χs ++χ (keep ∷ keep ∷ []))) ▶ˢ Σ ≡ χs ▶ˢ Σ
roundtrip-blame-store χs Σ = sym (applyStores-++ χs (keep ∷ keep ∷ []) Σ)

-- Related body results need not be related to the inputs, nor be syntax
-- that lowers to a smaller scope. The adapters leave those actual results
-- intact. S is an existing body-result relation, not an adapter obligation.

roundtrip-pair-return : ∀ {Δᴵ Δᴾ Δᴵ′ Δᴾ′}
    {Fᴵ Vᴵ : Term Δᴵ} {Fᴾ Vᴾ : Term Δᴾ}
    {Uᴵ : Term Δᴵ′} {Uᴾ : Term Δᴾ′}
    {χsᴵ : StoreChanges Δᴵ Δᴵ′} {χsᴾ : StoreChanges Δᴾ Δᴾ′}
    Xᴵ Aᴵ Yᴵ Bᴵ Xᴾ Aᴾ Yᴾ Bᴾ
  → Value Fᴵ → Value Vᴵ → Value Fᴾ → Value Vᴾ
  → Fᴵ · Vᴵ —↠[ χsᴵ ] Uᴵ → Fᴾ · Vᴾ —↠[ χsᴾ ] Uᴾ
  → Value Uᴵ → Value Uᴾ
  → (S : Term Δᴵ′ → Term Δᴾ′ → Set) → S Uᴵ Uᴾ
  → (roundtrip Xᴵ Aᴵ Yᴵ Bᴵ Fᴵ · Vᴵ
      —↠[ keep ∷ keep ∷ keep ∷ (χsᴵ ++χ (keep ∷ [])) ] Uᴵ)
    × (roundtrip Xᴾ Aᴾ Yᴾ Bᴾ Fᴾ · Vᴾ
      —↠[ keep ∷ keep ∷ keep ∷ (χsᴾ ++χ (keep ∷ [])) ] Uᴾ)
    × S Uᴵ Uᴾ
roundtrip-pair-return Xᴵ Aᴵ Yᴵ Bᴵ Xᴾ Aᴾ Yᴾ Bᴾ
    vFᴵ vVᴵ vFᴾ vVᴾ bodyᴵ bodyᴾ vUᴵ vUᴾ S related =
  roundtrip-return Xᴵ Aᴵ Yᴵ Bᴵ vFᴵ vVᴵ bodyᴵ vUᴵ ,
  roundtrip-return Xᴾ Aᴾ Yᴾ Bᴾ vFᴾ vVᴾ bodyᴾ vUᴾ , related
