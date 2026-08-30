module proof.LR-narrow.FunctionSealCompatibility where

-- File Charter:
--   * General function-reveal compatibility at abstract argument/result slots.
--   * Uses preservation and canonical forms to derive the returned seal;
--     the function body may allocate and return any new closure.
--   * Lifts a payload relation through nominal seals and proves its decoding
--     after independently allocating endpoint bodies. No body is assumed
--     to be an identity or a syntactic conceal/reveal roundtrip.

open import Data.List using ([])
import Data.Fin as Fin
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym) renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import Reduction
open import proof.Reduction using (_++χ_; applyStores-++)
open import proof.TypeSafety.Progress using
  (canonical-X; SealView; sv-conceal; lookup-unique)
open import proof.TypeSafety.Preservation using (multi-preservation)
open import proof.LR-narrow.PrivateSealBehavior using (_—↠[_]⟨_⟩+_)
open import proof.LR-narrow.FunctionSealRetraction using
  (applyVars; changed-entry; unseal-trace)

-- The public adapter has a single reveal. F itself is arbitrary.

reveal-function : ∀ {Δ} → TyVar Δ → Ty Δ → TyVar Δ → Ty Δ
  → Term Δ → Term Δ
reveal-function X A Y B F = F ↑ (seal X A ↦↑ unseal Y B)

reveal-function-typed : ∀ {Δ} {Σ : TyStore Δ} {X A Y B F}
  → Σ ∋ X ⦂ A → Σ ∋ Y ⦂ B
  → ⟨ Δ , Σ , [] ⟩ ⊢ F ⦂ (＇ X ⇒ ＇ Y)
  → ⟨ Δ , Σ , [] ⟩ ⊢ reveal-function X A Y B F ⦂ (A ⇒ B)
reveal-function-typed entryX entryY typed =
  ⊢reveal (⊢↑-⇒ (⊢↓-seal entryX) (⊢↑-unseal entryY)) typed

changed-variable-type : ∀ {Δ Δ′} (χs : StoreChanges Δ Δ′) X
  → χs ▶ᵗ (＇ X) ≡ ＇ (applyVars χs X)
changed-variable-type [] X = refl
changed-variable-type (keep ∷ χs) X = changed-variable-type χs X
changed-variable-type (bind A ∷ χs) X =
  changed-variable-type χs (Fin.suc X)

sealed-payload-typed : ∀ {Δ} {Σ : TyStore Δ} {X R U}
  → ⟨ Δ , Σ , [] ⟩ ⊢ U ↓ seal X R ⦂ ＇ X
  → ⟨ Δ , Σ , [] ⟩ ⊢ U ⦂ R
sealed-payload-typed (⊢conceal valid typed) = typed

canonical-payload : ∀ {Δ} {Σ : TyStore Δ} {Y B Z}
  → Σ ∋ Y ⦂ B → Value Z → ⟨ Δ , Σ , [] ⟩ ⊢ Z ⦂ ＇ Y
  → ∃[ U ] Value U × (⟨ Δ , Σ , [] ⟩ ⊢ U ⦂ B)
      × (Z ≡ U ↓ seal Y B)
canonical-payload {Σ = Σ} {Y} entry vZ typed with canonical-X vZ typed
canonical-payload {Σ = Σ} {Y} entry vZ typed
    | sv-conceal {W = U} actual vU eq with lookup-unique actual entry
canonical-payload {Σ = Σ} {Y} entry vZ typed
    | sv-conceal {W = U} actual vU eq | refl =
  U , vU , sealed-payload-typed
    (subst≡ (λ Z → ⟨ _ , Σ , [] ⟩ ⊢ Z ⦂ ＇ Y) eq typed) , eq

-- The only result-side shape needed by the operational theorem. The
-- following typed theorem derives it, so it is not a new proof obligation.

reveal-function-return : ∀ {Δ Δ′} {F V : Term Δ} {U : Term Δ′}
    {χs : StoreChanges Δ Δ′} X A Y B
  → Value F → Value V
  → F · (V ↓ seal X A)
      —↠[ χs ] U ↓ seal (applyVars χs Y) (χs ▶ᵗ B)
  → Value U
  → reveal-function X A Y B F · V —↠[ keep ∷ (χs ++χ (keep ∷ [])) ] U
reveal-function-return {F = F} {V} {U} {χs} X A Y B vF vV body vU =
    reveal-function X A Y B F · V
  —→[ keep ]⟨ pure-step (β-reveal-⇒ vF vV) ⟩
    (F · (V ↓ seal X A)) ↑ unseal Y B
  —↠[ χs ]⟨ unseal-trace Y B body ⟩+
    (U ↓ seal (applyVars χs Y) (χs ▶ᵗ B))
      ↑ unseal (applyVars χs Y) (χs ▶ᵗ B)
  —→[ keep ]⟨ pure-step (conceal-reveal vU) ⟩
    U ∎[]

typed-reveal-function-return : ∀ {Δ Δ′} {Σ : TyStore Δ}
    {F V : Term Δ} {Z : Term Δ′} {χs : StoreChanges Δ Δ′} {X A Y B}
  → Σ ∋ X ⦂ A → Σ ∋ Y ⦂ B
  → Value F → Value V
  → ⟨ Δ , Σ , [] ⟩ ⊢ F ⦂ (＇ X ⇒ ＇ Y)
  → ⟨ Δ , Σ , [] ⟩ ⊢ V ⦂ A
  → F · (V ↓ seal X A) —↠[ χs ] Z → Value Z
  → ∃[ U ] Value U × (⟨ Δ′ , χs ▶ˢ Σ , [] ⟩ ⊢ U ⦂ χs ▶ᵗ B)
      × (Z ≡ U ↓ seal (applyVars χs Y) (χs ▶ᵗ B))
      × (reveal-function X A Y B F · V
          —↠[ keep ∷ (χs ++χ (keep ∷ [])) ] U)
typed-reveal-function-return {Σ = Σ} {Z = Z} {χs} {X} {A} {Y} {B}
    entryX entryY vF vV typedF typedV body vZ
    with canonical-payload (changed-entry χs entryY) vZ
      (subst≡ (λ T → ⟨ _ , χs ▶ˢ Σ , [] ⟩ ⊢ Z ⦂ T)
        (changed-variable-type χs Y)
        (multi-preservation (⊢· typedF (⊢conceal (⊢↓-seal entryX) typedV))
          body))
typed-reveal-function-return {χs = χs} {X} {A} {Y} {B}
    entryX entryY vF vV typedF typedV body vZ | U , vU , typedU , refl =
  U , vU , typedU , refl , reveal-function-return X A Y B vF vV body vU

reveal-function-blame : ∀ {Δ Δ′} {F V : Term Δ} {χs : StoreChanges Δ Δ′}
    X A Y B
  → Value F → Value V → F · (V ↓ seal X A) —↠[ χs ] blame
  → reveal-function X A Y B F · V
      —↠[ keep ∷ (χs ++χ (keep ∷ [])) ] blame
reveal-function-blame {F = F} {V} {χs} X A Y B vF vV body =
    reveal-function X A Y B F · V
  —→[ keep ]⟨ pure-step (β-reveal-⇒ vF vV) ⟩
    (F · (V ↓ seal X A)) ↑ unseal Y B
  —↠[ χs ]⟨ unseal-trace Y B body ⟩+
    blame ↑ unseal (applyVars χs Y) (χs ▶ᵗ B)
  —→[ keep ]⟨ pure-step blame-reveal ⟩
    blame ∎[]

reveal-function-store : ∀ {Δ Δ′} (χs : StoreChanges Δ Δ′) (Σ : TyStore Δ)
  → (keep ∷ (χs ++χ (keep ∷ []))) ▶ˢ Σ ≡ χs ▶ˢ Σ
reveal-function-store χs Σ = sym (applyStores-++ χs (keep ∷ []) Σ)

-- Nominal seal lifting of a value relation. This retains the two concrete
-- seal names and representations. It does not relate a name to its
-- representation type, and it is only decoded by matching unseals.

data SealedValues {Δᴵ Δᴾ} (Xᴵ : TyVar Δᴵ) (Rᴵ : Ty Δᴵ)
    (Xᴾ : TyVar Δᴾ) (Rᴾ : Ty Δᴾ)
    (S : Term Δᴵ → Term Δᴾ → Set) : Term Δᴵ → Term Δᴾ → Set where
  related-seals : ∀ {Uᴵ Uᴾ}
    → Value Uᴵ → Value Uᴾ → S Uᴵ Uᴾ
    → SealedValues Xᴵ Rᴵ Xᴾ Rᴾ S
        (Uᴵ ↓ seal Xᴵ Rᴵ) (Uᴾ ↓ seal Xᴾ Rᴾ)

related-function-reveals-return : ∀ {Δᴵ Δᴾ Δᴵ′ Δᴾ′}
    {Fᴵ Vᴵ : Term Δᴵ} {Fᴾ Vᴾ : Term Δᴾ}
    {Zᴵ : Term Δᴵ′} {Zᴾ : Term Δᴾ′}
    {χsᴵ : StoreChanges Δᴵ Δᴵ′} {χsᴾ : StoreChanges Δᴾ Δᴾ′}
    Xᴵ Aᴵ Yᴵ Bᴵ Xᴾ Aᴾ Yᴾ Bᴾ
  → Value Fᴵ → Value Vᴵ → Value Fᴾ → Value Vᴾ
  → Fᴵ · (Vᴵ ↓ seal Xᴵ Aᴵ) —↠[ χsᴵ ] Zᴵ
  → Fᴾ · (Vᴾ ↓ seal Xᴾ Aᴾ) —↠[ χsᴾ ] Zᴾ
  → (S : Term Δᴵ′ → Term Δᴾ′ → Set)
  → SealedValues (applyVars χsᴵ Yᴵ) (χsᴵ ▶ᵗ Bᴵ)
      (applyVars χsᴾ Yᴾ) (χsᴾ ▶ᵗ Bᴾ) S Zᴵ Zᴾ
  → ∃[ Uᴵ ] ∃[ Uᴾ ]
      (reveal-function Xᴵ Aᴵ Yᴵ Bᴵ Fᴵ · Vᴵ
        —↠[ keep ∷ (χsᴵ ++χ (keep ∷ [])) ] Uᴵ)
      × (reveal-function Xᴾ Aᴾ Yᴾ Bᴾ Fᴾ · Vᴾ
        —↠[ keep ∷ (χsᴾ ++χ (keep ∷ [])) ] Uᴾ)
      × S Uᴵ Uᴾ
related-function-reveals-return Xᴵ Aᴵ Yᴵ Bᴵ Xᴾ Aᴾ Yᴾ Bᴾ
    vFᴵ vVᴵ vFᴾ vVᴾ bodyᴵ bodyᴾ S
    (related-seals {Uᴵ} {Uᴾ} vUᴵ vUᴾ related) =
  Uᴵ , Uᴾ , reveal-function-return Xᴵ Aᴵ Yᴵ Bᴵ vFᴵ vVᴵ bodyᴵ vUᴵ ,
  reveal-function-return Xᴾ Aᴾ Yᴾ Bᴾ vFᴾ vVᴾ bodyᴾ vUᴾ , related
