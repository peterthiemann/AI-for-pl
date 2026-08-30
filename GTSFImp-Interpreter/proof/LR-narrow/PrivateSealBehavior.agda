module proof.LR-narrow.PrivateSealBehavior where

-- File Charter:
--   * Certifies identity closures carrying arbitrary matching seal adapters.
--   * Proves application returns every value argument unchanged, retaining
--     the physical store and preserving any relation on endpoint arguments.
--   * Transports certificates through lookup-preserving store embeddings.
--   * Proof-local experiment: no assumed compatibility fields or live LR edits.

open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; ∃-syntax)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym) renaming (subst to subst≡)

open import Types
open import TyStore
open import TermCtx using (Z)
open import CastTerms
open import Conversion
open import Reduction
open import Consistency using (_↪ᵗ_; toRenameᵗ)
open import proof.TypeInTermSubst using (StoreRename)
open import proof.Reduction using (_++χ_; composeReduction)
open import proof.LR-narrow.SlotLifting using (rename↑-identity)
open import proof.LR-narrow.TypeRenamingComposition using (pack↑; apply↑)
import proof.LR-narrow.EscapingSealExperiment as Escaping

-- This is a syntax certificate, not an assumed behavioral specification.
-- Each adapter names an actual slot in the physical store. Its application
-- behavior is proved by induction below, without making that slot visible
-- to the semantic world or identifying it with another slot.

data PrivateIdentity {Δ} (Σ : TyStore Δ) : Ty Δ → Term Δ → Set where
  identity : ∀ {A} → PrivateIdentity Σ A (ƛ (` 0))

  seal-adapter : ∀ {X R F}
    → Σ ∋ X ⦂ R
    → PrivateIdentity Σ (＇ X) F
    → PrivateIdentity Σ R (F ↑ (seal X R ↦↑ unseal X R))

  identity-adapter : ∀ {A F}
    → PrivateIdentity Σ A F
    → PrivateIdentity Σ A (F ↑ (id↓ A ↦↑ id↑ A))

private-value : ∀ {Δ} {Σ : TyStore Δ} {A F}
  → PrivateIdentity Σ A F → Value F
private-value identity = ƛ (` 0)
private-value (seal-adapter entry p) = private-value p ↑ fun
private-value (identity-adapter p) = private-value p ↑ fun

private-typed : ∀ {Δ} {Σ : TyStore Δ} {A F}
  → PrivateIdentity Σ A F → ⟨ Δ , Σ , [] ⟩ ⊢ F ⦂ (A ⇒ A)
private-typed identity = ⊢ƛ (⊢` Z)
private-typed (seal-adapter entry p) =
  ⊢reveal (⊢↑-⇒ (⊢↓-seal entry) (⊢↑-unseal entry)) (private-typed p)
private-typed (identity-adapter p) =
  ⊢reveal (⊢↑-⇒ ⊢↓-id ⊢↑-id) (private-typed p)

private-rename : ∀ {Δ Δ′} {Σ : TyStore Δ} {Σ′ : TyStore Δ′}
    (ρ : Δ ↪ᵗ Δ′) {A F}
  → StoreRename (toRenameᵗ ρ) Σ Σ′
  → PrivateIdentity Σ A F
  → PrivateIdentity Σ′ (renameᵗ (toRenameᵗ ρ) A) (renameᵗᵐ ρ F)
private-rename ρ h identity = identity
private-rename ρ h (seal-adapter entry p) =
  seal-adapter (h entry) (private-rename ρ h p)
private-rename ρ h (identity-adapter p) =
  identity-adapter (private-rename ρ h p)

-- No allocation is performed while calling a certified identity. Retain
-- this fact in the trace itself, rather than just equating final stores.

data OnlyKeeps {Δ} : StoreChanges Δ Δ → Set where
  done : OnlyKeeps []
  more : ∀ {χs} → OnlyKeeps χs → OnlyKeeps (keep ∷ χs)

only-keeps-++ : ∀ {Δ} {χs ψs : StoreChanges Δ Δ}
  → OnlyKeeps χs → OnlyKeeps ψs → OnlyKeeps (χs ++χ ψs)
only-keeps-++ done q = q
only-keeps-++ (more p) q = more (only-keeps-++ p q)

only-keeps-store : ∀ {Δ} {χs : StoreChanges Δ Δ}
  → OnlyKeeps χs → (Σ : TyStore Δ) → χs ▶ˢ Σ ≡ Σ
only-keeps-store done Σ = refl
only-keeps-store (more p) Σ = only-keeps-store p Σ

only-keeps-term : ∀ {Δ} {χs : StoreChanges Δ Δ}
  → OnlyKeeps χs → (M : Term Δ) → χs ▶ᵀ M ≡ M
only-keeps-term done M = refl
only-keeps-term (more p) M = only-keeps-term p M

private-changes : ∀ {Δ} {Σ : TyStore Δ} {A F}
  → PrivateIdentity Σ A F → StoreChanges Δ Δ
private-changes identity = keep ∷ []
private-changes (seal-adapter entry p) =
  keep ∷ (private-changes p ++χ (keep ∷ []))
private-changes (identity-adapter p) =
  keep ∷ keep ∷ (private-changes p ++χ (keep ∷ []))

private-keeps : ∀ {Δ} {Σ : TyStore Δ} {A F} (p : PrivateIdentity Σ A F)
  → OnlyKeeps (private-changes p)
private-keeps identity = more done
private-keeps (seal-adapter entry p) =
  more (only-keeps-++ (private-keeps p) (more done))
private-keeps (identity-adapter p) =
  more (more (only-keeps-++ (private-keeps p) (more done)))

-- Extend the standard local chain notation to a nonempty reused tail.
infixr 2 _—↠[_]⟨_⟩+_
_—↠[_]⟨_⟩+_ : ∀ {Δ Δ′ Δ″} (M : Term Δ) {N : Term Δ′} {P : Term Δ″}
  → (χs : StoreChanges Δ Δ′) → M —↠[ χs ] N
  → ∀ {ψs : StoreChanges Δ′ Δ″} → N —↠[ ψs ] P
  → M —↠[ χs ++χ ψs ] P
M —↠[ χs ]⟨ trace ⟩+ rest = composeReduction trace rest

reveal-keep-step : ∀ {Δ} {M N : Term Δ} {A B} (c : Conv↑ Δ A B)
  → M —→[ keep ] N → M ↑ c —→[ keep ] N ↑ c
reveal-keep-step {M = M} {N = N} c step =
  subst≡ (λ P → M ↑ c —→[ keep ] P)
    (cong (apply↑ N) (rename↑-identity c)) (ξ-reveal step refl)

reveal-only-keeps : ∀ {Δ} {M N : Term Δ} {χs : StoreChanges Δ Δ} {A B}
  → OnlyKeeps χs → (c : Conv↑ Δ A B)
  → M —↠[ χs ] N → M ↑ c —↠[ χs ] N ↑ c
reveal-only-keeps {M = M} done c ↠-refl = (M ↑ c) ∎[]
reveal-only-keeps {M = M} {N = P} {χs = keep ∷ χs}
    (more p) c (↠-step {N = N} step rest) =
    M ↑ c
  —→[ keep ]⟨ reveal-keep-step c step ⟩
    N ↑ c
  —↠[ χs ]⟨ reveal-only-keeps p c rest ⟩
    P ↑ c ∎[]

-- The key elimination theorem is uniform in V, including values with
-- functions, universals, casts, or their own private seals.

private-application : ∀ {Δ} {Σ : TyStore Δ} {A F V}
  → (p : PrivateIdentity Σ A F) → Value V
  → F · V —↠[ private-changes p ] V
private-application {V = V} identity vV =
    (ƛ (` 0)) · V
  —→[ keep ]⟨ pure-step (β vV) ⟩
    V ∎[]
private-application {V = V} (seal-adapter {X} {R} {F} entry p) vV =
    (F ↑ (seal X R ↦↑ unseal X R)) · V
  —→[ keep ]⟨ pure-step (β-reveal-⇒ (private-value p) vV) ⟩
    (F · (V ↓ seal X R)) ↑ unseal X R
  —↠[ private-changes p ]⟨
      reveal-only-keeps (private-keeps p) (unseal X R)
        (private-application p (vV ↓ seal)) ⟩+
    (V ↓ seal X R) ↑ unseal X R
  —→[ keep ]⟨ pure-step (conceal-reveal vV) ⟩
    V ∎[]
private-application {V = V} (identity-adapter {A} {F} p) vV =
    (F ↑ (id↓ A ↦↑ id↑ A)) · V
  —→[ keep ]⟨ pure-step (β-reveal-⇒ (private-value p) vV) ⟩
    (F · (V ↓ id↓ A)) ↑ id↑ A
  —→[ keep ]⟨ reveal-keep-step (id↑ A)
      (ξ-·₂ (private-value p) (pure-step (id-conceal vV)) refl) ⟩
    (F · V) ↑ id↑ A
  —↠[ private-changes p ]⟨
      reveal-only-keeps (private-keeps p) (id↑ A)
        (private-application p vV) ⟩+
    V ↑ id↑ A
  —→[ keep ]⟨ pure-step (id-reveal vV) ⟩
    V ∎[]

-- A behavioral application principle across different PHYSICAL scopes.
-- S may be a visible-world value relation transported to these scopes;
-- neither S nor the certificate equates the private allocation histories.

private-pair-application : ∀ {Δᴵ Δᴾ} {Σᴵ : TyStore Δᴵ} {Σᴾ : TyStore Δᴾ}
    {Aᴵ Aᴾ Fᴵ Fᴾ Vᴵ Vᴾ}
  → (pᴵ : PrivateIdentity Σᴵ Aᴵ Fᴵ)
  → (pᴾ : PrivateIdentity Σᴾ Aᴾ Fᴾ)
  → Value Vᴵ → Value Vᴾ
  → ⟨ Δᴵ , Σᴵ , [] ⟩ ⊢ Vᴵ ⦂ Aᴵ
  → ⟨ Δᴾ , Σᴾ , [] ⟩ ⊢ Vᴾ ⦂ Aᴾ
  → (S : Term Δᴵ → Term Δᴾ → Set) → S Vᴵ Vᴾ
  → ∃[ Uᴵ ] ∃[ Uᴾ ]
      (Fᴵ · Vᴵ —↠[ private-changes pᴵ ] Uᴵ)
      × (Fᴾ · Vᴾ —↠[ private-changes pᴾ ] Uᴾ)
      × (private-changes pᴵ ▶ˢ Σᴵ ≡ Σᴵ)
      × (private-changes pᴾ ▶ˢ Σᴾ ≡ Σᴾ)
      × S Uᴵ Uᴾ
private-pair-application {Σᴵ = Σᴵ} {Σᴾ} {Vᴵ = Vᴵ} {Vᴾ}
    pᴵ pᴾ vVᴵ vVᴾ typedᴵ typedᴾ S related =
  Vᴵ , Vᴾ , private-application pᴵ vVᴵ , private-application pᴾ vVᴾ ,
  only-keeps-store (private-keeps pᴵ) Σᴵ ,
  only-keeps-store (private-keeps pᴾ) Σᴾ , related

-- The earlier counterexample closures are instances for ANY closed root
-- representation, not just naturals. The private Z remains in the precise
-- certificate, whereas the imprecise certificate contains only Y′.

bare-certificate : ∀ {R : Ty 0}
  → PrivateIdentity
      (store-bind (store-bind store-empty R) (＇ Fin.zero))
      (＇ (Fin.suc Fin.zero)) Escaping.bare-function
bare-certificate = seal-adapter (Z∋ refl) identity

wrapped-certificate : ∀ {R : Ty 0}
  → PrivateIdentity
      (store-bind (store-bind (store-bind store-empty R) (＇ Fin.zero))
        (＇ Fin.zero))
      (＇ (Fin.suc (Fin.suc Fin.zero))) Escaping.wrapped-function
wrapped-certificate = seal-adapter (S-bind∋ (Z∋ refl) refl)
  (identity-adapter (seal-adapter (Z∋ refl) identity))
