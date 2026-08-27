module proof.LR-narrow.AliasWorld where

-- File Charter:
--   * World-level alias coherence: what the cast and reveal analyses
--     may assume about an alias-mode center's semantic entry.  The
--     accessors are currently backed by the worlds' alias-freeness
--     (`noAlias`); the alias bind world replaces the bodies with real
--     entry coherence while keeping the signatures, so consumers are
--     already written against the alias-general interface.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst)

open import Types
open import CastTerms using (Term)
import Imprecision as I

open import LR-narrow.World
open import proof.LR-narrow.RevealAtomic using
  (rename-variable-inversion)

-- An alias-mode center carries an alias atom.

world-alias-atom : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (Z : TyVar Δᶜ) {T : Ty Δᶜ}
  → impEnv (core W) Z ≡ I.X⊑ᵗ T
  → AliasSemanticAtom (core W) Z T
world-alias-atom W Z eq
    with subst (SemanticEntry (core W) Z) eq (semanticEntry W Z)
       | aliasEntry W Z eq
world-alias-atom W Z eq | .(alias-entry a) | is-alias a = a

-- No embedded imprecise type reaches an alias-mode center: the
-- alias atom's occupant refutation applies to the inverted variable.

alias-no-imprecise-target : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    {Z : TyVar Δᶜ} {T : Ty Δᶜ} {Dᴵ : Ty Δᴵ}
  → impEnv (core W) Z ≡ I.X⊑ᵗ T
  → embedImprecise (core W) Dᴵ ≡ ＇ Z
  → ⊥
alias-no-imprecise-target W {Z = Z} eq tgt≡
    with rename-variable-inversion _ tgt≡
alias-no-imprecise-target W {Z = Z} eq tgt≡ | Y , _ , ρY≡ =
  aliasNoTargetOccupant (world-alias-atom W Z eq) (Y , ρY≡)

-- Rebuilding an inhabited alias slot at another premise: the seal
-- is kept and the payload is mapped, with the representative's
-- precise name and embedding equation available to the map.

alias-holds-chain : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z : TyVar Δᶜ} {T B B′ : Ty Δᶜ}
    {ℛ ℛ′ : PayloadRelation W}
    {p : impEnv W I.⊢ T ⊑ B} {p′ : impEnv W I.⊢ T ⊑ B′}
    {Vᴵ Vᴵ′ : Term Δᴵ} {Vᴾ : Term Δᴾ}
    (entry : SemanticEntry W Z mode) (eq : mode ≡ I.X⊑ᵗ T)
  → (∀ (rep : TyVar Δᴾ)
      → embedPrecise W (＇ rep) ≡ T
      → ∀ {Uᴾ : Term Δᴾ} → ℛ p Vᴵ Uᴾ → ℛ′ p′ Vᴵ′ Uᴾ)
  → AliasAtomHolds ℛ entry eq p Vᴵ Vᴾ
  → AliasAtomHolds ℛ′ entry eq p′ Vᴵ′ Vᴾ
alias-holds-chain (paired-entry a) eq f ()
alias-holds-chain (dynamic-entry a) () f holds
alias-holds-chain (target-entry a) () f holds
alias-holds-chain (alias-entry a) refl f
    (alias-holds Uᴾ shape rel) =
  alias-holds Uᴾ shape (f (aliasRepName a) (aliasRep-eq a) rel)

-- An alias-mode center's entry is an alias entry, so the paired
-- slot predicate cannot hold there.

paired-holds-subst : ∀ {Δᴾ Δᴵ Δᶜ} {Wc : CoreWorld Δᴾ Δᴵ Δᶜ}
    {Z : TyVar Δᶜ} {mode mode′ : I.VarImp Δᶜ}
    (eq : mode ≡ mode′)
    {entry : SemanticEntry Wc Z mode}
    {ℛ : PayloadRelation Wc}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → PairedAtomHolds ℛ entry Vᴵ Vᴾ
  → PairedAtomHolds ℛ (subst (SemanticEntry Wc Z) eq entry) Vᴵ Vᴾ
paired-holds-subst refl h = h

alias-mode-no-paired-holds : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    {Z : TyVar Δᶜ} {T : Ty Δᶜ} {ℛ : PayloadRelation (core W)}
    {Vᴵ : Term Δᴵ} {Vᴾ : Term Δᴾ}
  → impEnv (core W) Z ≡ I.X⊑ᵗ T
  → PairedAtomHolds ℛ (semanticEntry W Z) Vᴵ Vᴾ
  → ⊥
alias-mode-no-paired-holds W {Z = Z} eq holds
    with subst (SemanticEntry (core W) Z) eq (semanticEntry W Z)
       | aliasEntry W Z eq
       | paired-holds-subst eq holds
alias-mode-no-paired-holds W {Z = Z} eq holds
    | .(alias-entry a) | is-alias a | ()
