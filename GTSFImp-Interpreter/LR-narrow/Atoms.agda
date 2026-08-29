module LR-narrow.Atoms where

-- File Charter:
--   * Defines semantic slots indexed by their center-variable mode.
--   * A paired slot records the representation types bound at its endpoint
--     variables and their imprecision; a dynamic slot records the precise
--     representation and its imprecision below ★.  Sealed values at a slot
--     are related exactly when their payloads are related at the recorded
--     imprecision: the slot relation is canonical, hence Kripke.
--   * Records endpoint non-occupancy on one-sided slots.  A target-only slot
--     retains its runtime representative for scoped pending-bind proofs, but
--     remains inert in the ordinary value relation because imprecision has no
--     ★⊑X clause.
--   * Reindexes slots through paired and either-sided fresh store bindings.
--   * The payload relation is a parameter of the slot predicates; the
--     logical relation supplies itself at the next lower index.

open import Data.List using ([])
open import Data.Nat using (ℕ; suc; s≤s; z≤n)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; Σ-syntax)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; refl; sym; trans)
  renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
open import Conversion using (seal)
open import Consistency using (toRenameᵗ; keep)
import Imprecision as I
open import proof.ImprecisionConsistency using
  (fin-suc-injective; rename-⊑; shift-star-map; shift-alias-map)
open import LR-narrow.WorldCore

------------------------------------------------------------------------
-- Slots
------------------------------------------------------------------------

-- An occurrence in a renamed type is the image of an occurrence.

rename-∈ᵗ-inversion : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) {Y : TyVar Δ′} (A : Ty Δ)
  → Y ∈ᵗ renameᵗ ρ A
  → Σ[ Y′ ∈ TyVar Δ ] (Y ≡ ρ Y′) × (Y′ ∈ᵗ A)
rename-∈ᵗ-inversion ρ (＇ X) var-∈ = X , refl , var-∈
rename-∈ᵗ-inversion ρ (A ⇒ B) (∈-fun-left occurs)
    with rename-∈ᵗ-inversion ρ A occurs
rename-∈ᵗ-inversion ρ (A ⇒ B) (∈-fun-left occurs)
    | Y′ , refl , occurs′ = Y′ , refl , ∈-fun-left occurs′
rename-∈ᵗ-inversion ρ (A ⇒ B) (∈-fun-right no-occur occurs)
    with rename-∈ᵗ-inversion ρ B occurs
rename-∈ᵗ-inversion ρ (A ⇒ B) (∈-fun-right no-occur occurs)
    | Y′ , refl , occurs′ =
      Y′ , refl , occurs-right (occurs? Y′ A) occurs′
  where
  occurs-right : ∀ {Y′} → Occurs? Y′ A → Y′ ∈ᵗ B → Y′ ∈ᵗ A ⇒ B
  occurs-right (present occurs-A) occursB = ∈-fun-left occurs-A
  occurs-right (absent no-occur-A) occursB =
    ∈-fun-right no-occur-A occursB
rename-∈ᵗ-inversion ρ (`∀ A) (∈-all occurs)
    with rename-∈ᵗ-inversion (extᵗ ρ) A occurs
rename-∈ᵗ-inversion ρ (`∀ A) (∈-all occurs)
    | Fin.zero , () , occurs′
rename-∈ᵗ-inversion ρ (`∀ A) (∈-all occurs)
    | Fin.suc Y′ , eq , occurs′ =
  Y′ , fin-suc-injective eq , ∈-all occurs′

-- Every occurrence in a shifted type is positive, and shifting
-- strictly raises every occurrence.

shift-∈ᵗ-inversion : ∀ {Δ} {Y : TyVar (suc Δ)} (A : Ty Δ)
  → Y ∈ᵗ ⇑ᵗ A
  → Σ[ Y′ ∈ TyVar Δ ] (Y ≡ Fin.suc Y′) × (Y′ ∈ᵗ A)
shift-∈ᵗ-inversion A occurs = rename-∈ᵗ-inversion Fin.suc A occurs

-- A store lookup shifts the bound type past the entry itself, so a
-- bound variable never occurs in its own representation type.

store-∋-¬∈ : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ} {B : Ty Δ}
  → Σ ∋ X ⦂ B
  → X ∈ᵗ B
  → ⊥
store-∋-¬∈ (Z∋ {A = A} refl) occurs
    with shift-∈ᵗ-inversion A occurs
store-∋-¬∈ (Z∋ {A = A} refl) occurs | Y′ , () , occurs′
store-∋-¬∈ (S-lift∋ {A = A} bound refl) occurs
    with shift-∈ᵗ-inversion A occurs
store-∋-¬∈ (S-lift∋ {A = A} bound refl) occurs
    | Y′ , eq , occurs′ =
  store-∋-¬∈ bound
    (subst≡ (_∈ᵗ A) (sym (fin-suc-injective eq)) occurs′)
store-∋-¬∈ (S-bind∋ {A = A} bound refl) occurs
    with shift-∈ᵗ-inversion A occurs
store-∋-¬∈ (S-bind∋ {A = A} bound refl) occurs
    | Y′ , eq , occurs′ =
  store-∋-¬∈ bound
    (subst≡ (_∈ᵗ A) (sym (fin-suc-injective eq)) occurs′)

store-∋-∉ : ∀ {Δ} {Σ : TyStore Δ} {X : TyVar Δ} {B : Ty Δ}
  → Σ ∋ X ⦂ B
  → X ∉ᵗ B
store-∋-∉ {X = X} {B = B} bound with occurs? X B
store-∋-∉ bound | present occurs = ⊥-elim (store-∋-¬∈ bound occurs)
store-∋-∉ bound | absent no-occur = no-occur

record SemanticAtom {Δᴾ Δᴵ Δᶜ}
    (W : CoreWorld Δᴾ Δᴵ Δᶜ) (Z : TyVar Δᶜ) : Set where
  constructor semantic-atom
  field
    preciseVariable : TyVar Δᴾ
    impreciseVariable : TyVar Δᴵ
    preciseAligned :
      toRenameᵗ (preciseEmbedding W) preciseVariable ≡ Z
    impreciseAligned :
      toRenameᵗ (impreciseEmbedding W) impreciseVariable ≡ Z
    preciseRep : Ty Δᴾ
    impreciseRep : Ty Δᴵ
    rep-related : preciseRep ⊑ᵂ⟨ W ⟩ impreciseRep
    preciseBound : preciseStore W ∋ preciseVariable ⦂ preciseRep
    impreciseBound : impreciseStore W ∋ impreciseVariable ⦂ impreciseRep

open SemanticAtom public

record DynamicSemanticAtom {Δᴾ Δᴵ Δᶜ}
    (W : CoreWorld Δᴾ Δᴵ Δᶜ) (Z : TyVar Δᶜ) : Set where
  constructor dynamic-semantic-atom
  field
    dynamicPreciseVariable : TyVar Δᴾ
    dynamicPreciseAligned :
      toRenameᵗ (preciseEmbedding W) dynamicPreciseVariable ≡ Z
    dynamicNoTargetOccupant :
      (Σ[ Y ∈ TyVar Δᴵ ]
        toRenameᵗ (impreciseEmbedding W) Y ≡ Z) → ⊥
    dynamicRep : Ty Δᴾ
    dynamicRep-related :
      impEnv W I.⊢ embedPrecise W dynamicRep ⊑ ★
    dynamicFresh : ∀ {Y : TyVar Δᶜ}
      → Y ∈ᵗ embedPrecise W dynamicRep
      → Z Fin.< Y
    dynamicBound :
      preciseStore W ∋ dynamicPreciseVariable ⦂ dynamicRep

open DynamicSemanticAtom public

record TargetSemanticAtom {Δᴾ Δᴵ Δᶜ}
    (W : CoreWorld Δᴾ Δᴵ Δᶜ) (Z : TyVar Δᶜ) : Set where
  constructor target-semantic-atom
  field
    targetImpreciseVariable : TyVar Δᴵ
    targetImpreciseAligned :
      toRenameᵗ (impreciseEmbedding W) targetImpreciseVariable ≡ Z
    targetNoPreciseOccupant :
      (Σ[ X ∈ TyVar Δᴾ ]
        toRenameᵗ (preciseEmbedding W) X ≡ Z) → ⊥
    targetRep : Ty Δᴵ
    targetBound :
      impreciseStore W ∋ targetImpreciseVariable ⦂ targetRep

open TargetSemanticAtom public

-- An alias slot is a precise-only allocation whose representative type is
-- recorded in the mode: the center variable unfolds to the embedding of the
-- bound representation type.  Unlike the dynamic slot it carries no
-- imprecision derivation -- the `alias` rule supplies the premise at each use.

record AliasSemanticAtom {Δᴾ Δᴵ Δᶜ}
    (W : CoreWorld Δᴾ Δᴵ Δᶜ) (Z : TyVar Δᶜ) (T : Ty Δᶜ) : Set where
  constructor alias-semantic-atom
  field
    aliasPreciseVariable : TyVar Δᴾ
    aliasPreciseAligned :
      toRenameᵗ (preciseEmbedding W) aliasPreciseVariable ≡ Z
    aliasNoTargetOccupant :
      (Σ[ Y ∈ TyVar Δᴵ ]
        toRenameᵗ (impreciseEmbedding W) Y ≡ Z) → ⊥
    aliasRep : Ty Δᴾ
    aliasRep-eq : embedPrecise W aliasRep ≡ T
    aliasFresh : ∀ {Y : TyVar Δᶜ} → Y ∈ᵗ T → Z Fin.< Y
    aliasBound :
      preciseStore W ∋ aliasPreciseVariable ⦂ aliasRep

open AliasSemanticAtom public

data SemanticEntry {Δᴾ Δᴵ Δᶜ} (W : CoreWorld Δᴾ Δᴵ Δᶜ)
    (Z : TyVar Δᶜ) : I.VarImp Δᶜ → Set where
  paired-entry : ∀ {mode}
    → SemanticAtom W Z
    → SemanticEntry W Z mode
  dynamic-entry : DynamicSemanticAtom W Z → SemanticEntry W Z I.X⊑★
  target-entry : TargetSemanticAtom W Z → SemanticEntry W Z I.X⊑★
  alias-entry : ∀ {T}
    → AliasSemanticAtom W Z T
    → SemanticEntry W Z (I.X⊑ᵗ T)

------------------------------------------------------------------------
-- Canonical slot relations below a payload relation
------------------------------------------------------------------------

-- The payload relation is supplied by the logical relation at the next
-- lower step index; it is indexed by the center imprecision of the payload
-- types.

PayloadRelation : ∀ {Δᴾ Δᴵ Δᶜ} → CoreWorld Δᴾ Δᴵ Δᶜ → Set₁
PayloadRelation {Δᴾ} {Δᴵ} {Δᶜ} W =
  ∀ {Aᴾ Aᴵ : Ty Δᶜ} → impEnv W I.⊢ Aᴾ ⊑ Aᴵ
  → Term Δᴵ → Term Δᴾ → Set

-- Sealed values at a paired slot: both payloads are related at the
-- recorded representation imprecision.

record AtomHolds {Δᴾ Δᴵ Δᶜ} {W : CoreWorld Δᴾ Δᴵ Δᶜ}
    {Z} (ℛ : PayloadRelation W) (a : SemanticAtom W Z)
    (Vᴵ : Term Δᴵ) (Vᴾ : Term Δᴾ) : Set where
  constructor atom-holds
  field
    impreciseSealed : Term Δᴵ
    preciseSealed : Term Δᴾ
    imprecise-sealed-shape :
      Vᴵ ≡ impreciseSealed ↓ seal (impreciseVariable a) (impreciseRep a)
    precise-sealed-shape :
      Vᴾ ≡ preciseSealed ↓ seal (preciseVariable a) (preciseRep a)
    payloads-related : ℛ (rep-related a) impreciseSealed preciseSealed

open AtomHolds public

-- A sealed precise value at a dynamic slot against an imprecise dynamic
-- value: the precise payload is related to the imprecise value below ★.

record DynamicHolds {Δᴾ Δᴵ Δᶜ} {W : CoreWorld Δᴾ Δᴵ Δᶜ}
    {Z} (ℛ : PayloadRelation W) (a : DynamicSemanticAtom W Z)
    (Vᴵ : Term Δᴵ) (Vᴾ : Term Δᴾ) : Set where
  constructor dynamic-holds
  field
    dynamicSealed : Term Δᴾ
    dynamic-sealed-shape :
      Vᴾ ≡ dynamicSealed ↓ seal (dynamicPreciseVariable a) (dynamicRep a)
    dynamic-payload-related : ℛ (dynamicRep-related a) Vᴵ dynamicSealed

open DynamicHolds public

-- A sealed precise value at an alias slot: the payload below the seal
-- is related to the imprecise value at the alias premise, which
-- relates the recorded representative to the right endpoint.

record AliasHolds {Δᴾ Δᴵ Δᶜ} {W : CoreWorld Δᴾ Δᴵ Δᶜ}
    {Z} {T B : Ty Δᶜ} (ℛ : PayloadRelation W)
    (a : AliasSemanticAtom W Z T)
    (p : impEnv W I.⊢ T ⊑ B)
    (Vᴵ : Term Δᴵ) (Vᴾ : Term Δᴾ) : Set where
  constructor alias-holds
  field
    aliasSealed : Term Δᴾ
    alias-sealed-shape :
      Vᴾ ≡ aliasSealed
        ↓ seal (aliasPreciseVariable a) (aliasRep a)
    alias-payload-related : ℛ p Vᴵ aliasSealed

open AliasHolds public

PairedAtomHolds : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z : TyVar Δᶜ}
  → PayloadRelation W
  → SemanticEntry W Z mode
  → Term Δᴵ → Term Δᴾ → Set
PairedAtomHolds ℛ (paired-entry a) Vᴵ Vᴾ = AtomHolds ℛ a Vᴵ Vᴾ
PairedAtomHolds ℛ (dynamic-entry a) Vᴵ Vᴾ = ⊥
PairedAtomHolds ℛ (target-entry a) Vᴵ Vᴾ = ⊥
PairedAtomHolds ℛ (alias-entry a) Vᴵ Vᴾ = ⊥

DynamicAtomHolds : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z : TyVar Δᶜ}
  → PayloadRelation W
  → (entry : SemanticEntry W Z mode)
  → mode ≡ I.X⊑★
  → Term Δᴵ → Term Δᴾ → Set
DynamicAtomHolds ℛ (paired-entry a) eq Vᴵ Vᴾ = ⊥
DynamicAtomHolds ℛ (dynamic-entry a) refl Vᴵ Vᴾ = DynamicHolds ℛ a Vᴵ Vᴾ
DynamicAtomHolds ℛ (target-entry a) refl Vᴵ Vᴾ = ⊥
DynamicAtomHolds ℛ (alias-entry a) () Vᴵ Vᴾ

-- The value relation at an alias use of a slot: forced onto the alias
-- entry by mode disjointness; a paired slot never sits at the alias
-- mode.

AliasAtomHolds : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z : TyVar Δᶜ} {T B : Ty Δᶜ}
  → PayloadRelation W
  → (entry : SemanticEntry W Z mode)
  → mode ≡ I.X⊑ᵗ T
  → impEnv W I.⊢ T ⊑ B
  → Term Δᴵ → Term Δᴾ → Set
AliasAtomHolds ℛ (paired-entry a) eq p Vᴵ Vᴾ = ⊥
AliasAtomHolds ℛ (dynamic-entry a) () p Vᴵ Vᴾ
AliasAtomHolds ℛ (target-entry a) () p Vᴵ Vᴾ
AliasAtomHolds ℛ (alias-entry a) refl p Vᴵ Vᴾ =
  AliasHolds ℛ a p Vᴵ Vᴾ


-- The slot predicates are functorial in the payload relation.

PayloadMap : ∀ {Δᴾ Δᴵ Δᶜ} (W : CoreWorld Δᴾ Δᴵ Δᶜ)
  → PayloadRelation W → PayloadRelation W → Set
PayloadMap {Δᶜ = Δᶜ} W ℛ ℛ′ =
  ∀ {Aᴾ Aᴵ : Ty Δᶜ} {p : impEnv W I.⊢ Aᴾ ⊑ Aᴵ} {Vᴵ Vᴾ}
  → ℛ p Vᴵ Vᴾ → ℛ′ p Vᴵ Vᴾ

paired-holds-map : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z : TyVar Δᶜ}
    {ℛ ℛ′ : PayloadRelation W}
  → PayloadMap W ℛ ℛ′
  → (entry : SemanticEntry W Z mode)
  → ∀ {Vᴵ Vᴾ}
  → PairedAtomHolds ℛ entry Vᴵ Vᴾ
  → PairedAtomHolds ℛ′ entry Vᴵ Vᴾ
paired-holds-map f (paired-entry a)
    (atom-holds Uᴵ Uᴾ eqᴵ eqᴾ related) =
  atom-holds Uᴵ Uᴾ eqᴵ eqᴾ (f related)
paired-holds-map f (dynamic-entry a) ()
paired-holds-map f (target-entry a) ()
paired-holds-map f (alias-entry a) ()

dynamic-holds-map : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z : TyVar Δᶜ}
    {ℛ ℛ′ : PayloadRelation W}
  → PayloadMap W ℛ ℛ′
  → (entry : SemanticEntry W Z mode) (eq : mode ≡ I.X⊑★)
  → ∀ {Vᴵ Vᴾ}
  → DynamicAtomHolds ℛ entry eq Vᴵ Vᴾ
  → DynamicAtomHolds ℛ′ entry eq Vᴵ Vᴾ
dynamic-holds-map f (paired-entry a) eq ()
dynamic-holds-map f (dynamic-entry a) refl
    (dynamic-holds Uᴾ eqᴾ related) =
  dynamic-holds Uᴾ eqᴾ (f related)
dynamic-holds-map f (target-entry a) refl ()
dynamic-holds-map f (alias-entry a) () related

alias-holds-map : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z : TyVar Δᶜ} {T B : Ty Δᶜ}
    {ℛ ℛ′ : PayloadRelation W}
  → PayloadMap W ℛ ℛ′
  → (entry : SemanticEntry W Z mode) (eq : mode ≡ I.X⊑ᵗ T)
  → (p : impEnv W I.⊢ T ⊑ B)
  → ∀ {Vᴵ Vᴾ}
  → AliasAtomHolds ℛ entry eq p Vᴵ Vᴾ
  → AliasAtomHolds ℛ′ entry eq p Vᴵ Vᴾ
alias-holds-map f (paired-entry a) eq p ()
alias-holds-map f (dynamic-entry a) () p related
alias-holds-map f (target-entry a) () p related
alias-holds-map f (alias-entry a) refl p
    (alias-holds Uᴾ eqᴾ related) =
  alias-holds Uᴾ eqᴾ (f related)

dynamic-atom-no-target : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z : TyVar Δᶜ} {ℛ : PayloadRelation W}
    {Vᴵ Vᴾ}
    (entry : SemanticEntry W Z mode) (eq : mode ≡ I.X⊑★)
  → DynamicAtomHolds ℛ entry eq Vᴵ Vᴾ
  → (Σ[ Y ∈ TyVar Δᴵ ]
      toRenameᵗ (impreciseEmbedding W) Y ≡ Z) → ⊥
dynamic-atom-no-target (paired-entry a) eq ()
dynamic-atom-no-target (dynamic-entry a) refl related =
  dynamicNoTargetOccupant a
dynamic-atom-no-target (target-entry a) refl ()
dynamic-atom-no-target (alias-entry a) () related

alias-atom-no-target : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z : TyVar Δᶜ} {T B : Ty Δᶜ}
    {ℛ : PayloadRelation W} {p : impEnv W I.⊢ T ⊑ B} {Vᴵ Vᴾ}
    (entry : SemanticEntry W Z mode) (eq : mode ≡ I.X⊑ᵗ T)
  → AliasAtomHolds ℛ entry eq p Vᴵ Vᴾ
  → (Σ[ Y ∈ TyVar Δᴵ ]
      toRenameᵗ (impreciseEmbedding W) Y ≡ Z) → ⊥
alias-atom-no-target (paired-entry a) eq ()
alias-atom-no-target (dynamic-entry a) () related
alias-atom-no-target (target-entry a) () related
alias-atom-no-target (alias-entry a) refl related =
  aliasNoTargetOccupant a

alias-holds-payload : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z : TyVar Δᶜ} {T B : Ty Δᶜ}
    {ℛ : PayloadRelation W} {p : impEnv W I.⊢ T ⊑ B} {Vᴵ Vᴾ}
    (entry : SemanticEntry W Z mode) (eq : mode ≡ I.X⊑ᵗ T)
  → AliasAtomHolds ℛ entry eq p Vᴵ Vᴾ
  → Σ[ Uᴾ ∈ Term Δᴾ ] ℛ p Vᴵ Uᴾ
alias-holds-payload (paired-entry a) eq ()
alias-holds-payload (dynamic-entry a) () holds
alias-holds-payload (target-entry a) () holds
alias-holds-payload (alias-entry a) refl
    (alias-holds Uᴾ shape related) =
  Uᴾ , related

------------------------------------------------------------------------
-- Reindexing slots through fresh bindings
------------------------------------------------------------------------

-- Embedding a shifted endpoint type into the bound center context is the
-- shifted embedding.

embedPrecise-paired-shift : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : CoreWorld Δᴾ Δᴵ Δᶜ) (Aᴾ : Ty Δᴾ) (Aᴵ : Ty Δᴵ) (R : Ty Δᴾ)
  → embedPrecise (pairedBindCore W Aᴾ Aᴵ) (⇑ᵗ R)
      ≡ ⇑ᵗ (embedPrecise W R)
embedPrecise-paired-shift W Aᴾ Aᴵ R =
  trans (renameᵗ-comp Fin.suc (toRenameᵗ (keep (preciseEmbedding W))) R)
    (sym (renameᵗ-comp (toRenameᵗ (preciseEmbedding W)) Fin.suc R))

embedImprecise-paired-shift : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : CoreWorld Δᴾ Δᴵ Δᶜ) (Aᴾ : Ty Δᴾ) (Aᴵ : Ty Δᴵ) (R : Ty Δᴵ)
  → embedImprecise (pairedBindCore W Aᴾ Aᴵ) (⇑ᵗ R)
      ≡ ⇑ᵗ (embedImprecise W R)
embedImprecise-paired-shift W Aᴾ Aᴵ R =
  trans (renameᵗ-comp Fin.suc (toRenameᵗ (keep (impreciseEmbedding W))) R)
    (sym (renameᵗ-comp (toRenameᵗ (impreciseEmbedding W)) Fin.suc R))

embedPrecise-precise-shift : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : CoreWorld Δᴾ Δᴵ Δᶜ) (Aᴾ : Ty Δᴾ) (R : Ty Δᴾ)
  → embedPrecise (preciseBindCore W Aᴾ) (⇑ᵗ R)
      ≡ ⇑ᵗ (embedPrecise W R)
embedPrecise-precise-shift W Aᴾ R =
  trans (renameᵗ-comp Fin.suc (toRenameᵗ (keep (preciseEmbedding W))) R)
    (sym (renameᵗ-comp (toRenameᵗ (preciseEmbedding W)) Fin.suc R))

embedImprecise-precise-shift : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : CoreWorld Δᴾ Δᴵ Δᶜ) (Aᴾ : Ty Δᴾ) (R : Ty Δᴵ)
  → embedImprecise (preciseBindCore W Aᴾ) R
      ≡ ⇑ᵗ (embedImprecise W R)
embedImprecise-precise-shift W Aᴾ R =
  sym (renameᵗ-comp (toRenameᵗ (impreciseEmbedding W)) Fin.suc R)

embedPrecise-imprecise-shift : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : CoreWorld Δᴾ Δᴵ Δᶜ) (Aᴵ : Ty Δᴵ) (R : Ty Δᴾ)
  → embedPrecise (impreciseBindCore W Aᴵ) R
      ≡ ⇑ᵗ (embedPrecise W R)
embedPrecise-imprecise-shift W Aᴵ R =
  sym (renameᵗ-comp (toRenameᵗ (preciseEmbedding W)) Fin.suc R)

embedImprecise-imprecise-shift : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : CoreWorld Δᴾ Δᴵ Δᶜ) (Aᴵ : Ty Δᴵ) (R : Ty Δᴵ)
  → embedImprecise (impreciseBindCore W Aᴵ) (⇑ᵗ R)
      ≡ ⇑ᵗ (embedImprecise W R)
embedImprecise-imprecise-shift W Aᴵ R =
  trans (renameᵗ-comp Fin.suc (toRenameᵗ (keep (impreciseEmbedding W))) R)
    (sym (renameᵗ-comp (toRenameᵗ (impreciseEmbedding W)) Fin.suc R))

-- Transport of center imprecision along equalities of both endpoints.

transport-⊑ : ∀ {Δ} {μ : I.ImpEnv Δ} {A A′ B B′ : Ty Δ}
  → A′ ≡ A → B′ ≡ B → μ I.⊢ A ⊑ B → μ I.⊢ A′ ⊑ B′
transport-⊑ refl refl p = p

-- Center imprecision shifts behind any fresh binding: the new center does
-- not occur and the old modes are preserved.

shift-⊑ : ∀ {Δᶜ} {μ : I.ImpEnv Δᶜ} (v : I.VarImp (suc Δᶜ)) {A B : Ty Δᶜ}
  → μ I.⊢ A ⊑ B
  → I.extendᵐ v μ I.⊢ ⇑ᵗ A ⊑ ⇑ᵗ B
shift-⊑ {μ = μ} v p =
  rename-⊑ Fin.suc fin-suc-injective
    (shift-star-map {ν = μ} {v = v})
    (shift-alias-map {ν = μ} {v = v}) p

weaken-semantic-atom : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴾ : Ty Δᴾ)
  → (Aᴵ : Ty Δᴵ)
  → SemanticAtom W Z
  → SemanticAtom (pairedBindCore W Aᴾ Aᴵ) (Fin.suc Z)
weaken-semantic-atom {W = W} Aᴾ Aᴵ a =
  semantic-atom (Fin.suc (preciseVariable a))
    (Fin.suc (impreciseVariable a))
    (cong Fin.suc (preciseAligned a))
    (cong Fin.suc (impreciseAligned a))
    (⇑ᵗ (preciseRep a)) (⇑ᵗ (impreciseRep a))
    (transport-⊑ (embedPrecise-paired-shift W Aᴾ Aᴵ (preciseRep a))
      (embedImprecise-paired-shift W Aᴾ Aᴵ (impreciseRep a))
      (shift-⊑ I.X⊑X (rep-related a)))
    (S-bind∋ (preciseBound a) refl)
    (S-bind∋ (impreciseBound a) refl)

weaken-semantic-atom-precise : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴾ : Ty Δᴾ)
  → SemanticAtom W Z
  → SemanticAtom (preciseBindCore W Aᴾ) (Fin.suc Z)
weaken-semantic-atom-precise {W = W} Aᴾ a =
  semantic-atom (Fin.suc (preciseVariable a)) (impreciseVariable a)
    (cong Fin.suc (preciseAligned a))
    (cong Fin.suc (impreciseAligned a))
    (⇑ᵗ (preciseRep a)) (impreciseRep a)
    (transport-⊑ (embedPrecise-precise-shift W Aᴾ (preciseRep a))
      (embedImprecise-precise-shift W Aᴾ (impreciseRep a))
      (shift-⊑ I.X⊑★ (rep-related a)))
    (S-bind∋ (preciseBound a) refl)
    (impreciseBound a)

weaken-semantic-atom-imprecise : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴵ : Ty Δᴵ)
  → SemanticAtom W Z
  → SemanticAtom (impreciseBindCore W Aᴵ) (Fin.suc Z)
weaken-semantic-atom-imprecise {W = W} Aᴵ a =
  semantic-atom (preciseVariable a) (Fin.suc (impreciseVariable a))
    (cong Fin.suc (preciseAligned a))
    (cong Fin.suc (impreciseAligned a))
    (preciseRep a) (⇑ᵗ (impreciseRep a))
    (transport-⊑ (embedPrecise-imprecise-shift W Aᴵ (preciseRep a))
      (embedImprecise-imprecise-shift W Aᴵ (impreciseRep a))
      (shift-⊑ I.X⊑★ (rep-related a)))
    (preciseBound a)
    (S-bind∋ (impreciseBound a) refl)

weaken-dynamic-atom : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴾ : Ty Δᴾ)
  → (Aᴵ : Ty Δᴵ)
  → DynamicSemanticAtom W Z
  → DynamicSemanticAtom (pairedBindCore W Aᴾ Aᴵ) (Fin.suc Z)
weaken-dynamic-atom {W = W} {Z = Z} Aᴾ Aᴵ a =
  dynamic-semantic-atom (Fin.suc (dynamicPreciseVariable a))
    (cong Fin.suc (dynamicPreciseAligned a))
    no-target
    (⇑ᵗ (dynamicRep a))
    (transport-⊑ (embedPrecise-paired-shift W Aᴾ Aᴵ (dynamicRep a)) refl
      (shift-⊑ I.X⊑X (dynamicRep-related a)))
    fresh
    (S-bind∋ (dynamicBound a) refl)
  where
  fresh : ∀ {Y}
    → Y ∈ᵗ embedPrecise (pairedBindCore W Aᴾ Aᴵ) (⇑ᵗ (dynamicRep a))
    → Fin.suc Z Fin.< Y
  fresh {Y = Y} occurs
      with shift-∈ᵗ-inversion (embedPrecise W (dynamicRep a))
        (subst≡ (Y ∈ᵗ_)
          (embedPrecise-paired-shift W Aᴾ Aᴵ (dynamicRep a)) occurs)
  fresh occurs | Y′ , refl , occurs′ = s≤s (dynamicFresh a occurs′)

  no-target :
      (Σ[ Y ∈ TyVar _ ]
        toRenameᵗ (impreciseEmbedding
          (pairedBindCore W Aᴾ Aᴵ)) Y ≡ Fin.suc Z) → ⊥
  no-target (Fin.zero , ())
  no-target (Fin.suc Y , eq) =
    dynamicNoTargetOccupant a (Y , fin-suc-injective eq)

weaken-dynamic-atom-precise : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴾ : Ty Δᴾ)
  → DynamicSemanticAtom W Z
  → DynamicSemanticAtom (preciseBindCore W Aᴾ) (Fin.suc Z)
weaken-dynamic-atom-precise {W = W} {Z = Z} Aᴾ a =
  dynamic-semantic-atom (Fin.suc (dynamicPreciseVariable a))
    (cong Fin.suc (dynamicPreciseAligned a))
    no-target
    (⇑ᵗ (dynamicRep a))
    (transport-⊑ (embedPrecise-precise-shift W Aᴾ (dynamicRep a)) refl
      (shift-⊑ I.X⊑★ (dynamicRep-related a)))
    fresh
    (S-bind∋ (dynamicBound a) refl)
  where
  fresh : ∀ {Y}
    → Y ∈ᵗ embedPrecise (preciseBindCore W Aᴾ) (⇑ᵗ (dynamicRep a))
    → Fin.suc Z Fin.< Y
  fresh {Y = Y} occurs
      with shift-∈ᵗ-inversion (embedPrecise W (dynamicRep a))
        (subst≡ (Y ∈ᵗ_)
          (embedPrecise-precise-shift W Aᴾ (dynamicRep a)) occurs)
  fresh occurs | Y′ , refl , occurs′ = s≤s (dynamicFresh a occurs′)

  no-target :
      (Σ[ Y ∈ TyVar _ ]
        toRenameᵗ (impreciseEmbedding
          (preciseBindCore W Aᴾ)) Y ≡ Fin.suc Z) → ⊥
  no-target (Y , eq) =
    dynamicNoTargetOccupant a (Y , fin-suc-injective eq)

weaken-dynamic-atom-imprecise : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴵ : Ty Δᴵ)
  → DynamicSemanticAtom W Z
  → DynamicSemanticAtom (impreciseBindCore W Aᴵ) (Fin.suc Z)
weaken-dynamic-atom-imprecise {W = W} {Z = Z} Aᴵ a =
  dynamic-semantic-atom (dynamicPreciseVariable a)
    (cong Fin.suc (dynamicPreciseAligned a))
    no-target
    (dynamicRep a)
    (transport-⊑ (embedPrecise-imprecise-shift W Aᴵ (dynamicRep a)) refl
      (shift-⊑ I.X⊑★ (dynamicRep-related a)))
    fresh
    (dynamicBound a)
  where
  fresh : ∀ {Y}
    → Y ∈ᵗ embedPrecise (impreciseBindCore W Aᴵ) (dynamicRep a)
    → Fin.suc Z Fin.< Y
  fresh {Y = Y} occurs
      with shift-∈ᵗ-inversion (embedPrecise W (dynamicRep a))
        (subst≡ (Y ∈ᵗ_)
          (embedPrecise-imprecise-shift W Aᴵ (dynamicRep a)) occurs)
  fresh occurs | Y′ , refl , occurs′ = s≤s (dynamicFresh a occurs′)

  no-target :
      (Σ[ Y ∈ TyVar _ ]
        toRenameᵗ (impreciseEmbedding
          (impreciseBindCore W Aᴵ)) Y ≡ Fin.suc Z) → ⊥
  no-target (Fin.zero , ())
  no-target (Fin.suc Y , eq) =
    dynamicNoTargetOccupant a (Y , fin-suc-injective eq)

weaken-target-atom : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴾ : Ty Δᴾ)
  → (Aᴵ : Ty Δᴵ)
  → TargetSemanticAtom W Z
  → TargetSemanticAtom (pairedBindCore W Aᴾ Aᴵ) (Fin.suc Z)
weaken-target-atom {W = W} {Z = Z} Aᴾ Aᴵ a =
  target-semantic-atom (Fin.suc (targetImpreciseVariable a))
    (cong Fin.suc (targetImpreciseAligned a))
    no-precise (⇑ᵗ (targetRep a)) (S-bind∋ (targetBound a) refl)
  where
  no-precise :
      (Σ[ X ∈ TyVar _ ]
        toRenameᵗ (preciseEmbedding
          (pairedBindCore W Aᴾ Aᴵ)) X ≡ Fin.suc Z) → ⊥
  no-precise (Fin.zero , ())
  no-precise (Fin.suc X , eq) =
    targetNoPreciseOccupant a (X , fin-suc-injective eq)

weaken-target-atom-precise : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴾ : Ty Δᴾ)
  → TargetSemanticAtom W Z
  → TargetSemanticAtom (preciseBindCore W Aᴾ) (Fin.suc Z)
weaken-target-atom-precise {W = W} {Z = Z} Aᴾ a =
  target-semantic-atom (targetImpreciseVariable a)
    (cong Fin.suc (targetImpreciseAligned a))
    no-precise (targetRep a) (targetBound a)
  where
  no-precise :
      (Σ[ X ∈ TyVar _ ]
        toRenameᵗ (preciseEmbedding
          (preciseBindCore W Aᴾ)) X ≡ Fin.suc Z) → ⊥
  no-precise (Fin.zero , ())
  no-precise (Fin.suc X , eq) =
    targetNoPreciseOccupant a (X , fin-suc-injective eq)

weaken-target-atom-imprecise : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴵ : Ty Δᴵ)
  → TargetSemanticAtom W Z
  → TargetSemanticAtom (impreciseBindCore W Aᴵ) (Fin.suc Z)
weaken-target-atom-imprecise {W = W} {Z = Z} Aᴵ a =
  target-semantic-atom (Fin.suc (targetImpreciseVariable a))
    (cong Fin.suc (targetImpreciseAligned a))
    no-precise (⇑ᵗ (targetRep a)) (S-bind∋ (targetBound a) refl)
  where
  no-precise :
      (Σ[ X ∈ TyVar _ ]
        toRenameᵗ (preciseEmbedding
          (impreciseBindCore W Aᴵ)) X ≡ Fin.suc Z) → ⊥
  no-precise (X , eq) =
    targetNoPreciseOccupant a (X , fin-suc-injective eq)

weaken-alias-atom : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z} {T : Ty Δᶜ}
  → (Aᴾ : Ty Δᴾ)
  → (Aᴵ : Ty Δᴵ)
  → AliasSemanticAtom W Z T
  → AliasSemanticAtom (pairedBindCore W Aᴾ Aᴵ) (Fin.suc Z) (⇑ᵗ T)
weaken-alias-atom {W = W} {Z = Z} {T = T} Aᴾ Aᴵ a =
  alias-semantic-atom (Fin.suc (aliasPreciseVariable a))
    (cong Fin.suc (aliasPreciseAligned a))
    no-target
    (⇑ᵗ (aliasRep a))
    (trans
      (embedPrecise-paired-shift W Aᴾ Aᴵ (aliasRep a))
      (cong ⇑ᵗ (aliasRep-eq a)))
    fresh
    (S-bind∋ (aliasBound a) refl)
  where
  fresh : ∀ {Y} → Y ∈ᵗ ⇑ᵗ T → Fin.suc Z Fin.< Y
  fresh occurs with shift-∈ᵗ-inversion T occurs
  fresh occurs | Y′ , refl , occurs′ = s≤s (aliasFresh a occurs′)

  no-target :
      (Σ[ Y ∈ TyVar _ ]
        toRenameᵗ (impreciseEmbedding
          (pairedBindCore W Aᴾ Aᴵ)) Y ≡ Fin.suc Z) → ⊥
  no-target (Fin.zero , ())
  no-target (Fin.suc Y , eq) =
    aliasNoTargetOccupant a (Y , fin-suc-injective eq)

weaken-alias-atom-precise : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z} {T : Ty Δᶜ}
  → (Aᴾ : Ty Δᴾ)
  → AliasSemanticAtom W Z T
  → AliasSemanticAtom (preciseBindCore W Aᴾ) (Fin.suc Z) (⇑ᵗ T)
weaken-alias-atom-precise {W = W} {Z = Z} {T = T} Aᴾ a =
  alias-semantic-atom (Fin.suc (aliasPreciseVariable a))
    (cong Fin.suc (aliasPreciseAligned a))
    no-target
    (⇑ᵗ (aliasRep a))
    (trans (embedPrecise-precise-shift W Aᴾ (aliasRep a))
      (cong ⇑ᵗ (aliasRep-eq a)))
    fresh
    (S-bind∋ (aliasBound a) refl)
  where
  fresh : ∀ {Y} → Y ∈ᵗ ⇑ᵗ T → Fin.suc Z Fin.< Y
  fresh occurs with shift-∈ᵗ-inversion T occurs
  fresh occurs | Y′ , refl , occurs′ = s≤s (aliasFresh a occurs′)

  no-target :
      (Σ[ Y ∈ TyVar _ ]
        toRenameᵗ (impreciseEmbedding
          (preciseBindCore W Aᴾ)) Y ≡ Fin.suc Z) → ⊥
  no-target (Y , eq) =
    aliasNoTargetOccupant a (Y , fin-suc-injective eq)

weaken-alias-atom-imprecise : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z} {T : Ty Δᶜ}
  → (Aᴵ : Ty Δᴵ)
  → AliasSemanticAtom W Z T
  → AliasSemanticAtom (impreciseBindCore W Aᴵ) (Fin.suc Z) (⇑ᵗ T)
weaken-alias-atom-imprecise {W = W} {Z = Z} {T = T} Aᴵ a =
  alias-semantic-atom (aliasPreciseVariable a)
    (cong Fin.suc (aliasPreciseAligned a))
    no-target
    (aliasRep a)
    (trans
      (embedPrecise-imprecise-shift W Aᴵ (aliasRep a))
      (cong ⇑ᵗ (aliasRep-eq a)))
    fresh
    (aliasBound a)
  where
  fresh : ∀ {Y} → Y ∈ᵗ ⇑ᵗ T → Fin.suc Z Fin.< Y
  fresh occurs with shift-∈ᵗ-inversion T occurs
  fresh occurs | Y′ , refl , occurs′ = s≤s (aliasFresh a occurs′)

  no-target :
      (Σ[ Y ∈ TyVar _ ]
        toRenameᵗ (impreciseEmbedding
          (impreciseBindCore W Aᴵ)) Y ≡ Fin.suc Z) → ⊥
  no-target (Fin.zero , ())
  no-target (Fin.suc Y , eq) =
    aliasNoTargetOccupant a (Y , fin-suc-injective eq)

weaken-entry : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴾ : Ty Δᴾ)
  → (Aᴵ : Ty Δᴵ)
  → SemanticEntry W Z mode
  → SemanticEntry (pairedBindCore W Aᴾ Aᴵ) (Fin.suc Z) (I.⇑ᵛ mode)
weaken-entry Aᴾ Aᴵ (paired-entry a) =
  paired-entry (weaken-semantic-atom Aᴾ Aᴵ a)
weaken-entry Aᴾ Aᴵ (dynamic-entry a) =
  dynamic-entry (weaken-dynamic-atom Aᴾ Aᴵ a)
weaken-entry Aᴾ Aᴵ (target-entry a) =
  target-entry (weaken-target-atom Aᴾ Aᴵ a)
weaken-entry Aᴾ Aᴵ (alias-entry a) =
  alias-entry (weaken-alias-atom Aᴾ Aᴵ a)

weaken-entry-precise : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴾ : Ty Δᴾ)
  → SemanticEntry W Z mode
  → SemanticEntry (preciseBindCore W Aᴾ) (Fin.suc Z) (I.⇑ᵛ mode)
weaken-entry-precise Aᴾ (paired-entry a) =
  paired-entry (weaken-semantic-atom-precise Aᴾ a)
weaken-entry-precise Aᴾ (dynamic-entry a) =
  dynamic-entry (weaken-dynamic-atom-precise Aᴾ a)
weaken-entry-precise Aᴾ (target-entry a) =
  target-entry (weaken-target-atom-precise Aᴾ a)
weaken-entry-precise Aᴾ (alias-entry a) =
  alias-entry (weaken-alias-atom-precise Aᴾ a)

weaken-entry-imprecise : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (Aᴵ : Ty Δᴵ)
  → SemanticEntry W Z mode
  → SemanticEntry (impreciseBindCore W Aᴵ) (Fin.suc Z) (I.⇑ᵛ mode)
weaken-entry-imprecise Aᴵ (paired-entry a) =
  paired-entry (weaken-semantic-atom-imprecise Aᴵ a)
weaken-entry-imprecise Aᴵ (dynamic-entry a) =
  dynamic-entry (weaken-dynamic-atom-imprecise Aᴵ a)
weaken-entry-imprecise Aᴵ (target-entry a) =
  target-entry (weaken-target-atom-imprecise Aᴵ a)
weaken-entry-imprecise Aᴵ (alias-entry a) =
  alias-entry (weaken-alias-atom-imprecise Aᴵ a)

-- Embedding shifts through the alias bind mirror the precise bind:
-- the embeddings agree definitionally.

embedPrecise-alias-shift : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : CoreWorld Δᴾ Δᴵ Δᶜ) (rep : Ty Δᴾ) (R : Ty Δᴾ)
  → embedPrecise (aliasBindCore W rep) (⇑ᵗ R)
      ≡ ⇑ᵗ (embedPrecise W R)
embedPrecise-alias-shift W rep R =
  trans (renameᵗ-comp Fin.suc (toRenameᵗ (keep (preciseEmbedding W))) R)
    (sym (renameᵗ-comp (toRenameᵗ (preciseEmbedding W)) Fin.suc R))

embedImprecise-alias-shift : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : CoreWorld Δᴾ Δᴵ Δᶜ) (rep : Ty Δᴾ) (R : Ty Δᴵ)
  → embedImprecise (aliasBindCore W rep) R
      ≡ ⇑ᵗ (embedImprecise W R)
embedImprecise-alias-shift W rep R =
  sym (renameᵗ-comp (toRenameᵗ (impreciseEmbedding W)) Fin.suc R)

weaken-semantic-atom-aliasbind : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (rep : Ty Δᴾ)
  → SemanticAtom W Z
  → SemanticAtom (aliasBindCore W rep) (Fin.suc Z)
weaken-semantic-atom-aliasbind {W = W} rep a =
  semantic-atom (Fin.suc (preciseVariable a)) (impreciseVariable a)
    (cong Fin.suc (preciseAligned a))
    (cong Fin.suc (impreciseAligned a))
    (⇑ᵗ (preciseRep a)) (impreciseRep a)
    (transport-⊑ (embedPrecise-alias-shift W rep (preciseRep a))
      (embedImprecise-alias-shift W rep (impreciseRep a))
      (shift-⊑ (I.X⊑ᵗ (⇑ᵗ (embedPrecise W rep))) (rep-related a)))
    (S-bind∋ (preciseBound a) refl)
    (impreciseBound a)

weaken-dynamic-atom-aliasbind : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (rep : Ty Δᴾ)
  → DynamicSemanticAtom W Z
  → DynamicSemanticAtom (aliasBindCore W rep) (Fin.suc Z)
weaken-dynamic-atom-aliasbind {W = W} {Z = Z} rep a =
  dynamic-semantic-atom (Fin.suc (dynamicPreciseVariable a))
    (cong Fin.suc (dynamicPreciseAligned a))
    no-target
    (⇑ᵗ (dynamicRep a))
    (transport-⊑ (embedPrecise-alias-shift W rep (dynamicRep a)) refl
      (shift-⊑ (I.X⊑ᵗ (⇑ᵗ (embedPrecise W rep)))
        (dynamicRep-related a)))
    fresh
    (S-bind∋ (dynamicBound a) refl)
  where
  fresh : ∀ {Y}
    → Y ∈ᵗ embedPrecise (aliasBindCore W rep) (⇑ᵗ (dynamicRep a))
    → Fin.suc Z Fin.< Y
  fresh {Y = Y} occurs
      with shift-∈ᵗ-inversion (embedPrecise W (dynamicRep a))
        (subst≡ (Y ∈ᵗ_)
          (embedPrecise-alias-shift W rep (dynamicRep a)) occurs)
  fresh occurs | Y′ , refl , occurs′ = s≤s (dynamicFresh a occurs′)

  no-target :
      (Σ[ Y ∈ TyVar _ ]
        toRenameᵗ (impreciseEmbedding
          (aliasBindCore W rep)) Y ≡ Fin.suc Z) → ⊥
  no-target (Y , eq) =
    dynamicNoTargetOccupant a (Y , fin-suc-injective eq)

weaken-target-atom-aliasbind : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (rep : Ty Δᴾ)
  → TargetSemanticAtom W Z
  → TargetSemanticAtom (aliasBindCore W rep) (Fin.suc Z)
weaken-target-atom-aliasbind {W = W} {Z = Z} rep a =
  target-semantic-atom (targetImpreciseVariable a)
    (cong Fin.suc (targetImpreciseAligned a))
    no-precise (targetRep a) (targetBound a)
  where
  no-precise :
      (Σ[ X ∈ TyVar _ ]
        toRenameᵗ (preciseEmbedding
          (aliasBindCore W rep)) X ≡ Fin.suc Z) → ⊥
  no-precise (Fin.zero , ())
  no-precise (Fin.suc X , eq) =
    targetNoPreciseOccupant a (X , fin-suc-injective eq)

weaken-alias-atom-aliasbind : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z} {T : Ty Δᶜ}
  → (rep : Ty Δᴾ)
  → AliasSemanticAtom W Z T
  → AliasSemanticAtom (aliasBindCore W rep) (Fin.suc Z) (⇑ᵗ T)
weaken-alias-atom-aliasbind {W = W} {Z = Z} {T = T} rep a =
  alias-semantic-atom (Fin.suc (aliasPreciseVariable a))
    (cong Fin.suc (aliasPreciseAligned a))
    no-target
    (⇑ᵗ (aliasRep a))
    (trans (embedPrecise-alias-shift W rep (aliasRep a))
      (cong ⇑ᵗ (aliasRep-eq a)))
    fresh
    (S-bind∋ (aliasBound a) refl)
  where
  fresh : ∀ {Y} → Y ∈ᵗ ⇑ᵗ T → Fin.suc Z Fin.< Y
  fresh occurs with shift-∈ᵗ-inversion T occurs
  fresh occurs | Y′ , refl , occurs′ = s≤s (aliasFresh a occurs′)

  no-target :
      (Σ[ Y ∈ TyVar _ ]
        toRenameᵗ (impreciseEmbedding
          (aliasBindCore W rep)) Y ≡ Fin.suc Z) → ⊥
  no-target (Y , eq) =
    aliasNoTargetOccupant a (Y , fin-suc-injective eq)

weaken-entry-aliasbind : ∀ {Δᴾ Δᴵ Δᶜ mode}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} {Z}
  → (rep : Ty Δᴾ)
  → SemanticEntry W Z mode
  → SemanticEntry (aliasBindCore W rep) (Fin.suc Z) (I.⇑ᵛ mode)
weaken-entry-aliasbind rep (paired-entry a) =
  paired-entry (weaken-semantic-atom-aliasbind rep a)
weaken-entry-aliasbind rep (dynamic-entry a) =
  dynamic-entry (weaken-dynamic-atom-aliasbind rep a)
weaken-entry-aliasbind rep (target-entry a) =
  target-entry (weaken-target-atom-aliasbind rep a)
weaken-entry-aliasbind rep (alias-entry a) =
  alias-entry (weaken-alias-atom-aliasbind rep a)

-- The fresh alias slot at the alias bind records the shifted representative,
-- whose embedding equation holds by computation.

fresh-alias-semantic-atom : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : CoreWorld Δᴾ Δᴵ Δᶜ) (rep : Ty Δᴾ)
  → AliasSemanticAtom (aliasBindCore W rep) Fin.zero
      (⇑ᵗ (embedPrecise W rep))
fresh-alias-semantic-atom {Δᶜ = Δᶜ} W rep =
  alias-semantic-atom Fin.zero refl
    (λ { (Y , ()) })
    (⇑ᵗ rep)
    (embedPrecise-alias-shift W rep rep)
    fresh
    (Z∋ refl)
  where
  fresh : ∀ {Y : TyVar (suc Δᶜ)}
    → Y ∈ᵗ ⇑ᵗ (embedPrecise W rep)
    → (Fin.zero {n = Δᶜ}) Fin.< Y
  fresh occurs with shift-∈ᵗ-inversion (embedPrecise W rep) occurs
  fresh occurs | Y′ , refl , occurs′ = s≤s z≤n

-- An entry classified by an alias mode.

data IsAliasEntry {Δᴾ Δᴵ Δᶜ} {W : CoreWorld Δᴾ Δᴵ Δᶜ}
    {Z : TyVar Δᶜ} : ∀ {mode} → SemanticEntry W Z mode → Set where
  is-alias : ∀ {T} (a : AliasSemanticAtom W Z T)
    → IsAliasEntry (alias-entry a)


------------------------------------------------------------------------
-- Fresh slots
------------------------------------------------------------------------

-- A fresh paired slot at the just-bound variables records the bound
-- representation types and their imprecision.

fresh-semantic-atom : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : CoreWorld Δᴾ Δᴵ Δᶜ) (Aᴾ : Ty Δᴾ) (Aᴵ : Ty Δᴵ)
  → Aᴾ ⊑ᵂ⟨ W ⟩ Aᴵ
  → SemanticAtom (pairedBindCore W Aᴾ Aᴵ) Fin.zero
fresh-semantic-atom W Aᴾ Aᴵ r =
  semantic-atom Fin.zero Fin.zero refl refl (⇑ᵗ Aᴾ) (⇑ᵗ Aᴵ)
    (transport-⊑ (embedPrecise-paired-shift W Aᴾ Aᴵ Aᴾ)
      (embedImprecise-paired-shift W Aᴾ Aᴵ Aᴵ)
      (shift-⊑ I.X⊑X r))
    (Z∋ refl) (Z∋ refl)

-- A fresh dynamic slot at a precise-only binding records the bound precise
-- representation and its imprecision below ★.

fresh-dynamic-semantic-atom : ∀ {Δᴾ Δᴵ Δᶜ}
    (W : CoreWorld Δᴾ Δᴵ Δᶜ) (Aᴾ : Ty Δᴾ)
  → impEnv W I.⊢ embedPrecise W Aᴾ ⊑ ★
  → DynamicSemanticAtom (preciseBindCore W Aᴾ) Fin.zero
fresh-dynamic-semantic-atom {Δᶜ = Δᶜ} W Aᴾ r =
  dynamic-semantic-atom Fin.zero refl
    (λ { (Y , ()) })
    (⇑ᵗ Aᴾ)
    (transport-⊑ (embedPrecise-precise-shift W Aᴾ Aᴾ) refl
      (shift-⊑ I.X⊑★ r))
    fresh
    (Z∋ refl)
  where
  fresh : ∀ {Y}
    → Y ∈ᵗ embedPrecise (preciseBindCore W Aᴾ) (⇑ᵗ Aᴾ)
    → Fin.zero {Δᶜ} Fin.< Y
  fresh {Y = Y} occurs
      with shift-∈ᵗ-inversion (embedPrecise W Aᴾ)
        (subst≡ (Y ∈ᵗ_)
          (embedPrecise-precise-shift W Aᴾ Aᴾ) occurs)
  fresh occurs | Y′ , refl , occurs′ = s≤s z≤n

fresh-target-semantic-atom : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : CoreWorld Δᴾ Δᴵ Δᶜ} (Aᴵ : Ty Δᴵ)
  → TargetSemanticAtom (impreciseBindCore W Aᴵ) Fin.zero
fresh-target-semantic-atom Aᴵ =
  target-semantic-atom Fin.zero refl (λ { (X , ()) })
    (⇑ᵗ Aᴵ) (Z∋ refl)
