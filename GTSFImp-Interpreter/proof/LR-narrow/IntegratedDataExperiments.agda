module proof.LR-narrow.IntegratedDataExperiments where

-- File Charter:
--   * Value-level regression tests of the integrated dynamic-name model.
--   * Distinguishes same-representation tags, rejects occupied-slot erasure,
--     and admits a fresh dynamic argument to a previously related function.
--   * These assertions inspect the actual dynamic relation, not just final
--     evaluator outcomes. Uses the shared nominal runtime fixtures.

open import Data.Empty using (⊥)
open import Data.Nat using (suc; s≤s)
import Data.Fin as Fin
open import Data.Nat.Properties using (≤-refl)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import Primitives using (κℕ)
import Consistency as C
open import LR-narrow.LogicalRelation using (groundInjection)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.IntegratedModel
import proof.LR-narrow.IntegratedWorld as IW
import proof.LR-narrow.IntegratedData as ID
import proof.LR-narrow.NominalObservationExamples as N

open Model store-empty store-empty
open IW.Worlds store-empty store-empty
open ID.Unary store-empty
open ID.Data store-empty store-empty

S1 : PhysicalScope store-empty 1
S1 = allocate root (‵ `ℕ)

S2 : PhysicalScope store-empty 2
S2 = allocate S1 (‵ `ℕ)

W1 : World S1 S1
W1 = extend-paired empty (‵ `ℕ) (‵ `ℕ)

W2 : World S2 S2
W2 = extend-paired W1 (‵ `ℕ) (‵ `ℕ)

named-packet : ∀ X n → NominalPacket S2 X n (N.package X n)
named-packet X n = ground-packet (λ _ → C.X∼★)
  ($ (κℕ n) ↓ seal X (‵ `ℕ))
  (payload-seal (N.natural-entry X) payload-natural) (C.X∼★ᵍ refl) refl

natural-injection : ∀ {Δ} → C.idᶜ {Δ} C.⊢ ‵ `ℕ ∼ ★
natural-injection = groundInjection (‵ `ℕ) C.ι∼★

natural-packet : ∀ {Δ} (S : PhysicalScope store-empty Δ) n
  → NaturalPacket S n ($ (κℕ n) ⟨ natural-injection ⟩)
natural-packet S n =
  ground-packet C.idᶜ ($ (κℕ n)) payload-natural C.ι∼★ refl

same-new-name : ∀ n k
  → related dataDynamic W2 k (N.package Fin.zero n) (N.package Fin.zero n)
same-new-name n k =
  matched-name-tagged new-paired
    (named-packet Fin.zero n) (named-packet Fin.zero n)

same-old-name : ∀ n k
  → related dataDynamic W2 k
      (N.package (Fin.suc Fin.zero) n) (N.package (Fin.suc Fin.zero) n)
same-old-name n k = matched-name-tagged (old-paired new-paired)
  (named-packet (Fin.suc Fin.zero) n) (named-packet (Fin.suc Fin.zero) n)

private
  cast-domain-injective : ∀ {Δ} {μ ν : C.Env∼ Δ} {A B G H : Ty Δ}
      {M N : Term Δ} {c : μ C.⊢ A ∼ B} {d : ν C.⊢ G ∼ H}
    → M ⟨ c ⟩ ≡ N ⟨ d ⟩ → A ≡ G
  cast-domain-injective refl = refl

  packet-domain : ∀ {Δ} {S : PhysicalScope store-empty Δ} {A B n m M}
    → GroundPacket S A n M → GroundPacket S B m M → A ≡ B
  packet-domain p q = cast-domain-injective (trans (sym (exact p)) (exact q))

  natural-tag-number : ∀ {Δ} {ν : C.Env∼ Δ} {n m}
    → ($ (κℕ n) ⟨ natural-injection {Δ} ⟩)
      ≡ ($ (κℕ m) ⟨ groundInjection (‵ `ℕ) (C.ι∼★ {μ = ν}) ⟩)
    → n ≡ m
  natural-tag-number refl = refl

  packet-natural-number : ∀ {Δ} {S : PhysicalScope store-empty Δ} {n m}
    → NaturalPacket S m ($ (κℕ n) ⟨ natural-injection ⟩) → n ≡ m
  packet-natural-number (ground-packet μ U payload-natural C.ι∼★ eq) =
    natural-tag-number eq

dynamic-nominal-match : ∀ {ΔI ΔP}
    {S : PhysicalScope store-empty ΔI} {T : PhysicalScope store-empty ΔP}
    {W : World S T} {X Y n m k U V}
  → NominalPacket S X n U → NominalPacket T Y m V
  → related dataDynamic W k U V → Matched W X Y
dynamic-nominal-match p q (same-natural-tagged p′ q′)
    with packet-domain p p′
dynamic-nominal-match p q (same-natural-tagged p′ q′) | ()
dynamic-nominal-match p q (matched-name-tagged m p′ q′)
    with packet-domain p p′ | packet-domain q q′
dynamic-nominal-match p q (matched-name-tagged m p′ q′) | refl | refl = m
dynamic-nominal-match p q (precise-only-tagged o p′ q′)
    with packet-domain p p′
dynamic-nominal-match p q (precise-only-tagged o p′ q′) | ()

no-occupied-erasure : ∀ {ΔI ΔP}
    {S : PhysicalScope store-empty ΔI} {T : PhysicalScope store-empty ΔP}
    {W : World S T} {X Y n m k U V}
  → Matched W X Y → NaturalPacket S n U → NominalPacket T Y m V
  → related dataDynamic W k U V → ⊥
no-occupied-erasure m p q (same-natural-tagged p′ q′)
    with packet-domain q q′
no-occupied-erasure m p q (same-natural-tagged p′ q′) | ()
no-occupied-erasure m p q (matched-name-tagged m′ p′ q′)
    with packet-domain p p′
no-occupied-erasure m p q (matched-name-tagged m′ p′ q′) | ()
no-occupied-erasure m p q (precise-only-tagged o p′ q′)
    with packet-domain q q′
no-occupied-erasure m p q (precise-only-tagged o p′ q′) | refl =
  only-not-matched-at o m

same-representation-not-related : ∀ n k
  → related dataDynamic W2 k
      (N.package Fin.zero n) (N.package (Fin.suc Fin.zero) n) → ⊥
same-representation-not-related n k r
    with matched-left-inj
      (dynamic-nominal-match (named-packet Fin.zero n)
        (named-packet (Fin.suc Fin.zero) n) r)
      new-paired
same-representation-not-related n k r | ()

occupied-erasure-rejected : ∀ n k
  → related dataDynamic W2 k
      ($ (κℕ n) ⟨ natural-injection ⟩) (N.package Fin.zero n) → ⊥
occupied-erasure-rejected n k = no-occupied-erasure new-paired
  (natural-packet S2 n) (named-packet Fin.zero n)

-- Even identical runtime packets cannot use an empty capability world.
-- A producer that exports a fresh tag must establish a post-run capability.
missing-capability-rejected : ∀ n k
  → related dataDynamic (empty {S = S2} {T = S2}) k
      (N.package Fin.zero n) (N.package Fin.zero n) → ⊥
missing-capability-rejected n k r with dynamic-nominal-match
    (named-packet Fin.zero n) (named-packet Fin.zero n) r
missing-capability-rejected n k r | ()

-- Payload equality remains observable at zero; the dynamic relation does
-- not acquire an extra unguarded predecessor shift at a tag boundary.
different-data-rejected : ∀ n m k → n ≢ m
  → related dataDynamic (empty {S = root} {T = root}) k
      ($ (κℕ n) ⟨ natural-injection ⟩)
      ($ (κℕ m) ⟨ natural-injection ⟩) → ⊥
different-data-rejected n m k different (same-natural-tagged p q) =
  different (trans (packet-natural-number p) (sym (packet-natural-number q)))
different-data-rejected n m k different (matched-name-tagged match p q)
    with packet-domain (natural-packet root n) p
different-data-rejected n m k different (matched-name-tagged match p q) | ()
different-data-rejected n m k different (precise-only-tagged only p q)
    with packet-domain (natural-packet root m) q
different-data-rejected n m k different (precise-only-tagged only p q) | ()

fresh-erasure-allowed : ∀ n k
  → related dataDynamic
      (extend-only (empty {S = root} {T = root}) (‵ `ℕ)) k
      ($ (κℕ n) ⟨ natural-injection ⟩)
      (($ (κℕ n) ↓ seal Fin.zero (‵ `ℕ))
        ⟨ groundInjection (＇ Fin.zero) (C.X∼★ᶜ {μ = C.idᶜ} refl) ⟩)
fresh-erasure-allowed n k =
  precise-only-tagged new-precise-only (natural-packet root n)
    (ground-packet C.idᶜ ($ (κℕ n) ↓ seal Fin.zero (‵ `ℕ))
      (payload-seal (Z∋ refl) payload-natural) (C.X∼★ᶜ refl) refl)

-- The lambda was related before X was allocated. Its quantified argument
-- test accepts a newly created X packet, not merely a lifted old argument.

future-created-argument : ∀ n j
  → Observed dataDynamic W2 j
      ((ƛ (` 0)) · N.package Fin.zero n)
      ((ƛ (` 0)) · N.package Fin.zero n)
future-created-argument n j =
  ArrowValues.call (identity-related dataDynamic W1 (suc j))
    (grow stay) (grow stay) (extend-paired-future W1) (s≤s ≤-refl)
    (same-new-name n j)
