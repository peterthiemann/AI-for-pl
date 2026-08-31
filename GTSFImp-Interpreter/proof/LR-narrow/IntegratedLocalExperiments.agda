module proof.LR-narrow.IntegratedLocalExperiments where

-- File Charter:
--   * Regression tests for the approved scope-anchored local interface.
--   * Exercises small Code, paired/precise nominal meanings, reanchoring, and
--     same-index payload evidence.
--   * This file does not claim arbitrary type instantiation, general dynamic
--     payloads, or a full fundamental property.

open import Data.Empty using (⊥)
open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; ∃-syntax)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import TermCtx using (Z)
open import CastTerms
open import Conversion using (seal; unseal; ⊢↓-seal; ⊢↑-unseal)
open import Reduction
open import Primitives using (κℕ)
open import Interpreter
import Eval as E
open import LR-narrow.LogicalRelation using (same-natural)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.IntegratedLocal
import proof.LR-narrow.IntegratedLocalCodes as LC
import proof.LR-narrow.IntegratedLocalNominal as Nominal
import proof.LR-narrow.IntegratedLocalStructure as Structure
import proof.LR-narrow.IntegratedWorld as IW

module L = Local store-empty store-empty
module Codes = LC.Codes store-empty store-empty
module Nom = Nominal.LocalNominal store-empty store-empty
module Struct = Structure.LocalStructure store-empty store-empty
module Wds = IW.Worlds store-empty store-empty

open L
open Codes
open Wds

three : ℕ
three = suc (suc (suc zero))

seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

-- R18 remains blocked for every small code with Nat/Nat endpoints.  There is
-- no constructor that imports the arbitrary coarse SemanticType witness.

r18-code-naturals-reject-different : ∀
    {S₀ : PhysicalScope store-empty zero}
    {T₀ : PhysicalScope store-empty zero}
    (a : Code S₀ T₀ (‵ `ℕ) (‵ `ℕ)) k
  → related (denote a) stay stay (empty {S = S₀} {T = T₀}) k
      ($ (κℕ 0)) ($ (κℕ 1)) → ⊥
r18-code-naturals-reject-different a k =
  different-naturals-rejected a

r18-no-existential-code-relates-different-naturals : ∀
    {S₀ : PhysicalScope store-empty zero}
    {T₀ : PhysicalScope store-empty zero}
    k
  → (∃[ a ] related (denote {AI = ‵ `ℕ} {AP = ‵ `ℕ} a) stay stay
      (empty {S = S₀} {T = T₀}) k ($ (κℕ 0)) ($ (κℕ 1)))
  → ⊥
r18-no-existential-code-relates-different-naturals k (a , rel) =
  different-naturals-rejected a rel

-- R19 positive side: fresh nominal codes are formed at the allocated scopes,
-- so future-local endpoints like X⇒★ and X⇒X are not forced through a closed
-- root type.

fresh-source : PhysicalScope store-empty 1
fresh-source = allocate root (‵ `ℕ)

fresh-target : PhysicalScope store-empty 1
fresh-target = allocate root (‵ `ℕ)

fresh-world : World fresh-source fresh-target
fresh-world = extend-paired empty (‵ `ℕ) (‵ `ℕ)

fresh-X⇒★-code :
  Code fresh-source fresh-target
    (＇ Fin.zero ⇒ ★) (＇ Fin.zero ⇒ ★)
fresh-X⇒★-code =
  arrow-code (paired-code (Z∋ refl) (Z∋ refl) (base-code `ℕ))
    data-code

fresh-X⇒X-code :
  Code fresh-source fresh-target
    (＇ Fin.zero ⇒ ＇ Fin.zero) (＇ Fin.zero ⇒ ＇ Fin.zero)
fresh-X⇒X-code =
  arrow-code (paired-code (Z∋ refl) (Z∋ refl) (base-code `ℕ))
    (paired-code (Z∋ refl) (Z∋ refl) (base-code `ℕ))

fresh-identity-X⇒X-related : ∀ k
  → related (denote fresh-X⇒X-code) stay stay fresh-world k
      (ƛ (` 0)) (ƛ (` 0))
fresh-identity-X⇒X-related k =
  Struct.identity-related
    (denote (paired-code (Z∋ refl) (Z∋ refl) (base-code `ℕ)))
    stay stay fresh-world k

-- Precise-only nominal code: the target has a fresh nominal function slot
-- represented by Nat⇒Nat; the source remains the representation function.

precise-target : PhysicalScope store-empty 1
precise-target = allocate root (‵ `ℕ ⇒ ‵ `ℕ)

precise-world : World root precise-target
precise-world = extend-only empty (‵ `ℕ ⇒ ‵ `ℕ)

precise-function-code :
  Code root precise-target (‵ `ℕ ⇒ ‵ `ℕ) (＇ Fin.zero)
precise-function-code =
  precise-code (Z∋ refl)
    (arrow-code (base-code `ℕ) (base-code `ℕ))

precise-function-related : ∀ k
  → related (denote precise-function-code) stay stay precise-world k
      (ƛ (` 0))
      ((ƛ (` 0)) ↓ seal Fin.zero (‵ `ℕ ⇒ ‵ `ℕ))
precise-function-related k =
  Nom.precise-seal-values (ƛ (` 0)) (ƛ (` 0))
    (Struct.identity-related (denote (base-code `ℕ)) stay stay precise-world k)
    refl refl new-precise-only

precise-function-typed-source :
  ⟨ zero , store-empty , [] ⟩ ⊢ ƛ (` 0) ⦂ ‵ `ℕ ⇒ ‵ `ℕ
precise-function-typed-source = ⊢ƛ (⊢` Z)

precise-function-typed-target :
  ⟨ suc zero , scopeStore precise-target , [] ⟩
    ⊢ (ƛ (` 0)) ↓ seal Fin.zero (‵ `ℕ ⇒ ‵ `ℕ) ⦂ ＇ Fin.zero
precise-function-typed-target =
  ⊢conceal (⊢↓-seal (Z∋ refl)) (⊢ƛ (⊢` Z))

precise-source-app : Term zero
precise-source-app = (ƛ (` 0)) · $ (κℕ seven)

precise-target-app : Term (suc zero)
precise-target-app =
  (((ƛ (` 0)) ↓ seal Fin.zero (‵ `ℕ ⇒ ‵ `ℕ))
    ↑ unseal Fin.zero (‵ `ℕ ⇒ ‵ `ℕ)) · $ (κℕ seven)

precise-source-app-⊢ :
  ⟨ zero , store-empty , [] ⟩ ⊢ precise-source-app ⦂ ‵ `ℕ
precise-source-app-⊢ =
  ⊢· precise-function-typed-source (⊢$ (κℕ seven))

precise-target-app-⊢ :
  ⟨ suc zero , scopeStore precise-target , [] ⟩
    ⊢ precise-target-app ⦂ ‵ `ℕ
precise-target-app-⊢ =
  ⊢·
    (⊢reveal (⊢↑-unseal (Z∋ refl)) precise-function-typed-target)
    (⊢$ (κℕ seven))

precise-source-app-return :
  ∃[ tr ] interpretFrom store-empty (suc zero) precise-source-app
    ≡ returned
        (E.result zero (keep ∷ []) ($ (κℕ seven)) tr ($ (κℕ seven)))
precise-source-app-return = _ , refl

precise-target-app-return :
  ∃[ tr ] interpretFrom (scopeStore precise-target) (suc (suc zero))
      precise-target-app
    ≡ returned (E.result (suc zero) (keep ∷ keep ∷ [])
      ($ (κℕ seven)) tr ($ (κℕ seven)))
precise-target-app-return = _ , refl

-- Occupied target names cannot be used by the precise-only constructor.

occupied-world : World fresh-source precise-target
occupied-world = extend-paired empty (‵ `ℕ) (‵ `ℕ ⇒ ‵ `ℕ)

precise-occupied-code :
  Code fresh-source precise-target (‵ `ℕ ⇒ ‵ `ℕ) (＇ Fin.zero)
precise-occupied-code =
  precise-code (Z∋ refl)
    (arrow-code (base-code `ℕ) (base-code `ℕ))

precise-code-rejects-occupied-target : ∀ k
  → related (denote precise-occupied-code) stay stay occupied-world k
      (ƛ (` 0))
      ((ƛ (` 0)) ↓ seal Fin.zero (‵ `ℕ ⇒ ‵ `ℕ))
  → ⊥
precise-code-rejects-occupied-target k rel =
  only-not-matched-at (Nom.PreciseSealValues.precise-only-slot rel)
    new-paired

precise-future-source : PhysicalScope store-empty 1
precise-future-source = allocate root (‵ `𝔹)

precise-future-target : PhysicalScope store-empty 3
precise-future-target =
  allocate (allocate precise-target (‵ `𝔹)) (‵ `ℕ)

precise-future-world : World precise-future-source precise-future-target
precise-future-world =
  extend-privateP
    (extend-privateP (extend-privateI precise-world (‵ `𝔹)) (‵ `𝔹))
    (‵ `ℕ)

precise-unequal-future :
  Future (grow stay) (grow (grow stay)) precise-world precise-future-world
precise-unequal-future =
  future-trans (extend-privateI-future precise-world)
    (future-trans
      (extend-privateP-future (extend-privateI precise-world (‵ `𝔹)))
      (extend-privateP-future
        (extend-privateP (extend-privateI precise-world (‵ `𝔹)) (‵ `𝔹))))

precise-function-survives-unequal-future : ∀ k
  → related (denote precise-function-code) (grow stay) (grow (grow stay))
      precise-future-world k
      (liftTerm {S = root} {T = precise-future-source}
        (grow stay) (ƛ (` 0)))
      (liftTerm {S = precise-target} {T = precise-future-target}
        (grow (grow stay))
        ((ƛ (` 0)) ↓ seal Fin.zero (‵ `ℕ ⇒ ‵ `ℕ)))
precise-function-survives-unequal-future k =
  future-closed (denote precise-function-code)
    (grow stay) (grow (grow stay)) precise-unequal-future
    (precise-function-related k)

-- Old paired capabilities survive unequal future paths and can then be
-- reanchored at the future scopes without changing the related sealed values.

old-paired-code :
  Code fresh-source fresh-target (＇ Fin.zero) (＇ Fin.zero)
old-paired-code = paired-code (Z∋ refl) (Z∋ refl) (base-code `ℕ)

old-sealed-related : ∀ k
  → related (denote old-paired-code) stay stay fresh-world k
      ($ (κℕ three) ↓ seal Fin.zero (‵ `ℕ))
      ($ (κℕ three) ↓ seal Fin.zero (‵ `ℕ))
old-sealed-related k =
  Nom.paired-seal-values ($ (κℕ three)) ($ (κℕ three))
    (same-natural three) refl refl new-paired

future-source : PhysicalScope store-empty 2
future-source = allocate fresh-source (‵ `𝔹)

future-target : PhysicalScope store-empty 3
future-target =
  allocate (allocate fresh-target (‵ `𝔹)) (‵ `ℕ)

future-world : World future-source future-target
future-world =
  extend-privateP
    (extend-privateP (extend-privateI fresh-world (‵ `𝔹)) (‵ `𝔹))
    (‵ `ℕ)

unequal-future :
  Future (grow stay) (grow (grow stay)) fresh-world future-world
unequal-future =
  future-trans (extend-privateI-future fresh-world)
    (future-trans
      (extend-privateP-future (extend-privateI fresh-world (‵ `𝔹)))
      (extend-privateP-future
        (extend-privateP (extend-privateI fresh-world (‵ `𝔹)) (‵ `𝔹))))

old-sealed-survives-unequal-future : ∀ k
  → related (denote old-paired-code) (grow stay) (grow (grow stay))
      future-world k
      (liftTerm {S = fresh-source} {T = future-source}
        (grow stay) ($ (κℕ three) ↓ seal Fin.zero (‵ `ℕ)))
      (liftTerm {S = fresh-target} {T = future-target}
        (grow (grow stay))
        ($ (κℕ three) ↓ seal Fin.zero (‵ `ℕ)))
old-sealed-survives-unequal-future k =
  future-closed (denote old-paired-code)
    (grow stay) (grow (grow stay)) unequal-future
    (old-sealed-related k)

old-sealed-reanchored-after-unequal-future : ∀ k
  → related
      (Struct.reanchor (grow stay) (grow (grow stay))
        (denote old-paired-code))
      stay stay future-world k
      (liftTerm {S = fresh-source} {T = future-source}
        (grow stay) ($ (κℕ three) ↓ seal Fin.zero (‵ `ℕ)))
      (liftTerm {S = fresh-target} {T = future-target}
        (grow (grow stay))
        ($ (κℕ three) ↓ seal Fin.zero (‵ `ℕ)))
old-sealed-reanchored-after-unequal-future k =
  Struct.reanchor-related
    {S₀ = fresh-source} {T₀ = fresh-target}
    {S = future-source} {T = future-target}
    {AI = ＇ Fin.zero} {AP = ＇ Fin.zero}
    {A = denote old-paired-code}
    {W = future-world} {k = k}
    {U = liftTerm {S = fresh-source} {T = future-source}
      (grow stay) ($ (κℕ three) ↓ seal Fin.zero (‵ `ℕ))}
    {V = liftTerm {S = fresh-target} {T = future-target}
      (grow (grow stay))
      ($ (κℕ three) ↓ seal Fin.zero (‵ `ℕ))}
    (grow stay) (grow (grow stay))
    (old-sealed-survives-unequal-future k)
