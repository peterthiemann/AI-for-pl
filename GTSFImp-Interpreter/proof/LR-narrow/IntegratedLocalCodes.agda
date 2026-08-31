module proof.LR-narrow.IntegratedLocalCodes where

-- File Charter:
--   * Small scope-local codes with a FIXED structural interpretation.
--   * Codes contain syntax, store entries, and smaller codes, never arbitrary
--     semantic records. Concrete base endpoints force equal base values.
--   * Covers bases, the existing data-only dynamic meaning, arrows, matched
--     seals, and precise-only seals with same-index payload evidence.
--   * General recursive dynamic/universal interpretation is not claimed.

open import Data.Empty using (⊥)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym) renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
open import Primitives using (κℕ)
open import LR-narrow.LogicalRelation using (SameBaseValue)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.IntegratedLocal
import proof.LR-narrow.IntegratedLocalStructure as Structure
import proof.LR-narrow.IntegratedLocalNominal as Nominal
import proof.LR-narrow.IntegratedData as ID

module Codes {ΔI0 ΔP0} (ΣI0 : TyStore ΔI0) (ΣP0 : TyStore ΔP0) where

  open Local ΣI0 ΣP0
  open Worlds
  module D = ID.Data ΣI0 ΣP0

  data Code {ΔA ΔB} (S₀ : PhysicalScope ΣI0 ΔA)
      (T₀ : PhysicalScope ΣP0 ΔB) : Ty ΔA → Ty ΔB → Set where
    base-code : ∀ ι → Code S₀ T₀ (‵ ι) (‵ ι)
    data-code : Code S₀ T₀ ★ ★
    arrow-code : ∀ {AI AP BI BP}
      → Code S₀ T₀ AI AP → Code S₀ T₀ BI BP
      → Code S₀ T₀ (AI ⇒ BI) (AP ⇒ BP)
    paired-code : ∀ {X Y RI RP}
      → scopeStore S₀ ∋ X ⦂ RI → scopeStore T₀ ∋ Y ⦂ RP
      → Code S₀ T₀ RI RP → Code S₀ T₀ (＇ X) (＇ Y)
    precise-code : ∀ {AI Y RP}
      → scopeStore T₀ ∋ Y ⦂ RP
      → Code S₀ T₀ AI RP → Code S₀ T₀ AI (＇ Y)

  data-meaning : ∀ {ΔA ΔB} {S₀ : PhysicalScope ΣI0 ΔA}
      {T₀ : PhysicalScope ΣP0 ΔB}
    → Meaning S₀ T₀ ★ ★
  data-meaning = record
    { related = λ p q → D.DynamicValues
    ; imprecise-value = D.dynamic-valueI
    ; precise-value = D.dynamic-valueP
    ; imprecise-typed = λ { {p = p} rel →
        subst≡ (λ C → ⟨ _ , _ , [] ⟩ ⊢ _ ⦂ C)
          (sym (lift-ty-star p)) (D.dynamic-typedI rel) }
    ; precise-typed = λ { {q = q} rel →
        subst≡ (λ C → ⟨ _ , _ , [] ⟩ ⊢ _ ⦂ C)
          (sym (lift-ty-star q)) (D.dynamic-typedP rel) }
    ; downward = D.dynamic-downward
    ; future-closed = D.dynamic-future
    }

  denote : ∀ {ΔA ΔB} {S₀ : PhysicalScope ΣI0 ΔA}
      {T₀ : PhysicalScope ΣP0 ΔB} {AI AP}
    → Code S₀ T₀ AI AP → Meaning S₀ T₀ AI AP
  denote (base-code ι) = base ι
  denote data-code = data-meaning
  denote (arrow-code a b) =
    Structure.LocalStructure.arrow ΣI0 ΣP0 (denote a) (denote b)
  denote (paired-code entryI entryP a) =
    Nominal.LocalNominal.paired-seal ΣI0 ΣP0 (denote a) entryI entryP
  denote (precise-code entryP a) =
    Nominal.LocalNominal.precise-seal ΣI0 ΣP0 (denote a) entryP

  -- R18: this remains true even if the caller existentially chooses a code.
  -- It would be false if a constructor could import an arbitrary Meaning.
  natural-code-values : ∀ {ΔA ΔB} {S₀ : PhysicalScope ΣI0 ΔA}
      {T₀ : PhysicalScope ΣP0 ΔB} (a : Code S₀ T₀ (‵ `ℕ) (‵ `ℕ))
      {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {p : ScopeFuture S₀ S} {q : ScopeFuture T₀ T}
      {W : World S T} {k U V}
    → related (denote a) p q W k U V → SameBaseValue `ℕ U V
  natural-code-values (base-code `ℕ) rel = rel

  different-naturals-rejected : ∀ {ΔA ΔB}
      {S₀ : PhysicalScope ΣI0 ΔA} {T₀ : PhysicalScope ΣP0 ΔB}
      (a : Code S₀ T₀ (‵ `ℕ) (‵ `ℕ))
      {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {p : ScopeFuture S₀ S} {q : ScopeFuture T₀ T}
      {W : World S T} {k}
    → related (denote a) p q W k ($ (κℕ 0)) ($ (κℕ 1)) → ⊥
  different-naturals-rejected (base-code `ℕ) ()
