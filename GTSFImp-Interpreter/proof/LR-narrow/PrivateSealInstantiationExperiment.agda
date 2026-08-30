module proof.LR-narrow.PrivateSealInstantiationExperiment where

-- File Charter:
--   * Passes universal values through the earlier escaping identity closures.
--   * Instantiates the returned universals, including a second precise-only
--     universal wrapper, and checks exact stores and natural results.
--   * Keeps both private allocations physical and relates the final visible
--     scopes by an embedding. Does not change the live computation relation.

open import Data.List using ([])
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import TermCtx using (Z)
open import Primitives using (κℕ)
open import CastTerms
open import Conversion
open import Reduction
import Consistency as C
open import Consistency using (toRenameᵗ; wk↪ᵗ)
import Eval as E
open import Interpreter
import Imprecision as I
open import LR-narrow.World
open import LR-narrow.LogicalRelation
open import proof.TypeInTermSubst using (StoreRename; StoreRename-wk-bind)
open import proof.Reduction using (_++χ_; appL-↠)
open import proof.LR-narrow.Constant using (constant-values-related)
open import proof.LR-narrow.PrivateSealBehavior
open import proof.LR-narrow.ScopedReturnsExperiment using
  (store-rename-bind; store-rename-hide)
import proof.LR-narrow.EscapingSealExperiment as Escaping

poly-id-type : ∀ {Δ} → Ty Δ
poly-id-type = `∀ (＇ Fin.zero ⇒ ＇ Fin.zero)

initial : World 1 1 1
initial = pairedBindWorld emptyWorld poly-id-type poly-id-type
  (I.∀⊑∀ (I.⇒⊑⇒ I.X⊑X I.X⊑X))

paired : World 2 2 2
paired = pairedBindWorld initial (＇ Fin.zero) (＇ Fin.zero) I.X⊑X

physical : TyStore 3
physical = store-bind (preciseStore (core paired)) (＇ Fin.zero)

continued : World 3 3 3
continued = pairedBindWorld paired (‵ `ℕ) (‵ `ℕ) I.ι⊑ι

physical-final : TyStore 5
physical-final = store-bind (store-bind physical (‵ `ℕ)) (＇ Fin.zero)

-- Reveal the old X on BOTH ends of each certified X→X function. Now it
-- takes and returns a universal value, while retaining the private Z.

pass-bare : Term 2
pass-bare = Escaping.bare-function
  ↑ (seal (Fin.suc Fin.zero) poly-id-type
      ↦↑ unseal (Fin.suc Fin.zero) poly-id-type)

pass-wrapped : Term 3
pass-wrapped = Escaping.wrapped-function
  ↑ (seal (Fin.suc (Fin.suc Fin.zero)) poly-id-type
      ↦↑ unseal (Fin.suc (Fin.suc Fin.zero)) poly-id-type)

pass-bare-certificate :
  PrivateIdentity (preciseStore (core paired)) poly-id-type pass-bare
pass-bare-certificate =
  seal-adapter (S-bind∋ (Z∋ refl) refl) bare-certificate

pass-wrapped-certificate : PrivateIdentity physical poly-id-type pass-wrapped
pass-wrapped-certificate =
  seal-adapter (S-bind∋ (S-bind∋ (Z∋ refl) refl) refl) wrapped-certificate

pass-bare-⊢ : ⟨ 2 , preciseStore (core paired) , [] ⟩
  ⊢ pass-bare ⦂ (poly-id-type ⇒ poly-id-type)
pass-bare-⊢ = private-typed pass-bare-certificate

pass-wrapped-⊢ : ⟨ 3 , physical , [] ⟩
  ⊢ pass-wrapped ⦂ (poly-id-type ⇒ poly-id-type)
pass-wrapped-⊢ = private-typed pass-wrapped-certificate

-- The precise universal argument itself has an absent-slot reveal. Its
-- later instantiation will allocate another surplus private name.

argument-bare : Term 2
argument-bare = Λ (ƛ (` 0))

argument-wrapped : Term 3
argument-wrapped = (Λ (ƛ (` 0)))
  ↑ 〖 Fin.zero , ＇ (Fin.suc Fin.zero) ↑ poly-id-type 〗

argument-bare-⊢ : ⟨ 2 , preciseStore (core paired) , [] ⟩
  ⊢ argument-bare ⦂ poly-id-type
argument-bare-⊢ = ⊢Λ (ƛ (` 0)) (⊢ƛ (⊢` Z))

argument-wrapped-⊢ : ⟨ 3 , physical , [] ⟩
  ⊢ argument-wrapped ⦂ poly-id-type
argument-wrapped-⊢ = ⊢reveal (⊢↑-∀ (⊢↑-⇒ ⊢↓-id ⊢↑-id))
  (⊢Λ (ƛ (` 0)) (⊢ƛ (⊢` Z)))

pass-bare-↠ : pass-bare · argument-bare
  —↠[ private-changes pass-bare-certificate ] argument-bare
pass-bare-↠ = private-application pass-bare-certificate (Λ (ƛ (` 0)))

pass-wrapped-↠ : pass-wrapped · argument-wrapped
  —↠[ private-changes pass-wrapped-certificate ] argument-wrapped
pass-wrapped-↠ =
  private-application pass-wrapped-certificate ((Λ (ƛ (` 0))) ↑ all)

fresh-bare : Term 3
fresh-bare = (ƛ (` 0)) ↑ (seal Fin.zero (‵ `ℕ) ↦↑ unseal Fin.zero (‵ `ℕ))

fresh-wrapped : Term 5
fresh-wrapped = ((ƛ (` 0))
  ↑ (seal Fin.zero (＇ (Fin.suc Fin.zero))
      ↦↑ unseal Fin.zero (＇ (Fin.suc Fin.zero))))
  ↑ (id↓ (＇ (Fin.suc Fin.zero)) ↦↑ id↑ (＇ (Fin.suc Fin.zero)))
  ↑ (seal (Fin.suc Fin.zero) (‵ `ℕ) ↦↑ unseal (Fin.suc Fin.zero) (‵ `ℕ))

fresh-bare-certificate :
  PrivateIdentity (impreciseStore (core continued)) (‵ `ℕ) fresh-bare
fresh-bare-certificate = seal-adapter (Z∋ refl) identity

fresh-wrapped-certificate : PrivateIdentity physical-final (‵ `ℕ) fresh-wrapped
fresh-wrapped-certificate = seal-adapter (S-bind∋ (Z∋ refl) refl)
  (identity-adapter (seal-adapter (Z∋ refl) identity))

fresh-bare-⊢ : ⟨ 3 , impreciseStore (core continued) , [] ⟩
  ⊢ fresh-bare ⦂ (‵ `ℕ ⇒ ‵ `ℕ)
fresh-bare-⊢ = private-typed fresh-bare-certificate

fresh-wrapped-⊢ : ⟨ 5 , physical-final , [] ⟩
  ⊢ fresh-wrapped ⦂ (‵ `ℕ ⇒ ‵ `ℕ)
fresh-wrapped-⊢ = private-typed fresh-wrapped-certificate

argument-bare-↠ : argument-bare ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ‵ `ℕ ]
  —↠[ bind (‵ `ℕ) ∷ [] ] fresh-bare
argument-bare-↠ =
    argument-bare ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ‵ `ℕ ]
  —→[ bind (‵ `ℕ) ]⟨ β-Λ (ƛ (` 0)) ⟩
    fresh-bare ∎[]

argument-wrapped-↠ :
  argument-wrapped ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ‵ `ℕ ]
    —↠[ bind (‵ `ℕ) ∷ bind (＇ Fin.zero) ∷ [] ] fresh-wrapped
argument-wrapped-↠ =
    argument-wrapped ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ‵ `ℕ ]
  —→[ bind (‵ `ℕ) ]⟨ β-reveal-∀ (Λ (ƛ (` 0))) ⟩
    (((Λ (ƛ (` 0))) ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ＇ Fin.zero ])
      ↑ (id↓ (＇ Fin.zero) ↦↑ id↑ (＇ Fin.zero)))
      ↑ (seal Fin.zero (‵ `ℕ) ↦↑ unseal Fin.zero (‵ `ℕ))
  —→[ bind (＇ Fin.zero) ]⟨
      ξ-reveal (ξ-reveal (β-Λ (ƛ (` 0))) refl) refl ⟩
    fresh-wrapped ∎[]

pass-bare-instantiation :
  (pass-bare · argument-bare) ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ‵ `ℕ ]
    —↠[ private-changes pass-bare-certificate ++χ (bind (‵ `ℕ) ∷ []) ]
    fresh-bare
pass-bare-instantiation = private-instantiation pass-bare-certificate
  (Λ (ƛ (` 0))) argument-bare-⊢ argument-bare-↠

pass-wrapped-instantiation :
  (pass-wrapped · argument-wrapped) ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ‵ `ℕ ]
    —↠[ private-changes pass-wrapped-certificate
          ++χ (bind (‵ `ℕ) ∷ bind (＇ Fin.zero) ∷ []) ]
    fresh-wrapped
pass-wrapped-instantiation = private-instantiation pass-wrapped-certificate
  ((Λ (ƛ (` 0))) ↑ all) argument-wrapped-⊢ argument-wrapped-↠

observe-bare : Term 2
observe-bare = ((pass-bare · argument-bare)
  ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ‵ `ℕ ]) · $ (κℕ 7)

observe-wrapped : Term 3
observe-wrapped = ((pass-wrapped · argument-wrapped)
  ⦂∀ (＇ Fin.zero ⇒ ＇ Fin.zero) [ ‵ `ℕ ]) · $ (κℕ 7)

observe-bare-⊢ : ⟨ 2 , impreciseStore (core paired) , [] ⟩
  ⊢ observe-bare ⦂ ‵ `ℕ
observe-bare-⊢ = ⊢· (⊢• (⊢· pass-bare-⊢ argument-bare-⊢)) (⊢$ (κℕ 7))

observe-wrapped-⊢ : ⟨ 3 , physical , [] ⟩ ⊢ observe-wrapped ⦂ ‵ `ℕ
observe-wrapped-⊢ =
  ⊢· (⊢• (⊢· pass-wrapped-⊢ argument-wrapped-⊢)) (⊢$ (κℕ 7))

observe-bare-↠ : observe-bare
  —↠[ (private-changes pass-bare-certificate ++χ (bind (‵ `ℕ) ∷ []))
        ++χ private-changes fresh-bare-certificate ]
    $ (κℕ 7)
observe-bare-↠ =
    observe-bare
  —↠[ private-changes pass-bare-certificate ++χ (bind (‵ `ℕ) ∷ []) ]⟨
      appL-↠ pass-bare-instantiation ⟩+
    fresh-bare · $ (κℕ 7)
  —↠[ private-changes fresh-bare-certificate ]⟨
      private-application fresh-bare-certificate ($ (κℕ 7)) ⟩
    $ (κℕ 7) ∎[]

observe-wrapped-↠ : observe-wrapped
  —↠[ (private-changes pass-wrapped-certificate
        ++χ (bind (‵ `ℕ) ∷ bind (＇ Fin.zero) ∷ []))
        ++χ private-changes fresh-wrapped-certificate ]
    $ (κℕ 7)
observe-wrapped-↠ =
    observe-wrapped
  —↠[ private-changes pass-wrapped-certificate
        ++χ (bind (‵ `ℕ) ∷ bind (＇ Fin.zero) ∷ []) ]⟨
      appL-↠ pass-wrapped-instantiation ⟩+
    fresh-wrapped · $ (κℕ 7)
  —↠[ private-changes fresh-wrapped-certificate ]⟨
      private-application fresh-wrapped-certificate ($ (κℕ 7)) ⟩
    $ (κℕ 7) ∎[]

-- The proof-carrying interpreter checks the whole programs, including
-- both application prefixes and the second universal elimination. The
-- final contexts and stores are fixed in the claims, not just the data.

observe-bare-eval : ∃[ changes ]
  ∃ λ (trace : observe-bare —↠[ changes ] $ (κℕ 7)) →
  (interpretFrom (impreciseStore (core paired)) 9 observe-bare
    ≡ returned (E.result 3 changes ($ (κℕ 7)) trace ($ (κℕ 7))))
  × (changes ▶ˢ impreciseStore (core paired)
      ≡ impreciseStore (core continued))
observe-bare-eval = _ , _ , refl , refl

observe-wrapped-eval : ∃[ changes ]
  ∃ λ (trace : observe-wrapped —↠[ changes ] $ (κℕ 7)) →
  (interpretFrom physical 20 observe-wrapped
    ≡ returned (E.result 5 changes ($ (κℕ 7)) trace ($ (κℕ 7))))
  × (changes ▶ˢ physical ≡ physical-final)
observe-wrapped-eval = _ , _ , refl , refl

-- The new paired allocation sits above the OLD private Z; a second
-- private name then sits above that new pair. Neither private slot is
-- identified with its representation or removed from the runtime store.

final-store-embedding :
  StoreRename (toRenameᵗ (C.skip (C.keep wk↪ᵗ)))
    (preciseStore (core continued)) physical-final
final-store-embedding = store-rename-hide
  (store-rename-bind StoreRename-wk-bind (‵ `ℕ)) (＇ Fin.zero)

final-value-embedding :
  $ (κℕ 7) ≡ renameᵗᵐ (C.skip (C.keep (wk↪ᵗ {Δ = 2}))) ($ (κℕ 7))
final-value-embedding = refl

final-values-related : ∀ k
  → ValueImprecision continued (I.ι⊑ι {ι = `ℕ}) k ($ (κℕ 7)) ($ (κℕ 7))
final-values-related k = constant-values-related k (κℕ 7)
