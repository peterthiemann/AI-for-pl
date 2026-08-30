module proof.LR-narrow.ScopedFreshBodyCompatibilityExperiment where

-- File Charter:
--   * Regression instantiations for fresh body compatibility over the
--     private visible environment fixture.
--   * Exercises the public canonical generator equalities at unequal futures
--     and the canonical reveal/conceal observation wrappers at every index.
--   * The executable fixture below uses the fresh slot and the old natural
--     slot at their actual physical indices; no semantics are changed here.

open import Data.List using ([])
open import Data.Nat using (ℕ; zero)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import TermCtx using (Z)
open import CastTerms
open import Conversion
open import Consistency using (toRenameᵗ)
open import Reduction
open import Primitives using (κℕ)
open import Interpreter
import Eval as Eval
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedIdentity as SI
open import proof.LR-narrow.ScopedBodyInterpretation
  using (BodyFragment; variable-body; arrow-body)
open import proof.LR-narrow.TypeRenamingComposition using (pack↑; pack↓)
open import proof.LR-narrow.VisibleEnvironment
import proof.LR-narrow.ScopedBodyInterpretation as BI
import proof.LR-narrow.ScopedBodyConversion as BC
import proof.LR-narrow.ScopedConversionCompatibility as CC
import proof.LR-narrow.ScopedConversionTransport as SCT
import proof.LR-narrow.ScopedFreshBodyCompatibility as FreshCompat
import proof.LR-narrow.FunctionSealClosureExperiment as C
import proof.LR-narrow.VisibleEnvironmentExperiment as V

module Old = Model C.initial C.initial

oldNatural : Model.ScopedType C.initial C.physical
oldNatural = V.Private.rebase Old.natural

module Fresh = FreshCompat.Fresh V.privateEnvironment oldNatural
module E = Extend V.privateEnvironment oldNatural
module New = BI.Interpretation
  (store-bind C.initial (Model.impreciseTy oldNatural))
  (store-bind C.physical (Model.preciseTy oldNatural))
module OldInterp = BI.Interpretation C.initial C.physical
module NewModel = Model
  (store-bind C.initial (Model.impreciseTy oldNatural))
  (store-bind C.physical (Model.preciseTy oldNatural))
module NewCompat = CC.Compatibility
  (store-bind C.initial (Model.impreciseTy oldNatural))
  (store-bind C.physical (Model.preciseTy oldNatural))

old-natural-var : TyVar 3
old-natural-var = Fin.suc (Fin.suc Fin.zero)

old-natural-varᴾ : TyVar 4
old-natural-varᴾ = Fin.suc (Fin.suc (Fin.suc Fin.zero))

argument-body : BodyFragment {n = 3} (＇ Fin.zero ⇒ ＇ old-natural-var)
argument-body = arrow-body variable-body variable-body

fixture-body : BodyFragment {n = 3}
  ((＇ Fin.zero ⇒ ＇ old-natural-var) ⇒
   (＇ Fin.zero ⇒ ＇ old-natural-var))
fixture-body = arrow-body argument-body argument-body

abstract-argument : NewModel.ScopedType
abstract-argument = New.interpret-body argument-body (meaning E.extended)

old-public-argument : Model.ScopedType C.initial C.physical
old-public-argument = OldInterp.interpret-body argument-body
  (OldInterp.extend-meaning oldNatural (meaning V.privateEnvironment))

public-argument : NewModel.ScopedType
public-argument = E.R.rebase old-public-argument

one-moreᴵ : PhysicalScope
  (store-bind C.initial (Model.impreciseTy oldNatural)) 4
one-moreᴵ = allocate root (‵ `ℕ)

two-moreᴾ : PhysicalScope
  (store-bind C.physical (Model.preciseTy oldNatural)) 6
two-moreᴾ = allocate (allocate root (‵ `ℕ)) (‵ `ℕ)

revealᴵ-generated-one-more : pack↑
    (SCT.scope↑ one-moreᴵ
      (BC.Conversions.revealᴵ
        (store-bind C.initial (Model.impreciseTy oldNatural))
        (store-bind C.physical (Model.preciseTy oldNatural))
        fixture-body Fresh.assignment))
  ≡ pack↑ 〖 Fin.suc Fin.zero , ‵ `ℕ
      ↑ ((＇ Fin.suc Fin.zero ⇒ ＇ Fin.suc old-natural-var) ⇒
         (＇ Fin.suc Fin.zero ⇒ ＇ Fin.suc old-natural-var)) 〗
revealᴵ-generated-one-more = Fresh.revealᴵ-generated fixture-body one-moreᴵ

concealᴵ-generated-one-more : pack↓
    (SCT.scope↓ one-moreᴵ
      (BC.Conversions.concealᴵ
        (store-bind C.initial (Model.impreciseTy oldNatural))
        (store-bind C.physical (Model.preciseTy oldNatural))
        fixture-body Fresh.assignment))
  ≡ pack↓ (makeConceal (Fin.suc Fin.zero) (‵ `ℕ)
      ((＇ Fin.suc Fin.zero ⇒ ＇ Fin.suc old-natural-var) ⇒
       (＇ Fin.suc Fin.zero ⇒ ＇ Fin.suc old-natural-var)))
concealᴵ-generated-one-more = Fresh.concealᴵ-generated fixture-body one-moreᴵ

revealᴾ-generated-two-more : pack↑
    (SCT.scope↑ two-moreᴾ
      (BC.Conversions.revealᴾ
        (store-bind C.initial (Model.impreciseTy oldNatural))
        (store-bind C.physical (Model.preciseTy oldNatural))
        fixture-body Fresh.assignment))
  ≡ pack↑ 〖 Fin.suc (Fin.suc Fin.zero) , ‵ `ℕ
      ↑ ((＇ Fin.suc (Fin.suc Fin.zero)
            ⇒ ＇ Fin.suc (Fin.suc old-natural-varᴾ)) ⇒
         (＇ Fin.suc (Fin.suc Fin.zero)
            ⇒ ＇ Fin.suc (Fin.suc old-natural-varᴾ))) 〗
revealᴾ-generated-two-more = Fresh.revealᴾ-generated fixture-body two-moreᴾ

concealᴾ-generated-two-more : pack↓
    (SCT.scope↓ two-moreᴾ
      (BC.Conversions.concealᴾ
        (store-bind C.initial (Model.impreciseTy oldNatural))
        (store-bind C.physical (Model.preciseTy oldNatural))
        fixture-body Fresh.assignment))
  ≡ pack↓ (makeConceal (Fin.suc (Fin.suc Fin.zero)) (‵ `ℕ)
      ((＇ Fin.suc (Fin.suc Fin.zero)
          ⇒ ＇ Fin.suc (Fin.suc old-natural-varᴾ)) ⇒
       (＇ Fin.suc (Fin.suc Fin.zero)
          ⇒ ＇ Fin.suc (Fin.suc old-natural-varᴾ))))
concealᴾ-generated-two-more = Fresh.concealᴾ-generated fixture-body two-moreᴾ

canonical-reveal-identity-observed : ∀ k
  → NewModel.ObservedComputations
      (E.R.rebase
        (OldInterp.interpret-body fixture-body
          (OldInterp.extend-meaning oldNatural
            (meaning V.privateEnvironment))))
      root root k
      ((ƛ (` zero)) ↑ 〖 Fin.zero ,
        ⇑ᵗ (Model.impreciseTy oldNatural)
        ↑ renameᵗ
            (extᵗ (toRenameᵗ (impreciseNames V.privateEnvironment)))
            ((＇ Fin.zero ⇒ ＇ old-natural-var) ⇒
             (＇ Fin.zero ⇒ ＇ old-natural-var)) 〗)
      ((ƛ (` zero)) ↑ 〖 Fin.zero ,
        ⇑ᵗ (Model.preciseTy oldNatural)
        ↑ renameᵗ
            (extᵗ (toRenameᵗ (preciseNames V.privateEnvironment)))
            ((＇ Fin.zero ⇒ ＇ old-natural-var) ⇒
             (＇ Fin.zero ⇒ ＇ old-natural-var)) 〗)
canonical-reveal-identity-observed k =
  Fresh.canonical-reveal-observed fixture-body
    (NewCompat.values-observed
      (New.interpret-body fixture-body (meaning E.extended))
      (SI.identity-related abstract-argument k))

canonical-conceal-identity-observed : ∀ k
  → NewModel.ObservedComputations
      (New.interpret-body fixture-body (meaning E.extended))
      root root k
      ((ƛ (` zero)) ↓ makeConceal Fin.zero
        (⇑ᵗ (Model.impreciseTy oldNatural))
        (renameᵗ
          (extᵗ (toRenameᵗ (impreciseNames V.privateEnvironment)))
          ((＇ Fin.zero ⇒ ＇ old-natural-var) ⇒
           (＇ Fin.zero ⇒ ＇ old-natural-var))))
      ((ƛ (` zero)) ↓ makeConceal Fin.zero
        (⇑ᵗ (Model.preciseTy oldNatural))
        (renameᵗ
          (extᵗ (toRenameᵗ (preciseNames V.privateEnvironment)))
          ((＇ Fin.zero ⇒ ＇ old-natural-var) ⇒
           (＇ Fin.zero ⇒ ＇ old-natural-var))))
canonical-conceal-identity-observed k =
  Fresh.canonical-conceal-observed fixture-body
    (NewCompat.values-observed
      (E.R.rebase
        (OldInterp.interpret-body fixture-body
          (OldInterp.extend-meaning oldNatural
            (meaning V.privateEnvironment))))
      (E.R.arrow-from old-public-argument old-public-argument
        (SI.identity-related public-argument k)))

freshStoreᴵ : TyStore 3
freshStoreᴵ = store-bind C.initial (Model.impreciseTy oldNatural)

freshStoreᴾ : TyStore 4
freshStoreᴾ = store-bind C.physical (Model.preciseTy oldNatural)

fixtureTyᴵ : Ty 3
fixtureTyᴵ =
  (＇ Fin.zero ⇒ ＇ old-natural-var) ⇒
  (＇ Fin.zero ⇒ ＇ old-natural-var)

fixtureTyᴾ : Ty 4
fixtureTyᴾ =
  (＇ Fin.zero ⇒ ＇ old-natural-varᴾ) ⇒
  (＇ Fin.zero ⇒ ＇ old-natural-varᴾ)

fresh-revealᴵ : Conv↑ 3 fixtureTyᴵ
  (replaceTy Fin.zero (‵ `ℕ) fixtureTyᴵ)
fresh-revealᴵ = 〖 Fin.zero , ‵ `ℕ ↑ fixtureTyᴵ 〗

fresh-revealᴾ : Conv↑ 4 fixtureTyᴾ
  (replaceTy Fin.zero (‵ `ℕ) fixtureTyᴾ)
fresh-revealᴾ = 〖 Fin.zero , ‵ `ℕ ↑ fixtureTyᴾ 〗

argumentTyᴵ : Ty 3
argumentTyᴵ = ＇ Fin.zero ⇒ ＇ old-natural-var

argumentTyᴾ : Ty 4
argumentTyᴾ = ＇ Fin.zero ⇒ ＇ old-natural-varᴾ

fresh-revealᴵ-typed : freshStoreᴵ ⊢↑ fresh-revealᴵ
fresh-revealᴵ-typed = ⊢↑-⇒
  (⊢↓-⇒ (⊢↑-unseal (Z∋ refl)) ⊢↓-id)
  (⊢↑-⇒ (⊢↓-seal (Z∋ refl)) ⊢↑-id)

fresh-revealᴾ-typed : freshStoreᴾ ⊢↑ fresh-revealᴾ
fresh-revealᴾ-typed = ⊢↑-⇒
  (⊢↓-⇒ (⊢↑-unseal (Z∋ refl)) ⊢↓-id)
  (⊢↑-⇒ (⊢↓-seal (Z∋ refl)) ⊢↑-id)

old-natural-entryᴵ : freshStoreᴵ ∋ old-natural-var ⦂ ‵ `ℕ
old-natural-entryᴵ = S-bind∋ (S-bind∋ (Z∋ refl) refl) refl

old-natural-entryᴾ : freshStoreᴾ ∋ old-natural-varᴾ ⦂ ‵ `ℕ
old-natural-entryᴾ =
  S-bind∋ (S-bind∋ (S-bind∋ (Z∋ refl) refl) refl) refl

argument-functionᴵ : Term 3
argument-functionᴵ = ƛ (` zero ↓ seal old-natural-var (‵ `ℕ))

argument-functionᴾ : Term 4
argument-functionᴾ = ƛ (` zero ↓ seal old-natural-varᴾ (‵ `ℕ))

argument-functionᴵ-value : Value argument-functionᴵ
argument-functionᴵ-value = ƛ _

argument-functionᴾ-value : Value argument-functionᴾ
argument-functionᴾ-value = ƛ _

argument-functionᴵ-⊢ : ⟨ 3 , freshStoreᴵ , [] ⟩
  ⊢ argument-functionᴵ ⦂ (‵ `ℕ ⇒ ＇ old-natural-var)
argument-functionᴵ-⊢ =
  ⊢ƛ (⊢conceal (⊢↓-seal old-natural-entryᴵ) (⊢` Z))

argument-functionᴾ-⊢ : ⟨ 4 , freshStoreᴾ , [] ⟩
  ⊢ argument-functionᴾ ⦂ (‵ `ℕ ⇒ ＇ old-natural-varᴾ)
argument-functionᴾ-⊢ =
  ⊢ƛ (⊢conceal (⊢↓-seal old-natural-entryᴾ) (⊢` Z))

revealed-identityᴵ : Term 3
revealed-identityᴵ = (ƛ (` zero)) ↑ fresh-revealᴵ

revealed-identityᴾ : Term 4
revealed-identityᴾ = (ƛ (` zero)) ↑ fresh-revealᴾ

revealed-identityᴵ-⊢ : ⟨ 3 , freshStoreᴵ , [] ⟩
  ⊢ revealed-identityᴵ ⦂ replaceTy Fin.zero (‵ `ℕ) fixtureTyᴵ
revealed-identityᴵ-⊢ = ⊢reveal fresh-revealᴵ-typed (⊢ƛ (⊢` Z))

revealed-identityᴾ-⊢ : ⟨ 4 , freshStoreᴾ , [] ⟩
  ⊢ revealed-identityᴾ ⦂ replaceTy Fin.zero (‵ `ℕ) fixtureTyᴾ
revealed-identityᴾ-⊢ = ⊢reveal fresh-revealᴾ-typed (⊢ƛ (⊢` Z))

runtimeᴵ : ℕ → Term 3
runtimeᴵ n =
  (((revealed-identityᴵ · argument-functionᴵ) · $ (κℕ n))
    ↑ unseal old-natural-var (‵ `ℕ))

runtimeᴾ : ℕ → Term 4
runtimeᴾ n =
  (((revealed-identityᴾ · argument-functionᴾ) · $ (κℕ n))
    ↑ unseal old-natural-varᴾ (‵ `ℕ))

runtimeᴵ-⊢ : ∀ n → ⟨ 3 , freshStoreᴵ , [] ⟩ ⊢ runtimeᴵ n ⦂ ‵ `ℕ
runtimeᴵ-⊢ n = ⊢reveal (⊢↑-unseal old-natural-entryᴵ)
  (⊢· (⊢· revealed-identityᴵ-⊢ argument-functionᴵ-⊢) (⊢$ (κℕ n)))

runtimeᴾ-⊢ : ∀ n → ⟨ 4 , freshStoreᴾ , [] ⟩ ⊢ runtimeᴾ n ⦂ ‵ `ℕ
runtimeᴾ-⊢ n = ⊢reveal (⊢↑-unseal old-natural-entryᴾ)
  (⊢· (⊢· revealed-identityᴾ-⊢ argument-functionᴾ-⊢) (⊢$ (κℕ n)))

runtimeᴵ-↠ : ∀ n → runtimeᴵ n
  —↠[ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ]
  $ (κℕ n)
runtimeᴵ-↠ n =
    runtimeᴵ n
  —→[ keep ]⟨ ξ-reveal
      (ξ-·₁ (pure-step
        (β-reveal-⇒ (ƛ (` zero)) argument-functionᴵ-value)) refl) refl ⟩
    (((((ƛ (` zero)) · (argument-functionᴵ ↓ makeConceal Fin.zero
          (‵ `ℕ) argumentTyᴵ))
        ↑ 〖 Fin.zero , ‵ `ℕ ↑ argumentTyᴵ 〗) · $ (κℕ n))
      ↑ unseal old-natural-var (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (ξ-·₁ (ξ-reveal
        (pure-step (β (argument-functionᴵ-value ↓ fun))) refl) refl) refl ⟩
    ((((argument-functionᴵ ↓ makeConceal Fin.zero (‵ `ℕ) argumentTyᴵ)
        ↑ 〖 Fin.zero , ‵ `ℕ ↑ argumentTyᴵ 〗) · $ (κℕ n))
      ↑ unseal old-natural-var (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (pure-step (β-reveal-⇒ (argument-functionᴵ-value ↓ fun) ($ (κℕ n))))
      refl ⟩
    ((((argument-functionᴵ ↓ makeConceal Fin.zero (‵ `ℕ) argumentTyᴵ)
        · ($ (κℕ n) ↓ seal Fin.zero (‵ `ℕ)))
        ↑ id↑ (＇ old-natural-var))
      ↑ unseal old-natural-var (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (ξ-reveal (pure-step
        (β-conceal-⇒ argument-functionᴵ-value (($ (κℕ n)) ↓ seal)))
        refl) refl ⟩
    ((((argument-functionᴵ ·
        (($ (κℕ n) ↓ seal Fin.zero (‵ `ℕ))
          ↑ unseal Fin.zero (‵ `ℕ)))
        ↓ id↓ (＇ old-natural-var))
        ↑ id↑ (＇ old-natural-var))
      ↑ unseal old-natural-var (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (ξ-reveal (ξ-conceal
        (ξ-·₂ argument-functionᴵ-value
          (pure-step (conceal-reveal ($ (κℕ n)))) refl) refl) refl) refl ⟩
    ((((argument-functionᴵ · $ (κℕ n))
        ↓ id↓ (＇ old-natural-var))
        ↑ id↑ (＇ old-natural-var))
      ↑ unseal old-natural-var (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (ξ-reveal
        (ξ-conceal (pure-step (β ($ (κℕ n)))) refl) refl) refl ⟩
    (((($ (κℕ n) ↓ seal old-natural-var (‵ `ℕ))
        ↓ id↓ (＇ old-natural-var))
        ↑ id↑ (＇ old-natural-var))
      ↑ unseal old-natural-var (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (ξ-reveal (pure-step (id-conceal (($ (κℕ n)) ↓ seal))) refl) refl ⟩
    ((($ (κℕ n) ↓ seal old-natural-var (‵ `ℕ))
        ↑ id↑ (＇ old-natural-var))
      ↑ unseal old-natural-var (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (pure-step (id-reveal (($ (κℕ n)) ↓ seal))) refl ⟩
    (($ (κℕ n) ↓ seal old-natural-var (‵ `ℕ))
      ↑ unseal old-natural-var (‵ `ℕ))
  —→[ keep ]⟨ pure-step (conceal-reveal ($ (κℕ n))) ⟩
    $ (κℕ n) ∎[]

runtimeᴵ-return : ∀ n
  → interpretFrom freshStoreᴵ 9 (runtimeᴵ n)
      ≡ returned (Eval.result 3
        (keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep
          ∷ keep ∷ [])
        ($ (κℕ n)) (runtimeᴵ-↠ n) ($ (κℕ n)))
runtimeᴵ-return n = refl

runtimeᴾ-↠ : ∀ n → runtimeᴾ n
  —↠[ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [] ]
  $ (κℕ n)
runtimeᴾ-↠ n =
    runtimeᴾ n
  —→[ keep ]⟨ ξ-reveal
      (ξ-·₁ (pure-step
        (β-reveal-⇒ (ƛ (` zero)) argument-functionᴾ-value)) refl) refl ⟩
    (((((ƛ (` zero)) · (argument-functionᴾ ↓ makeConceal Fin.zero
          (‵ `ℕ) argumentTyᴾ))
        ↑ 〖 Fin.zero , ‵ `ℕ ↑ argumentTyᴾ 〗) · $ (κℕ n))
      ↑ unseal old-natural-varᴾ (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (ξ-·₁ (ξ-reveal
        (pure-step (β (argument-functionᴾ-value ↓ fun))) refl) refl) refl ⟩
    ((((argument-functionᴾ ↓ makeConceal Fin.zero (‵ `ℕ) argumentTyᴾ)
        ↑ 〖 Fin.zero , ‵ `ℕ ↑ argumentTyᴾ 〗) · $ (κℕ n))
      ↑ unseal old-natural-varᴾ (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (pure-step (β-reveal-⇒ (argument-functionᴾ-value ↓ fun) ($ (κℕ n))))
      refl ⟩
    ((((argument-functionᴾ ↓ makeConceal Fin.zero (‵ `ℕ) argumentTyᴾ)
        · ($ (κℕ n) ↓ seal Fin.zero (‵ `ℕ)))
        ↑ id↑ (＇ old-natural-varᴾ))
      ↑ unseal old-natural-varᴾ (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (ξ-reveal (pure-step
        (β-conceal-⇒ argument-functionᴾ-value (($ (κℕ n)) ↓ seal)))
        refl) refl ⟩
    ((((argument-functionᴾ ·
        (($ (κℕ n) ↓ seal Fin.zero (‵ `ℕ))
          ↑ unseal Fin.zero (‵ `ℕ)))
        ↓ id↓ (＇ old-natural-varᴾ))
        ↑ id↑ (＇ old-natural-varᴾ))
      ↑ unseal old-natural-varᴾ (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (ξ-reveal (ξ-conceal
        (ξ-·₂ argument-functionᴾ-value
          (pure-step (conceal-reveal ($ (κℕ n)))) refl) refl) refl) refl ⟩
    ((((argument-functionᴾ · $ (κℕ n))
        ↓ id↓ (＇ old-natural-varᴾ))
        ↑ id↑ (＇ old-natural-varᴾ))
      ↑ unseal old-natural-varᴾ (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (ξ-reveal
        (ξ-conceal (pure-step (β ($ (κℕ n)))) refl) refl) refl ⟩
    (((($ (κℕ n) ↓ seal old-natural-varᴾ (‵ `ℕ))
        ↓ id↓ (＇ old-natural-varᴾ))
        ↑ id↑ (＇ old-natural-varᴾ))
      ↑ unseal old-natural-varᴾ (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (ξ-reveal (pure-step (id-conceal (($ (κℕ n)) ↓ seal))) refl) refl ⟩
    ((($ (κℕ n) ↓ seal old-natural-varᴾ (‵ `ℕ))
        ↑ id↑ (＇ old-natural-varᴾ))
      ↑ unseal old-natural-varᴾ (‵ `ℕ))
  —→[ keep ]⟨ ξ-reveal
      (pure-step (id-reveal (($ (κℕ n)) ↓ seal))) refl ⟩
    (($ (κℕ n) ↓ seal old-natural-varᴾ (‵ `ℕ))
      ↑ unseal old-natural-varᴾ (‵ `ℕ))
  —→[ keep ]⟨ pure-step (conceal-reveal ($ (κℕ n))) ⟩
    $ (κℕ n) ∎[]

runtimeᴾ-return : ∀ n
  → interpretFrom freshStoreᴾ 9 (runtimeᴾ n)
      ≡ returned (Eval.result 4
        (keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep
          ∷ keep ∷ [])
        ($ (κℕ n)) (runtimeᴾ-↠ n) ($ (κℕ n)))
runtimeᴾ-return n = refl
