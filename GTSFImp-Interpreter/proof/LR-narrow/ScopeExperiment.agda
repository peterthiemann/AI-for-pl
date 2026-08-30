module proof.LR-narrow.ScopeExperiment where

-- File Charter:
--   * Tests alias-free scope transport at an absent universal reveal.
--   * Pins the exact allocation traces and data results of both endpoints.
--   * Refutes the current return observation even for genuinely related
--     universal inputs, and checks the dead-scope data boundary.
--   * Does not change the live LR or assume any compatibility obligations.

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([])
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans) renaming (subst to subst≡)

open import Types
open import TyStore
open import Primitives using (κℕ)
open import CastTerms
open import Conversion
open import Reduction
import Eval as E
open import Interpreter
import Imprecision as I
open import Consistency using (toRenameᵗ)
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.ClosingSubstitution using (related-empty)
open import LR-narrow.TermRelation using (CompiledUniversalBodyRelation)
open import proof.LR-narrow.Universal using (universals-related-from-body)
open import proof.LR-narrow.Constant using
  (constant-values-related; constant-values-related-future)
open import proof.LR-narrow.RevealAtomic using (related-reveal-identities)
open import proof.ImprecisionConsistency using (ty-all-injective)
open import proof.LR-narrow.ValueExtraction using
  (future-precise-monotone)

initial : World 1 1 1
initial = pairedBindWorld emptyWorld (‵ `ℕ) (‵ `ℕ) I.ι⊑ι

paired : World 2 2 2
paired = pairedBindWorld initial (＇ Fin.zero) (＇ Fin.zero) I.X⊑X

bare : Term 1
bare = (Λ ($ (κℕ 7))) ⦂∀ (‵ `ℕ) [ ＇ Fin.zero ]

bare-⊢ : ⟨ 1 , preciseStore (core initial) , [] ⟩ ⊢ bare ⦂ ‵ `ℕ
bare-⊢ = ⊢• (⊢Λ ($ (κℕ 7)) (⊢$ (κℕ 7)))

bare-↠ : bare —↠[ bind (＇ Fin.zero) ∷ keep ∷ [] ] $ (κℕ 7)
bare-↠ =
    (Λ ($ (κℕ 7))) ⦂∀ (‵ `ℕ) [ ＇ Fin.zero ]
  —→[ bind (＇ Fin.zero) ]⟨ β-Λ ($ (κℕ 7)) ⟩
    $ (κℕ 7) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ pure-step (id-reveal ($ (κℕ 7))) ⟩
    $ (κℕ 7) ∎[]

bare-result : E.EvalResult bare
bare-result = E.result 2 (bind (＇ Fin.zero) ∷ keep ∷ [])
  ($ (κℕ 7)) bare-↠ ($ (κℕ 7))

bare-eval : ∀ gas
  → interpretFrom (impreciseStore (core initial)) (suc (suc gas)) bare
      ≡ returned bare-result
bare-eval zero = refl
bare-eval (suc gas) = refl

wrapped : Term 1
wrapped = ((Λ ($ (κℕ 7)))
  ↑ 〖 Fin.zero , ‵ `ℕ ↑ `∀ (‵ `ℕ) 〗)
  ⦂∀ (‵ `ℕ) [ ＇ Fin.zero ]

wrapped-⊢ :
  ⟨ 1 , preciseStore (core initial) , [] ⟩ ⊢ wrapped ⦂ ‵ `ℕ
wrapped-⊢ = ⊢• (⊢reveal (⊢↑-∀ ⊢↑-id)
  (⊢Λ ($ (κℕ 7)) (⊢$ (κℕ 7))))

wrapped-↠ : wrapped
  —↠[ bind (＇ Fin.zero) ∷ bind (＇ Fin.zero) ∷ keep ∷ keep ∷ keep ∷ [] ]
    $ (κℕ 7)
wrapped-↠ =
    ((Λ ($ (κℕ 7))) ↑ `∀↑ id↑ (‵ `ℕ))
      ⦂∀ (‵ `ℕ) [ ＇ Fin.zero ]
  —→[ bind (＇ Fin.zero) ]⟨ β-reveal-∀ (Λ ($ (κℕ 7))) ⟩
    (((Λ ($ (κℕ 7))) ⦂∀ (‵ `ℕ) [ ＇ Fin.zero ])
      ↑ id↑ (‵ `ℕ)) ↑ id↑ (‵ `ℕ)
  —→[ bind (＇ Fin.zero) ]⟨
      ξ-reveal (ξ-reveal (β-Λ ($ (κℕ 7))) refl) refl ⟩
    (($ (κℕ 7) ↑ id↑ (‵ `ℕ)) ↑ id↑ (‵ `ℕ)) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨
      ξ-reveal (ξ-reveal (pure-step (id-reveal ($ (κℕ 7)))) refl) refl ⟩
    ($ (κℕ 7) ↑ id↑ (‵ `ℕ)) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ ξ-reveal (pure-step (id-reveal ($ (κℕ 7)))) refl ⟩
    $ (κℕ 7) ↑ id↑ (‵ `ℕ)
  —→[ keep ]⟨ pure-step (id-reveal ($ (κℕ 7))) ⟩
    $ (κℕ 7) ∎[]

wrapped-result : E.EvalResult wrapped
wrapped-result = E.result 3
  (bind (＇ Fin.zero) ∷ bind (＇ Fin.zero) ∷ keep ∷ keep ∷ keep ∷ [])
  ($ (κℕ 7)) wrapped-↠ ($ (κℕ 7))

wrapped-eval : ∀ gas
  → interpretFrom (preciseStore (core initial))
      (suc (suc (suc (suc (suc gas))))) wrapped ≡ returned wrapped-result
wrapped-eval zero = refl
wrapped-eval (suc gas) = refl

-- Store chains rooted at the existing paired natural name. Each later
-- name denotes the immediately preceding name. In any old-style future,
-- every source allocation in such a chain must have a target partner.

data NameChain : ∀ {Δ} → TyStore (suc Δ) → Set where
  root : NameChain (store-bind store-empty (‵ `ℕ))
  link : ∀ {Δ} {Σ : TyStore (suc Δ)}
    → NameChain Σ → NameChain (store-bind Σ (＇ Fin.zero))

paired-not-dynamic : I.VarImp.X⊑X ≡ I.VarImp.X⊑★ → ⊥
paired-not-dynamic ()

name-chain-paired : ∀ {Δᴾ Δᴵ Δᶜ} {W : World (suc Δᴾ) Δᴵ Δᶜ}
  → Future initial W
  → NameChain (preciseStore (core W))
  → (∀ X → impEnv (core W)
      (toRenameᵗ (preciseEmbedding (core W)) X) ≡ I.X⊑X)
    × (suc Δᴾ ≤ Δᴵ)
name-chain-paired future-refl root = (λ { Fin.zero → refl }) , ≤-refl
name-chain-paired (future-paired step r) root
  with future-precise-monotone step
... | ()
name-chain-paired (future-precise step r) root
  with future-precise-monotone step
... | ()
name-chain-paired (future-paired step r) (link chain) =
  (λ { Fin.zero → refl ; (Fin.suc X) → proj₁ ih X }) , s≤s (proj₂ ih)
  where
  ih = name-chain-paired step chain
name-chain-paired (future-precise step (I.X⊑★ eq)) (link chain) =
  ⊥-elim (paired-not-dynamic
    (trans (sym (proj₁ (name-chain-paired step chain) Fin.zero)) eq))
name-chain-paired (future-imprecise step) chain =
  proj₁ ih , ≤-trans (proj₂ ih) (n≤1+n _)
  where
  ih = name-chain-paired step chain

no-raw-join : ∀ {Δᶜ} {W : World 3 2 Δᶜ}
  → Future initial W
  → preciseStore (core W)
      ≡ store-bind (preciseStore (core paired)) (＇ Fin.zero)
  → ⊥
no-raw-join step eq with proj₂
  (name-chain-paired step (subst≡ NameChain (sym eq) (link (link root))))
... | s≤s (s≤s ())

bare-return-exact : ∀ gas {result}
  → interpretFrom (impreciseStore (core initial)) gas bare ≡ returned result
  → result ≡ bare-result
bare-return-exact zero ()
bare-return-exact (suc zero) ()
bare-return-exact (suc (suc zero)) refl = refl
bare-return-exact (suc (suc (suc gas))) refl = refl

not-related : ∀ {R : IndexedValueRelation initial}
  → ComputationsRelated initial R 6 bare wrapped
  → ⊥
not-related related
    with backward-return related ≤-refl (wrapped-eval zero)
not-related related | gas , result , result-eq , returns
    with bare-return-exact gas result-eq
not-related related | gas , .bare-result , result-eq , returns
    | refl with returns
not-related related | gas , .bare-result , result-eq , returns
    | refl
    | paired-returns W step storeᴵ storeᴾ termsᴵ termsᴾ values =
  no-raw-join step storeᴾ

-- The source universal is genuinely related to itself at every index:
-- this is not a counterexample built from unrelated input values.

literal-body-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (step : Future W W′)
  → (liftPreciseBody step (‵ `ℕ) ≡ ‵ `ℕ)
    × (liftImpreciseBody step (‵ `ℕ) ≡ ‵ `ℕ)
    × (liftPreciseBodyTerm step ($ (κℕ 7)) ≡ $ (κℕ 7))
    × (liftImpreciseBodyTerm step ($ (κℕ 7)) ≡ $ (κℕ 7))
literal-body-lift future-refl = refl , refl , refl , refl
literal-body-lift (future-paired step r) with literal-body-lift step
... | tyᴾ , tyᴵ , termᴾ , termᴵ rewrite tyᴾ | tyᴵ | termᴾ | termᴵ =
  refl , refl , refl , refl
literal-body-lift (future-precise step r) with literal-body-lift step
... | tyᴾ , tyᴵ , termᴾ , termᴵ rewrite tyᴾ | tyᴵ | termᴾ | termᴵ =
  refl , refl , refl , refl
literal-body-lift (future-imprecise step) with literal-body-lift step
... | tyᴾ , tyᴵ , termᴾ , termᴵ rewrite tyᴾ | tyᴵ | termᴾ | termᴵ =
  refl , refl , refl , refl

literal-body-related : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} k
  → CompiledUniversalBodyRelation {W = W} (I.ι⊑ι {ι = `ℕ})
      (‵ `ℕ) (‵ `ℕ) k [] ($ (κℕ 7)) ($ (κℕ 7))
literal-body-related k W′ step γ Rᴾ Rᴵ r s with literal-body-lift step
literal-body-related k W′ step γ Rᴾ Rᴵ r s
    | tyᴾ , tyᴵ , termᴾ , termᴵ rewrite tyᴾ | tyᴵ | termᴾ | termᴵ with s
literal-body-related k W′ step γ Rᴾ Rᴵ r s
    | tyᴾ , tyᴵ , termᴾ , termᴵ | I.ι⊑ι =
  related-reveal-identities (liftCenterImprecision bind-step I.ι⊑ι)
    (‵ `ℕ) (‵ `ℕ) (constant-values-related-future bind-step k (κℕ 7))
  where
  bind-step = future-paired (future-refl {W = W′}) r

literal-universal-chain : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} k
  → UniversalsRelated W (I.ι⊑ι {ι = `ℕ}) (‵ `ℕ) (‵ `ℕ) k
      (Λ ($ (κℕ 7))) (Λ ($ (κℕ 7)))
literal-universal-chain {W = W} k =
  universals-related-from-body {W = W} {k = k} {Γ = []}
    {p = I.ι⊑ι {ι = `ℕ}} {Bᴾ = ‵ `ℕ} {Bᴵ = ‵ `ℕ}
    ($ (κℕ 7)) ($ (κℕ 7)) (λ i i≤k → literal-body-related i)
    future-refl related-empty k ≤-refl

literal-universal-endpoints : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
  → TypedEndpoints W (I.∀⊑∀ (I.ι⊑ι {ι = `ℕ}))
      (Λ ($ (κℕ 7))) (Λ ($ (κℕ 7)))
literal-universal-endpoints = typed-endpoints (`∀ (‵ `ℕ)) (`∀ (‵ `ℕ))
  refl refl (Λ ($ (κℕ 7))) (Λ ($ (κℕ 7)))
  (⊢Λ ($ (κℕ 7)) (⊢$ (κℕ 7))) (⊢Λ ($ (κℕ 7)) (⊢$ (κℕ 7)))

literal-universal-related : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} k
  → ValueImprecision W (I.∀⊑∀ (I.ι⊑ι {ι = `ℕ})) k
      (Λ ($ (κℕ 7))) (Λ ($ (κℕ 7)))
literal-universal-related zero = literal-universal-endpoints
literal-universal-related (suc k) = literal-universal-endpoints ,
  ‵ `ℕ , ‵ `ℕ , refl , refl , literal-universal-chain (suc k)

rename-natural-inversion : ∀ {Δ Δ′} {ρ : Δ ⇒ʳ Δ′} {A : Ty Δ}
  → renameᵗ ρ A ≡ ‵ `ℕ → A ≡ ‵ `ℕ
rename-natural-inversion {A = ＇ X} ()
rename-natural-inversion {A = ‵ `ℕ} refl = refl
rename-natural-inversion {A = ‵ `𝔹} ()
rename-natural-inversion {A = ★} ()
rename-natural-inversion {A = A ⇒ B} ()
rename-natural-inversion {A = `∀ A} ()

wrapped-universal-not-related :
  ValueImprecision initial (I.∀⊑∀ I.ι⊑ι) 6
    (Λ ($ (κℕ 7)))
    ((Λ ($ (κℕ 7))) ↑ 〖 Fin.zero , ‵ `ℕ ↑ `∀ (‵ `ℕ) 〗)
  → ⊥
wrapped-universal-not-related (endpoints , Bᴾ , Bᴵ , eqᴾ , eqᴵ , chain)
    with rename-natural-inversion (ty-all-injective eqᴾ)
       | rename-natural-inversion (ty-all-injective eqᴵ)
wrapped-universal-not-related
    (endpoints , .(‵ `ℕ) , .(‵ `ℕ) , eqᴾ , eqᴵ , chain) | refl | refl =
  not-related (proj₁ chain initial future-refl
    (＇ Fin.zero) (＇ Fin.zero) I.X⊑X I.ι⊑ι)

inert-universal-reveal-not-closed :
  (ValueImprecision initial (I.∀⊑∀ I.ι⊑ι) 6
      (Λ ($ (κℕ 7))) (Λ ($ (κℕ 7)))
   → ValueImprecision initial (I.∀⊑∀ I.ι⊑ι) 6
      (Λ ($ (κℕ 7)))
      ((Λ ($ (κℕ 7))) ↑ 〖 Fin.zero , ‵ `ℕ ↑ `∀ (‵ `ℕ) 〗))
  → ⊥
inert-universal-reveal-not-closed closure =
  wrapped-universal-not-related (closure (literal-universal-related 6))

-- The extra binder does not escape in this example's result. Lowering
-- that result to the paired scope restores the ordinary value relation.
-- This is a boundary witness, not a general garbage-collection theorem.

scope-closed-returns : ∀ k
  → ∃[ V ]
      (E.term wrapped-result ≡ ⇑ᵗᵐ V)
      × (E.changes wrapped-result ▶ˢ preciseStore (core initial)
          ≡ store-bind (preciseStore (core paired)) (＇ Fin.zero))
      × (E.changes bare-result ▶ˢ impreciseStore (core initial)
          ≡ impreciseStore (core paired))
      × ValueImprecision paired (I.ι⊑ι {ι = `ℕ}) k
          (E.term bare-result) V
scope-closed-returns k = $ (κℕ 7) , refl , refl , refl ,
  constant-values-related k (κℕ 7)
