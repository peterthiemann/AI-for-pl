module proof.LR-narrow.IntegratedUniversal where

-- File Charter:
--   * Concrete dynamic-payload producers and their universal identity-reveal
--     wrappers inhabit the integrated natural-instantiation value relation.
--   * Instantiation preserves arbitrary old world capabilities and relates
--     fresh returned adapters in the actual, independently allocated scopes.
--   * This does not interpret arbitrary instantiation types or change the LR.

open import Data.List using ([])
open import Data.Nat using (suc; _<_)
open import Data.Product using (_,_; proj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans)
  renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
import Consistency as C
open C using (Env∼; _⊢_∼★)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.IntegratedModel
open import proof.LR-narrow.IntegratedProducer
  using (scope-body-star)
open import proof.LR-narrow.IntegratedProducerSteps using (payload-body)
import proof.LR-narrow.IntegratedWorld as IW
import proof.LR-narrow.IntegratedProducer as Producer
import proof.LR-narrow.IntegratedData as ID
import proof.LR-narrow.IntegratedUniversalSteps as US

scope-payload-body : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
    (S : PhysicalScope Σ₀ Δ)
  → scopeBody S payload-body ≡ payload-body
scope-payload-body S rewrite scope-body-arrow S (＇ Fin.zero) ★
  | scope-body-bound S | scope-body-star S = refl

scope-payload-universal : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
    (S : PhysicalScope Σ₀ Δ)
  → scopeTy S (`∀ payload-body) ≡ `∀ payload-body
scope-payload-universal S = trans (scope-universal S payload-body)
  (cong `∀ (scope-payload-body S))

module Universals {ΔI0 ΔP0} (ΣI0 : TyStore ΔI0)
    (ΣP0 : TyStore ΔP0) where

  open Model ΣI0 ΣP0
  open IW.Worlds ΣI0 ΣP0
  open Producer.ProducerAt ΣI0 ΣP0
    using (payload-family; paired-adapters-related; adapters-related)
  module Data = ID.Data ΣI0 ΣP0

  wrapped-instantiation-future : ∀ {ΔI ΔP}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      (W : World S T)
    → Future (grow (grow stay)) (grow stay) W
        (extend-paired (extend-privateI W (‵ `ℕ)) (＇ Fin.zero) (‵ `ℕ))
  wrapped-instantiation-future W = record
    { matched-future = λ m → old-paired (old-privateI m)
    ; only-future = λ o → old-only-paired (old-only-privateI o)
    }

  producer-instantiation-observed : ∀ {ΔI ΔP}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {W : World S T}
      {μI : Env∼ (suc ΔI)} {μP : Env∼ (suc ΔP)}
      {gateI : μI ⊢ ＇ Fin.zero ∼★} {gateP : μP ⊢ ＇ Fin.zero ∼★} k
    → Observed (arrow natural Data.dataDynamic) W k
        (US.producer-function gateI ⦂∀ payload-body [ ‵ `ℕ ])
        (US.producer-function gateP ⦂∀ payload-body [ ‵ `ℕ ])
  producer-instantiation-observed {S = S} {T} {W}
      {gateI = gateI} {gateP} k =
    observed-from-returns {gasI = 1} {gasP = 1}
      {W′ = extend-paired W (‵ `ℕ) (‵ `ℕ)}
      (proj₂ (US.bare-instantiation-return
        {Σ = scopeStore S} {gate = gateI}))
      (proj₂ (US.bare-instantiation-return
        {Σ = scopeStore T} {gate = gateP}))
      (extend-paired-future W)
      (paired-adapters-related (Z∋ refl) (Z∋ refl) new-paired k)

  wrapper-instantiation-observed : ∀ {ΔI ΔP}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {W : World S T}
      {μI : Env∼ (suc ΔI)} {μP : Env∼ (suc ΔP)}
      {gateI : μI ⊢ ＇ Fin.zero ∼★} {gateP : μP ⊢ ＇ Fin.zero ∼★} k
    → Observed (arrow natural Data.dataDynamic) W k
        (US.wrapped-producer-function gateI ⦂∀ payload-body [ ‵ `ℕ ])
        (US.producer-function gateP ⦂∀ payload-body [ ‵ `ℕ ])
  wrapper-instantiation-observed {S = S} {T} {W}
      {gateI = gateI} {gateP} k =
    observed-from-returns {gasI = 3} {gasP = 1}
      {W′ = extend-paired (extend-privateI W (‵ `ℕ))
        (＇ Fin.zero) (‵ `ℕ)}
      (proj₂ (US.wrapped-instantiation-return
        {Σ = scopeStore S} {gate = gateI}))
      (proj₂ (US.bare-instantiation-return
        {Σ = scopeStore T} {gate = gateP}))
      (wrapped-instantiation-future W)
      (adapters-related (S-bind∋ (Z∋ refl) refl) (Z∋ refl)
        (Z∋ refl) new-paired k)

  producer-related : ∀ {ΔI ΔP}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {W : World S T}
      {μI : Env∼ (suc ΔI)} {μP : Env∼ (suc ΔP)}
      {gateI : μI ⊢ ＇ Fin.zero ∼★} {gateP : μP ⊢ ＇ Fin.zero ∼★} k
    → related (naturalUniversal payload-family) W k
        (US.producer-function gateI) (US.producer-function gateP)
  producer-related {S = S} {T} {W} {gateI = gateI} {gateP} k =
    natural-universal-values US.producer-function-value
      US.producer-function-value
      (subst≡ (λ A → ⟨ _ , scopeStore S , [] ⟩
        ⊢ US.producer-function gateI ⦂ A)
        (sym (scope-payload-universal S)) US.producer-function-⊢)
      (subst≡ (λ A → ⟨ _ , scopeStore T , [] ⟩
        ⊢ US.producer-function gateP ⦂ A)
        (sym (scope-payload-universal T)) US.producer-function-⊢)
      instantiate
    where
    instantiate : ∀ {ΔI′ ΔP′}
        {S′ : PhysicalScope ΣI0 ΔI′} {T′ : PhysicalScope ΣP0 ΔP′}
        {W′ : World S′ T′} {j}
      → (p : ScopeFuture S S′) → (q : ScopeFuture T T′)
      → Future p q W W′ → j < k
      → Observed (arrow natural Data.dataDynamic) W′ j
          (liftTerm p (US.producer-function gateI)
            ⦂∀ scopeBody S′ payload-body [ ‵ `ℕ ])
          (liftTerm q (US.producer-function gateP)
            ⦂∀ scopeBody T′ payload-body [ ‵ `ℕ ])
    instantiate {S′ = S′} {T′} {j = j} p q ext j<k
        with US.lift-producer-function {gate = gateI} p
           | US.lift-producer-function {gate = gateP} q
    instantiate {S′ = S′} {T′} {j = j} p q ext j<k
        | μI′ , gateI′ , eqI | μP′ , gateP′ , eqP
        rewrite eqI | eqP | scope-payload-body S′
          | scope-payload-body T′ =
      producer-instantiation-observed {S = S′} {T = T′}
        {gateI = gateI′} {gateP = gateP′} j

  wrapper-related : ∀ {ΔI ΔP}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {W : World S T}
      {μI : Env∼ (suc ΔI)} {μP : Env∼ (suc ΔP)}
      {gateI : μI ⊢ ＇ Fin.zero ∼★} {gateP : μP ⊢ ＇ Fin.zero ∼★} k
    → related (naturalUniversal payload-family) W k
        (US.wrapped-producer-function gateI) (US.producer-function gateP)
  wrapper-related {S = S} {T} {W} {gateI = gateI} {gateP} k =
    natural-universal-values US.wrapped-producer-function-value
      US.producer-function-value
      (subst≡ (λ A → ⟨ _ , scopeStore S , [] ⟩
        ⊢ US.wrapped-producer-function gateI ⦂ A)
        (sym (scope-payload-universal S)) US.wrapped-producer-function-⊢)
      (subst≡ (λ A → ⟨ _ , scopeStore T , [] ⟩
        ⊢ US.producer-function gateP ⦂ A)
        (sym (scope-payload-universal T)) US.producer-function-⊢)
      instantiate
    where
    instantiate : ∀ {ΔI′ ΔP′}
        {S′ : PhysicalScope ΣI0 ΔI′} {T′ : PhysicalScope ΣP0 ΔP′}
        {W′ : World S′ T′} {j}
      → (p : ScopeFuture S S′) → (q : ScopeFuture T T′)
      → Future p q W W′ → j < k
      → Observed (arrow natural Data.dataDynamic) W′ j
          (liftTerm p (US.wrapped-producer-function gateI)
            ⦂∀ scopeBody S′ payload-body [ ‵ `ℕ ])
          (liftTerm q (US.producer-function gateP)
            ⦂∀ scopeBody T′ payload-body [ ‵ `ℕ ])
    instantiate {S′ = S′} {T′} {j = j} p q ext j<k
        with US.lift-wrapped-producer-function {gate = gateI} p
           | US.lift-producer-function {gate = gateP} q
    instantiate {S′ = S′} {T′} {j = j} p q ext j<k
        | μI′ , gateI′ , eqI | μP′ , gateP′ , eqP
        rewrite eqI | eqP | scope-payload-body S′
          | scope-payload-body T′ =
      wrapper-instantiation-observed {S = S′} {T = T′}
        {gateI = gateI′} {gateP = gateP′} j
