module proof.LR-narrow.KeepStepExpansion where

-- File Charter:
--   * One-sided expansion by a store-preserving (`keep`) step: a step on
--     only the precise or only the imprecise endpoint preserves the
--     computation relation at the same index, because the index counts
--     imprecise steps and the precise endpoint is unbounded.
--   * Extracted from proof.LR-narrow.Cast so that developments that do
--     not depend on the cast obligations can use them.

open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (n≤1+n; ≤-trans; ∸-monoʳ-≤)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Data.Sum using (inj₁; inj₂)
import Data.Sum
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl)

open import Types
import Imprecision as I
open import TyStore
open import CastTerms
open import Reduction
import Eval as E
open import Interpreter
open import LR-narrow.World
open import LR-narrow.Computation
open import LR-narrow.LogicalRelation
open import LR-narrow.Closure using (value-imprecision-downward-to)
open import proof.LR-narrow.Application using
  (prepend-result; paired-returns-reindex)
open import proof.LR-narrow.BindStepExpansion using
  (step-return-expand; step-return-invert; step-blame-expand;
   step-blame-invert; StepReturn; step-return; StepBlame; step-blame)

paired-future-values-downward : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ}
    {j k : ℕ} {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
    {resultᴵ : E.EvalResult Mᴵ} {resultᴾ : E.EvalResult Mᴾ}
  → j ≤ k
  → PairedReturns W (FutureValueRelation p) k resultᴵ resultᴾ
  → PairedReturns W (FutureValueRelation p) j resultᴵ resultᴾ
paired-future-values-downward j≤k
    (paired-returns W′ W≼W′ imprecise-store precise-store
      imprecise-terms precise-terms related) =
  paired-returns W′ W≼W′ imprecise-store precise-store
    imprecise-terms precise-terms
    (value-imprecision-downward-to j≤k related)

paired-results-downward : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W}
    {j k : ℕ} {Mᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
    {resultᴵ : E.EvalResult Mᴵ} {resultᴾ : E.EvalResult Mᴾ}
  → (∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      {W≼W′ : Future W W′} {i l : ℕ}
      {Vᴵ : Term Δᴵ′} {Vᴾ : Term Δᴾ′}
    → i ≤ l → R W′ W≼W′ l Vᴵ Vᴾ → R W′ W≼W′ i Vᴵ Vᴾ)
  → j ≤ k
  → PairedReturns W R k resultᴵ resultᴾ
  → PairedReturns W R j resultᴵ resultᴾ
paired-results-downward downward j≤k
    (paired-returns W′ W≼W′ imprecise-store precise-store
      imprecise-terms precise-terms related) =
  paired-returns W′ W≼W′ imprecise-store precise-store
    imprecise-terms precise-terms (downward j≤k related)

paired-precise-keep-step : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W} {k : ℕ}
    {Mᴵ : Term Δᴵ} {Mᴾ Nᴾ : Term Δᴾ}
    {stepᴾ : Mᴾ —→[ keep ] Nᴾ}
    {resultᴵ : E.EvalResult Mᴵ} {resultᴾ : E.EvalResult Nᴾ}
  → PairedReturns W R k resultᴵ resultᴾ
  → PairedReturns W R k resultᴵ (prepend-result stepᴾ resultᴾ)
paired-precise-keep-step
    (paired-returns W′ W≼W′ imprecise-store precise-store
      imprecise-terms precise-terms related) =
  paired-returns W′ W≼W′ imprecise-store precise-store
    imprecise-terms precise-terms related

paired-imprecise-keep-step : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W} {k : ℕ}
    {Mᴵ Nᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
    {stepᴵ : Mᴵ —→[ keep ] Nᴵ}
    {resultᴵ : E.EvalResult Nᴵ} {resultᴾ : E.EvalResult Mᴾ}
  → PairedReturns W R k resultᴵ resultᴾ
  → PairedReturns W R k (prepend-result stepᴵ resultᴵ) resultᴾ
paired-imprecise-keep-step
    (paired-returns W′ W≼W′ imprecise-store precise-store
      imprecise-terms precise-terms related) =
  paired-returns W′ W≼W′ imprecise-store precise-store
    imprecise-terms precise-terms related

paired-future-precise-step : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k : ℕ}
    {Mᴵ : Term Δᴵ} {Mᴾ Nᴾ : Term Δᴾ}
    {stepᴾ : Mᴾ —→[ keep ] Nᴾ}
    {resultᴵ : E.EvalResult Mᴵ} {resultᴾ : E.EvalResult Nᴾ}
  → PairedReturns W (FutureValueRelation p) k resultᴵ resultᴾ
  → PairedReturns W (FutureValueRelation p) k resultᴵ
      (prepend-result stepᴾ resultᴾ)
paired-future-precise-step
    paired = paired-precise-keep-step paired

paired-future-imprecise-step : ∀ {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k : ℕ}
    {Mᴵ Nᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
    {stepᴵ : Mᴵ —→[ keep ] Nᴵ}
    {resultᴵ : E.EvalResult Nᴵ} {resultᴾ : E.EvalResult Mᴾ}
  → PairedReturns W (FutureValueRelation p) k resultᴵ resultᴾ
  → PairedReturns W (FutureValueRelation p) k
      (prepend-result stepᴵ resultᴵ) resultᴾ
paired-future-imprecise-step
    paired = paired-imprecise-keep-step paired

related-precise-keep-step-expand-with : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W} {k : ℕ}
    {Mᴵ : Term Δᴵ} {Mᴾ Nᴾ : Term Δᴾ}
  → (∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      {W≼W′ : Future W W′} {i l : ℕ}
      {Vᴵ : Term Δᴵ′} {Vᴾ : Term Δᴾ′}
    → i ≤ l → R W′ W≼W′ l Vᴵ Vᴾ → R W′ W≼W′ i Vᴵ Vᴾ)
  → Mᴾ ≢ blame
  → E.value? Mᴾ ≡ nothing
  → (stepᴾ : Mᴾ —→[ keep ] Nᴾ)
  → E.step? (preciseStore (core W)) Mᴾ ≡
      just (E.step-result keep Nᴾ stepᴾ)
  → ComputationsRelated W R k Mᴵ Nᴾ
  → ComputationsRelated W R k Mᴵ Mᴾ
related-precise-keep-step-expand-with {W = W} {R = R} {k = k}
    {Mᴵ = Mᴵ} {Mᴾ = Mᴾ} {Nᴾ = Nᴾ}
    downward Mᴾ≢blame value-eqᴾ stepᴾ step-eqᴾ related = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = blame-forward
  }
  where
  forward : ∀ {n} {resultᴵ : E.EvalResult Mᴵ}
    → n < k
    → interpretFrom (impreciseStore (core W)) n Mᴵ ≡ returned resultᴵ
    → (Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult Mᴾ ]
          interpretFrom (preciseStore (core W)) m Mᴾ
            ≡ returned resultᴾ
          × PairedReturns W R (k ∸ n) resultᴵ resultᴾ)
       Data.Sum.⊎
       (Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Mᴾ)
  forward {n = n} n≤k returnᴵ with forward-return related n≤k returnᴵ
  forward {n = n} n≤k returnᴵ
      | inj₁ (m , resultᴾ , returnᴾ , paired) =
    inj₁ (suc m , prepend-result stepᴾ resultᴾ ,
      step-return-expand {Σ = preciseStore (core W)}
        Mᴾ≢blame value-eqᴾ stepᴾ step-eqᴾ returnᴾ ,
      paired-precise-keep-step paired)
  forward {n = n} n≤k returnᴵ | inj₂ (m , blamingᴾ) =
    inj₂ (suc m , step-blame-expand {Σ = preciseStore (core W)}
      Mᴾ≢blame value-eqᴾ stepᴾ step-eqᴾ blamingᴾ)

  backward : ∀ {n} {resultᴾ : E.EvalResult Mᴾ}
    → n < k
    → interpretFrom (preciseStore (core W)) n Mᴾ ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult Mᴵ ]
        interpretFrom (impreciseStore (core W)) m Mᴵ
          ≡ returned resultᴵ
        × PairedReturns W R (k ∸ n) resultᴵ resultᴾ
  backward {n = zero} n≤k returnᴾ
      with step-return-invert {Σ = preciseStore (core W)} {n = zero}
        {M = Mᴾ} {N = Nᴾ}
        Mᴾ≢blame value-eqᴾ stepᴾ step-eqᴾ returnᴾ
  backward {n = zero} n≤k returnᴾ | ()
  backward {n = suc n} n≤k returnᴾ
      with step-return-invert {Σ = preciseStore (core W)}
        {n = suc n} {M = Mᴾ} {N = Nᴾ}
        Mᴾ≢blame value-eqᴾ stepᴾ step-eqᴾ returnᴾ
  backward {n = suc n} n≤k returnᴾ
      | step-return resultᴾ′ returnᴾ′ resultᴾ-eq
      with backward-return related
        (≤-trans (n≤1+n (suc n)) n≤k) returnᴾ′
  backward {n = suc n} n≤k returnᴾ
      | step-return resultᴾ′ returnᴾ′ resultᴾ-eq
      | m , resultᴵ , returnᴵ , paired =
    m , resultᴵ , returnᴵ , paired-returns-reindex refl resultᴾ-eq
      (paired-precise-keep-step
        (paired-results-downward downward
          (∸-monoʳ-≤ k (n≤1+n n)) paired))

  blame-forward : ∀ {n}
    → n < k
    → BlamesFrom (impreciseStore (core W)) n Mᴵ
    → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Mᴾ
  blame-forward {n = n} n≤k blamingᴵ
      with forward-blame related n≤k blamingᴵ
  blame-forward {n = n} n≤k blamingᴵ | m , blamingᴾ =
    suc m , step-blame-expand {Σ = preciseStore (core W)}
      Mᴾ≢blame value-eqᴾ stepᴾ step-eqᴾ blamingᴾ

related-precise-keep-step-expand : ∀
    {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k : ℕ}
    {Mᴵ : Term Δᴵ} {Mᴾ Nᴾ : Term Δᴾ}
  → Mᴾ ≢ blame
  → E.value? Mᴾ ≡ nothing
  → (stepᴾ : Mᴾ —→[ keep ] Nᴾ)
  → E.step? (preciseStore (core W)) Mᴾ ≡
      just (E.step-result keep Nᴾ stepᴾ)
  → ComputationsRelated W (FutureValueRelation p) k Mᴵ Nᴾ
  → ComputationsRelated W (FutureValueRelation p) k Mᴵ Mᴾ
related-precise-keep-step-expand {W = W} {p = p} {k = k}
    {Mᴵ = Mᴵ} {Mᴾ = Mᴾ} {Nᴾ = Nᴾ}
    Mᴾ≢blame value-eqᴾ stepᴾ step-eqᴾ related = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = blame-forward
  }
  where
  forward : ∀ {n} {resultᴵ : E.EvalResult Mᴵ}
    → n < k
    → interpretFrom (impreciseStore (core W)) n Mᴵ ≡ returned resultᴵ
    → (Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult Mᴾ ]
          interpretFrom (preciseStore (core W)) m Mᴾ
            ≡ returned resultᴾ
          × PairedReturns W (FutureValueRelation p)
              (k ∸ n) resultᴵ resultᴾ)
       Data.Sum.⊎
       (Σ[ m ∈ ℕ ]
          BlamesFrom (preciseStore (core W)) m Mᴾ)
  forward {n = n} n≤k returnᴵ
      with forward-return related n≤k returnᴵ
  forward {n = n} n≤k returnᴵ
      | inj₁ (m , resultᴾ , returnᴾ , paired) =
    inj₁ (suc m , prepend-result stepᴾ resultᴾ ,
      step-return-expand {Σ = preciseStore (core W)}
        Mᴾ≢blame value-eqᴾ stepᴾ step-eqᴾ returnᴾ ,
      paired-future-precise-step paired)
  forward {n = n} n≤k returnᴵ | inj₂ (m , blamingᴾ) =
    inj₂ (suc m , step-blame-expand
      {Σ = preciseStore (core W)} Mᴾ≢blame value-eqᴾ
      stepᴾ step-eqᴾ blamingᴾ)

  backward : ∀ {n} {resultᴾ : E.EvalResult Mᴾ}
    → n < k
    → interpretFrom (preciseStore (core W)) n Mᴾ ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult Mᴵ ]
        interpretFrom (impreciseStore (core W)) m Mᴵ
          ≡ returned resultᴵ
        × PairedReturns W (FutureValueRelation p)
            (k ∸ n) resultᴵ resultᴾ
  backward {n = zero} n≤k returnᴾ
      with step-return-invert {Σ = preciseStore (core W)} {n = zero}
        {M = Mᴾ} {N = Nᴾ}
        Mᴾ≢blame value-eqᴾ stepᴾ step-eqᴾ returnᴾ
  backward {n = zero} n≤k returnᴾ | ()
  backward {n = suc n} n≤k returnᴾ
      with step-return-invert {Σ = preciseStore (core W)}
        {n = suc n} {M = Mᴾ} {N = Nᴾ}
        Mᴾ≢blame value-eqᴾ stepᴾ step-eqᴾ returnᴾ
  backward {n = suc n} n≤k returnᴾ
      | step-return resultᴾ′ returnᴾ′ resultᴾ-eq
      with backward-return related
        (≤-trans (n≤1+n (suc n)) n≤k) returnᴾ′
  backward {n = suc n} n≤k returnᴾ
      | step-return resultᴾ′ returnᴾ′ resultᴾ-eq
      | m , resultᴵ , returnᴵ , paired =
    m , resultᴵ , returnᴵ ,
    paired-returns-reindex refl resultᴾ-eq
      (paired-future-precise-step
        (paired-future-values-downward
          (∸-monoʳ-≤ k (n≤1+n n)) paired))

  blame-forward : ∀ {n}
    → n < k
    → BlamesFrom (impreciseStore (core W)) n Mᴵ
    → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Mᴾ
  blame-forward {n = n} n≤k blamingᴵ
      with forward-blame related n≤k blamingᴵ
  blame-forward {n = n} n≤k blamingᴵ | m , blamingᴾ =
    suc m , step-blame-expand {Σ = preciseStore (core W)}
      Mᴾ≢blame value-eqᴾ stepᴾ step-eqᴾ blamingᴾ

related-imprecise-keep-step-expand : ∀
    {Δᴾ Δᴵ Δᶜ Aᴾ Aᴵ}
    {W : World Δᴾ Δᴵ Δᶜ}
    {p : impEnv (core W) I.⊢ Aᴾ ⊑ Aᴵ} {k : ℕ}
    {Mᴵ Nᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
  → Mᴵ ≢ blame
  → E.value? Mᴵ ≡ nothing
  → (stepᴵ : Mᴵ —→[ keep ] Nᴵ)
  → E.step? (impreciseStore (core W)) Mᴵ ≡
      just (E.step-result keep Nᴵ stepᴵ)
  → ComputationsRelated W (FutureValueRelation p) k Nᴵ Mᴾ
  → ComputationsRelated W (FutureValueRelation p) k Mᴵ Mᴾ
related-imprecise-keep-step-expand {W = W} {p = p} {k = k}
    {Mᴵ = Mᴵ} {Nᴵ = Nᴵ} {Mᴾ = Mᴾ}
    Mᴵ≢blame value-eqᴵ stepᴵ step-eqᴵ related = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = blame-forward
  }
  where
  forward : ∀ {n} {resultᴵ : E.EvalResult Mᴵ}
    → n < k
    → interpretFrom (impreciseStore (core W)) n Mᴵ ≡ returned resultᴵ
    → (Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult Mᴾ ]
          interpretFrom (preciseStore (core W)) m Mᴾ
            ≡ returned resultᴾ
          × PairedReturns W (FutureValueRelation p)
              (k ∸ n) resultᴵ resultᴾ)
       Data.Sum.⊎
       (Σ[ m ∈ ℕ ]
          BlamesFrom (preciseStore (core W)) m Mᴾ)
  forward {n = zero} n≤k returnᴵ
      with step-return-invert {Σ = impreciseStore (core W)}
        {n = zero} {M = Mᴵ} {N = Nᴵ}
        Mᴵ≢blame value-eqᴵ stepᴵ step-eqᴵ returnᴵ
  forward {n = zero} n≤k returnᴵ | ()
  forward {n = suc n} n≤k returnᴵ
      with step-return-invert {Σ = impreciseStore (core W)}
        {n = suc n} {M = Mᴵ} {N = Nᴵ}
        Mᴵ≢blame value-eqᴵ stepᴵ step-eqᴵ returnᴵ
  forward {n = suc n} n≤k returnᴵ
      | step-return resultᴵ′ returnᴵ′ resultᴵ-eq
      with forward-return related (≤-trans (n≤1+n (suc n)) n≤k) returnᴵ′
  forward {n = suc n} n≤k returnᴵ
      | step-return resultᴵ′ returnᴵ′ resultᴵ-eq
      | inj₁ (m , resultᴾ , returnᴾ , paired) =
    inj₁ (m , resultᴾ , returnᴾ ,
      paired-returns-reindex resultᴵ-eq refl
        (paired-future-imprecise-step
          (paired-future-values-downward
            (∸-monoʳ-≤ k (n≤1+n n)) paired)))
  forward {n = suc n} n≤k returnᴵ
      | step-return resultᴵ′ returnᴵ′ resultᴵ-eq
      | inj₂ (m , blamingᴾ) = inj₂ (m , blamingᴾ)

  backward : ∀ {n} {resultᴾ : E.EvalResult Mᴾ}
    → n < k
    → interpretFrom (preciseStore (core W)) n Mᴾ ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult Mᴵ ]
        interpretFrom (impreciseStore (core W)) m Mᴵ
          ≡ returned resultᴵ
        × PairedReturns W (FutureValueRelation p)
            (k ∸ n) resultᴵ resultᴾ
  backward {n = n} n≤k returnᴾ
      with backward-return related n≤k returnᴾ
  backward {n = n} n≤k returnᴾ
      | m , resultᴵ , returnᴵ , paired =
    suc m , prepend-result stepᴵ resultᴵ ,
    step-return-expand {Σ = impreciseStore (core W)}
      Mᴵ≢blame value-eqᴵ stepᴵ step-eqᴵ returnᴵ ,
    paired-future-imprecise-step paired

  blame-forward : ∀ {n}
    → n < k
    → BlamesFrom (impreciseStore (core W)) n Mᴵ
    → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Mᴾ
  blame-forward {n = zero} n≤k blamingᴵ
      with step-blame-invert {Σ = impreciseStore (core W)}
        {n = zero} {M = Mᴵ} {N = Nᴵ}
        Mᴵ≢blame value-eqᴵ stepᴵ step-eqᴵ blamingᴵ
  blame-forward {n = zero} n≤k blamingᴵ | ()
  blame-forward {n = suc n} n≤k blamingᴵ
      with step-blame-invert {Σ = impreciseStore (core W)}
        {n = suc n} {M = Mᴵ} {N = Nᴵ}
        Mᴵ≢blame value-eqᴵ stepᴵ step-eqᴵ blamingᴵ
  blame-forward {n = suc n} n≤k blamingᴵ
      | step-blame blamingᴵ′ =
    forward-blame related (≤-trans (n≤1+n (suc n)) n≤k) blamingᴵ′

related-imprecise-keep-step-expand-with : ∀ {Δᴾ Δᴵ Δᶜ}
    {W : World Δᴾ Δᴵ Δᶜ} {R : IndexedValueRelation W} {k : ℕ}
    {Mᴵ Nᴵ : Term Δᴵ} {Mᴾ : Term Δᴾ}
  → (∀ {Δᴾ′ Δᴵ′ Δᶜ′}
      {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
      {W≼W′ : Future W W′} {i l : ℕ}
      {Vᴵ : Term Δᴵ′} {Vᴾ : Term Δᴾ′}
    → i ≤ l → R W′ W≼W′ l Vᴵ Vᴾ → R W′ W≼W′ i Vᴵ Vᴾ)
  → Mᴵ ≢ blame
  → E.value? Mᴵ ≡ nothing
  → (stepᴵ : Mᴵ —→[ keep ] Nᴵ)
  → E.step? (impreciseStore (core W)) Mᴵ ≡
      just (E.step-result keep Nᴵ stepᴵ)
  → ComputationsRelated W R k Nᴵ Mᴾ
  → ComputationsRelated W R k Mᴵ Mᴾ
related-imprecise-keep-step-expand-with {W = W} {R = R} {k = k}
    {Mᴵ = Mᴵ} {Nᴵ = Nᴵ} {Mᴾ = Mᴾ}
    downward Mᴵ≢blame value-eqᴵ stepᴵ step-eqᴵ related = record
  { forward-return = forward
  ; backward-return = backward
  ; forward-blame = blame-forward
  }
  where
  forward : ∀ {n} {resultᴵ : E.EvalResult Mᴵ}
    → n < k
    → interpretFrom (impreciseStore (core W)) n Mᴵ ≡ returned resultᴵ
    → (Σ[ m ∈ ℕ ] Σ[ resultᴾ ∈ E.EvalResult Mᴾ ]
          interpretFrom (preciseStore (core W)) m Mᴾ
            ≡ returned resultᴾ
          × PairedReturns W R (k ∸ n) resultᴵ resultᴾ)
       Data.Sum.⊎
       (Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Mᴾ)
  forward {n = zero} n≤k returnᴵ
      with step-return-invert {Σ = impreciseStore (core W)}
        {n = zero} {M = Mᴵ} {N = Nᴵ}
        Mᴵ≢blame value-eqᴵ stepᴵ step-eqᴵ returnᴵ
  forward {n = zero} n≤k returnᴵ | ()
  forward {n = suc n} n≤k returnᴵ
      with step-return-invert {Σ = impreciseStore (core W)}
        {n = suc n} {M = Mᴵ} {N = Nᴵ}
        Mᴵ≢blame value-eqᴵ stepᴵ step-eqᴵ returnᴵ
  forward {n = suc n} n≤k returnᴵ
      | step-return resultᴵ′ returnᴵ′ resultᴵ-eq
      with forward-return related
        (≤-trans (n≤1+n (suc n)) n≤k) returnᴵ′
  forward {n = suc n} n≤k returnᴵ
      | step-return resultᴵ′ returnᴵ′ resultᴵ-eq
      | inj₁ (m , resultᴾ , returnᴾ , paired) =
    inj₁ (m , resultᴾ , returnᴾ ,
      paired-returns-reindex resultᴵ-eq refl
        (paired-imprecise-keep-step
          (paired-results-downward downward
            (∸-monoʳ-≤ k (n≤1+n n)) paired)))
  forward {n = suc n} n≤k returnᴵ
      | step-return resultᴵ′ returnᴵ′ resultᴵ-eq
      | inj₂ (m , blamingᴾ) = inj₂ (m , blamingᴾ)

  backward : ∀ {n} {resultᴾ : E.EvalResult Mᴾ}
    → n < k
    → interpretFrom (preciseStore (core W)) n Mᴾ ≡ returned resultᴾ
    → Σ[ m ∈ ℕ ] Σ[ resultᴵ ∈ E.EvalResult Mᴵ ]
        interpretFrom (impreciseStore (core W)) m Mᴵ
          ≡ returned resultᴵ
        × PairedReturns W R (k ∸ n) resultᴵ resultᴾ
  backward {n = n} n≤k returnᴾ
      with backward-return related n≤k returnᴾ
  backward {n = n} n≤k returnᴾ
      | m , resultᴵ , returnᴵ , paired =
    suc m , prepend-result stepᴵ resultᴵ ,
    step-return-expand {Σ = impreciseStore (core W)}
      Mᴵ≢blame value-eqᴵ stepᴵ step-eqᴵ returnᴵ ,
    paired-imprecise-keep-step paired

  blame-forward : ∀ {n}
    → n < k
    → BlamesFrom (impreciseStore (core W)) n Mᴵ
    → Σ[ m ∈ ℕ ] BlamesFrom (preciseStore (core W)) m Mᴾ
  blame-forward {n = zero} n≤k blamingᴵ
      with step-blame-invert {Σ = impreciseStore (core W)}
        {n = zero} {M = Mᴵ} {N = Nᴵ}
        Mᴵ≢blame value-eqᴵ stepᴵ step-eqᴵ blamingᴵ
  blame-forward {n = zero} n≤k blamingᴵ | ()
  blame-forward {n = suc n} n≤k blamingᴵ
      with step-blame-invert {Σ = impreciseStore (core W)}
        {n = suc n} {M = Mᴵ} {N = Nᴵ}
        Mᴵ≢blame value-eqᴵ stepᴵ step-eqᴵ blamingᴵ
  blame-forward {n = suc n} n≤k blamingᴵ
      | step-blame blamingᴵ′ =
    forward-blame related (≤-trans (n≤1+n (suc n)) n≤k) blamingᴵ′
