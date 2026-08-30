module proof.LR-narrow.ScopedConversionCompatibility where

-- File Charter:
--   * Scoped operational tools for structural reveal/conceal compatibility.
--   * Related values survive identity conversions; arrow wrapper calls expand
--     through their actual beta steps, in all three observation directions.
--   * Paired and precise-only variants share the same operational interface;
--     the latter leave the imprecise term and outer index unchanged.
--   * ScopedApplication separately handles argument computations; these
--     lemmas supply the value and administrative-step boundaries.

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import Reduction
open import proof.LR-narrow.Application using (value-return-exact)
open import proof.LR-narrow.RevealSteps
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
open import proof.LR-narrow.ScopedStepExpansion using (observed-right-step)
import proof.LR-narrow.ScopedFunctionSeal as FS

module Compatibility {Δᴵ₀ Δᴾ₀} (Σᴵ₀ : TyStore Δᴵ₀)
    (Σᴾ₀ : TyStore Δᴾ₀) where

  open Model Σᴵ₀ Σᴾ₀
  open FS.Compatibility Σᴵ₀ Σᴾ₀ using (observed-pure-steps)

  values-observed : ∀ {Δᴵ Δᴾ} (A : ScopedType)
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {k U V}
    → related A S T k U V → ObservedComputations A S T k U V
  values-observed A {S} {T} r = observed-from-returns
    {gasᴵ = 0} {gasᴾ = 0}
    (value-return-exact {Σ = scopeStore S} 0 (imprecise-value A r))
    (value-return-exact {Σ = scopeStore T} 0 (precise-value A r)) r

  identity-reveals : ∀ {Δᴵ Δᴾ} (A : ScopedType)
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {k U V}
    → related A S T k U V
    → ObservedComputations A S T k
        (U ↑ id↑ (scopeTy S (impreciseTy A)))
        (V ↑ id↑ (scopeTy T (preciseTy A)))
  identity-reveals A {S} {T} r
      with reveal-id-step-question {Σ = scopeStore S}
        (scopeTy S (impreciseTy A)) (imprecise-value A r)
         | reveal-id-step-question {Σ = scopeStore T}
        (scopeTy T (preciseTy A)) (precise-value A r)
  identity-reveals A {S} {T} r | vU , stepU | vV , stepV =
    observed-pure-steps (λ ())
      (reveal-id-value-none (scopeTy S (impreciseTy A)) vU)
      (id-reveal vU) stepU (λ ())
      (reveal-id-value-none (scopeTy T (preciseTy A)) vV)
      (id-reveal vV) stepV (values-observed A r)

  identity-conceals : ∀ {Δᴵ Δᴾ} (A : ScopedType)
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {k U V}
    → related A S T k U V
    → ObservedComputations A S T k
        (U ↓ id↓ (scopeTy S (impreciseTy A)))
        (V ↓ id↓ (scopeTy T (preciseTy A)))
  identity-conceals A {S} {T} r
      with conceal-id-step-question {Σ = scopeStore S}
        (scopeTy S (impreciseTy A)) (imprecise-value A r)
         | conceal-id-step-question {Σ = scopeStore T}
        (scopeTy T (preciseTy A)) (precise-value A r)
  identity-conceals A {S} {T} r | vU , stepU | vV , stepV =
    observed-pure-steps (λ ())
      (conceal-id-value-none (scopeTy S (impreciseTy A)) vU)
      (id-conceal vU) stepU (λ ())
      (conceal-id-value-none (scopeTy T (preciseTy A)) vV)
      (id-conceal vV) stepV (values-observed A r)

  right-identity-reveals : ∀ {Δᴵ Δᴾ} (A : ScopedType)
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {k U V}
    → related A S T k U V
    → ObservedComputations A S T k U
        (V ↑ id↑ (scopeTy T (preciseTy A)))
  right-identity-reveals A {T = T} r
      with reveal-id-step-question {Σ = scopeStore T}
        (scopeTy T (preciseTy A)) (precise-value A r)
  right-identity-reveals A {T = T} r | vV , stepV =
    observed-right-step (λ ())
      (reveal-id-value-none (scopeTy T (preciseTy A)) vV)
      (pure-step (id-reveal vV)) stepV (values-observed A r)

  right-identity-conceals : ∀ {Δᴵ Δᴾ} (A : ScopedType)
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {k U V}
    → related A S T k U V
    → ObservedComputations A S T k U
        (V ↓ id↓ (scopeTy T (preciseTy A)))
  right-identity-conceals A {T = T} r
      with conceal-id-step-question {Σ = scopeStore T}
        (scopeTy T (preciseTy A)) (precise-value A r)
  right-identity-conceals A {T = T} r | vV , stepV =
    observed-right-step (λ ())
      (conceal-id-value-none (scopeTy T (preciseTy A)) vV)
      (pure-step (id-conceal vV)) stepV (values-observed A r)

  reveal-applications : ∀ {Δᴵ Δᴾ} {B : ScopedType}
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ}
      {k F G U V Aᴵ Aᴵ′ Bᴵ Bᴵ′ Aᴾ Aᴾ′ Bᴾ Bᴾ′}
      (cᴵ : Conv↓ Δᴵ Aᴵ′ Aᴵ) (dᴵ : Conv↑ Δᴵ Bᴵ Bᴵ′)
      (cᴾ : Conv↓ Δᴾ Aᴾ′ Aᴾ) (dᴾ : Conv↑ Δᴾ Bᴾ Bᴾ′)
    → Value F → Value G → Value U → Value V
    → ObservedComputations B S T k
        ((F · (U ↓ cᴵ)) ↑ dᴵ) ((G · (V ↓ cᴾ)) ↑ dᴾ)
    → ObservedComputations B S T k
        ((F ↑ (cᴵ ↦↑ dᴵ)) · U) ((G ↑ (cᴾ ↦↑ dᴾ)) · V)
  reveal-applications {S = S} {T} cᴵ dᴵ cᴾ dᴾ vF vG vU vV c
      with reveal-fun-app-step-question {Σ = scopeStore S} cᴵ dᴵ vF vU
         | reveal-fun-app-step-question {Σ = scopeStore T} cᴾ dᴾ vG vV
  reveal-applications cᴵ dᴵ cᴾ dᴾ vF vG vU vV c
      | vF′ , vU′ , stepᴵ | vG′ , vV′ , stepᴾ =
    observed-pure-steps (λ ()) refl (β-reveal-⇒ vF′ vU′) stepᴵ
      (λ ()) refl (β-reveal-⇒ vG′ vV′) stepᴾ c

  right-reveal-applications : ∀ {Δᴵ Δᴾ} {B : ScopedType}
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ}
      {k F G U V Aᴾ Aᴾ′ Bᴾ Bᴾ′}
      (cᴾ : Conv↓ Δᴾ Aᴾ′ Aᴾ) (dᴾ : Conv↑ Δᴾ Bᴾ Bᴾ′)
    → Value G → Value V
    → ObservedComputations B S T k
        (F · U) ((G · (V ↓ cᴾ)) ↑ dᴾ)
    → ObservedComputations B S T k
        (F · U) ((G ↑ (cᴾ ↦↑ dᴾ)) · V)
  right-reveal-applications {T = T} cᴾ dᴾ vG vV c
      with reveal-fun-app-step-question {Σ = scopeStore T} cᴾ dᴾ vG vV
  right-reveal-applications cᴾ dᴾ vG vV c | vG′ , vV′ , stepᴾ =
    observed-right-step (λ ()) (reveal-fun-app-value-none cᴾ dᴾ)
      (pure-step (β-reveal-⇒ vG′ vV′)) stepᴾ c

  conceal-applications : ∀ {Δᴵ Δᴾ} {B : ScopedType}
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ}
      {k F G U V Aᴵ Aᴵ′ Bᴵ Bᴵ′ Aᴾ Aᴾ′ Bᴾ Bᴾ′}
      (cᴵ : Conv↑ Δᴵ Aᴵ′ Aᴵ) (dᴵ : Conv↓ Δᴵ Bᴵ Bᴵ′)
      (cᴾ : Conv↑ Δᴾ Aᴾ′ Aᴾ) (dᴾ : Conv↓ Δᴾ Bᴾ Bᴾ′)
    → Value F → Value G → Value U → Value V
    → ObservedComputations B S T k
        ((F · (U ↑ cᴵ)) ↓ dᴵ) ((G · (V ↑ cᴾ)) ↓ dᴾ)
    → ObservedComputations B S T k
        ((F ↓ (cᴵ ↦↓ dᴵ)) · U) ((G ↓ (cᴾ ↦↓ dᴾ)) · V)
  conceal-applications {S = S} {T} cᴵ dᴵ cᴾ dᴾ vF vG vU vV c
      with conceal-fun-app-step-question {Σ = scopeStore S} cᴵ dᴵ vF vU
         | conceal-fun-app-step-question {Σ = scopeStore T} cᴾ dᴾ vG vV
  conceal-applications cᴵ dᴵ cᴾ dᴾ vF vG vU vV c
      | vF′ , vU′ , stepᴵ | vG′ , vV′ , stepᴾ =
    observed-pure-steps (λ ()) refl (β-conceal-⇒ vF′ vU′) stepᴵ
      (λ ()) refl (β-conceal-⇒ vG′ vV′) stepᴾ c

  right-conceal-applications : ∀ {Δᴵ Δᴾ} {B : ScopedType}
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ}
      {k F G U V Aᴾ Aᴾ′ Bᴾ Bᴾ′}
      (cᴾ : Conv↑ Δᴾ Aᴾ′ Aᴾ) (dᴾ : Conv↓ Δᴾ Bᴾ Bᴾ′)
    → Value G → Value V
    → ObservedComputations B S T k
        (F · U) ((G · (V ↑ cᴾ)) ↓ dᴾ)
    → ObservedComputations B S T k
        (F · U) ((G ↓ (cᴾ ↦↓ dᴾ)) · V)
  right-conceal-applications {T = T} cᴾ dᴾ vG vV c
      with conceal-fun-app-step-question {Σ = scopeStore T} cᴾ dᴾ vG vV
  right-conceal-applications cᴾ dᴾ vG vV c | vG′ , vV′ , stepᴾ =
    observed-right-step (λ ()) (conceal-fun-app-value-none cᴾ dᴾ)
      (pure-step (β-conceal-⇒ vG′ vV′)) stepᴾ c
