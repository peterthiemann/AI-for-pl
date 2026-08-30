module proof.LR-narrow.ScopedFunctionSeal where

-- File Charter:
--   * General function-seal compatibility for the fixed-root scoped model.
--   * Decodes nominal computation results in all three DGG directions and
--     derives public arrow relatedness from abstract arrow relatedness.
--   * Preserves independent physical histories and escaped private names.
--   * Uses evaluator phases, typed unseal inversion, and proved LR closure.

open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc; _≤_; _<_; _∸_; s≤s)
open import Data.Nat.Properties using
  (≤-trans; n≤1+n; m≤m+n; ∸-monoʳ-≤)
open import Data.Product using (_×_; _,_; ∃; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂; trans)
  renaming (subst to subst≡; subst₂ to subst₂≡)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import Reduction
import Eval as E
open import Interpreter
open import LR-narrow.Computation using (BlamesFrom)
open import proof.TypeInTermSubst using (toRename-wk-eq; renameᵗ-wk-eq)
open import proof.LR-narrow.Application using (_++ˢ_; prepend-result)
open import proof.LR-narrow.FramePhases using (Frame)
open import proof.LR-narrow.RevealFrames using (revealFrame; reveal-frm)
open import proof.LR-narrow.RevealSteps using (reveal-fun-app-step-question)
open import proof.LR-narrow.StepExpansion using
  (pure-step-return-invert; pure-step-return; pure-step-return-expand;
   pure-step-blame-invert; pure-step-blame; pure-step-blame-expand)
open import proof.LR-narrow.FunctionSealObservation using
  (unseal-return-invert; unseal-return-expand; unseal-blame-invert)
open import proof.LR-narrow.FunctionSealCompatibility using
  (related-seals; reveal-function; reveal-function-typed)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior

-- Normalize runtime names/types and administrative histories at one boundary.

private
  scoped-unseal-return-invert : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
      (S : PhysicalScope Σ₀ Δ) {gas M Y B}
      {out : E.EvalResult (M ↑ unseal (scopeVar S Y) (scopeTy S B))}
    → Σ₀ ∋ Y ⦂ B → ⟨ Δ , scopeStore S , [] ⟩ ⊢ M ⦂ ＇ scopeVar S Y
    → interpretFrom (scopeStore S) gas
        (M ↑ unseal (scopeVar S Y) (scopeTy S B)) ≡ returned out
    → ∃[ bodyGas ] ∃[ χs ]
        ∃ λ (bodyTrace : M —↠[ χs ] E.term out
          ↓ seal (scopeVar (advance S χs) Y) (scopeTy (advance S χs) B)) →
        (interpretFrom (scopeStore S) bodyGas M ≡ returned
          (E.result (E.Δ′ out) χs (E.term out
            ↓ seal (scopeVar (advance S χs) Y) (scopeTy (advance S χs) B))
            bodyTrace (E.value out ↓ seal)))
        × (bodyGas ≤ gas)
        × (advance S (E.changes out) ≡ advance S χs)
  scoped-unseal-return-invert S {gas} {Y = Y} {B} entry typed ret
      with unseal-return-invert {Σ = scopeStore S} {gas = gas}
        (scope-entry S entry) typed ret
  scoped-unseal-return-invert S {Y = Y} {B} entry typed ret
      | bodyGas , χs , trace , bodyRet , budget , changesEq , typedU
      rewrite advance-variable S χs Y | advance-type S χs B =
    bodyGas , χs , trace , bodyRet ,
    ≤-trans (m≤m+n bodyGas 1) budget ,
    trans (cong (advance S) changesEq) (advance-keep S χs)

  scoped-unseal-return-expand : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
      (S : PhysicalScope Σ₀ Δ) {gas M Y B} {χs : StoreChanges Δ Δ′}
      {U : Term Δ′} {trace : M —↠[ χs ] U
        ↓ seal (scopeVar (advance S χs) Y) (scopeTy (advance S χs) B)}
    → (vU : Value U)
    → interpretFrom (scopeStore S) gas M ≡ returned
        (E.result Δ′ χs (U
          ↓ seal (scopeVar (advance S χs) Y) (scopeTy (advance S χs) B))
          trace (vU ↓ seal))
    → ∃[ wholeGas ] ∃ λ (wholeTrace :
        M ↑ unseal (scopeVar S Y) (scopeTy S B)
        —↠[ χs ++ˢ (keep ∷ []) ] U) →
        interpretFrom (scopeStore S) wholeGas
          (M ↑ unseal (scopeVar S Y) (scopeTy S B))
          ≡ returned (E.result Δ′ (χs ++ˢ (keep ∷ [])) U wholeTrace vU)
  scoped-unseal-return-expand S {gas} {Y = Y} {B} {χs} vU ret
      rewrite sym (advance-variable S χs Y) | sym (advance-type S χs B) =
    unseal-return-expand {Σ = scopeStore S} {gas = gas} vU ret

  abstract-arrow-typed : ∀ {Δ₀ Δ} {Σ₀ : TyStore Δ₀}
      (S : PhysicalScope Σ₀ Δ) {F X Y}
    → ⟨ Δ , scopeStore S , [] ⟩ ⊢ F ⦂ scopeTy S (＇ X ⇒ ＇ Y)
    → ⟨ Δ , scopeStore S , [] ⟩ ⊢ F
        ⦂ (＇ scopeVar S X ⇒ ＇ scopeVar S Y)
  abstract-arrow-typed S {F} {X} {Y} typed =
    subst≡ (λ A → ⟨ _ , scopeStore S , [] ⟩ ⊢ F ⦂ A)
      (trans (scope-arrow S (＇ X) (＇ Y))
        (cong₂ _⇒_ (scope-variable S X) (scope-variable S Y))) typed

  lift-function-seal : ∀ {Δ₀ Δ Δ′} {Σ₀ : TyStore Δ₀}
      {S : PhysicalScope Σ₀ Δ} {T : PhysicalScope Σ₀ Δ′}
      (p : ScopeFuture S T) X A Y B F
    → liftTerm p
        (reveal-function (scopeVar S X) (scopeTy S A)
          (scopeVar S Y) (scopeTy S B) F)
        ≡ reveal-function (scopeVar T X) (scopeTy T A)
            (scopeVar T Y) (scopeTy T B) (liftTerm p F)
  lift-function-seal stay X A Y B F = refl
  lift-function-seal {S = S} (grow p) X A Y B F
      rewrite toRename-wk-eq (scopeVar S X) | renameᵗ-wk-eq (scopeTy S A)
        | toRename-wk-eq (scopeVar S Y) | renameᵗ-wk-eq (scopeTy S B) =
    lift-function-seal p X A Y B (⇑ᵗᵐ F)

module Compatibility {Δᴵ₀ Δᴾ₀} (Σᴵ₀ : TyStore Δᴵ₀)
    (Σᴾ₀ : TyStore Δᴾ₀) where

  open Model Σᴵ₀ Σᴾ₀

  -- Matching pure prefixes need no fuel credit from the inner relation.
  -- Each observed prefix consumes a step; lower the returned residual index.

  observed-pure-steps : ∀ {Δᴵ Δᴾ} {B : ScopedType}
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ}
      {k M M′ N N′}
    → M ≢ blame → E.value? M ≡ nothing → (stepᴵ : M —→ M′)
    → E.step? (scopeStore S) M ≡ just (E.step-result keep M′ (pure-step stepᴵ))
    → N ≢ blame → E.value? N ≡ nothing → (stepᴾ : N —→ N′)
    → E.step? (scopeStore T) N ≡ just (E.step-result keep N′ (pure-step stepᴾ))
    → ObservedComputations B S T k M′ N′ → ObservedComputations B S T k M N
  observed-pure-steps {B = B} {S} {T} {k} {M} {M′} {N} {N′}
      notᴵ valᴵ stepᴵ eqᴵ notᴾ valᴾ stepᴾ eqᴾ c = record
    { forward-return = forward
    ; backward-return = backward
    ; forward-blame = blames
    }
    where
    forward : ∀ {n} {out : E.EvalResult M}
      → n < k → interpretFrom (scopeStore S) n M ≡ returned out
      → (∃[ m ] ∃[ out′ ] (interpretFrom (scopeStore T) m N ≡ returned out′)
          × related B (advance S (E.changes out)) (advance T (E.changes out′))
              (k ∸ n) (E.term out) (E.term out′))
        ⊎ (∃[ m ] BlamesFrom (scopeStore T) m N)
    forward {n} n<k ret with pure-step-return-invert
      {Σ = scopeStore S} {n = n} notᴵ valᴵ stepᴵ eqᴵ ret
    forward n<k ret | pure-step-return {gas} out bodyRet refl
        with ObservedComputations.forward-return c
          (≤-trans (s≤s (n≤1+n gas)) n<k) bodyRet
    forward n<k ret | pure-step-return {gas} out bodyRet refl
        | inj₁ (m , out′ , ret′ , r) =
      inj₁ (suc m , prepend-result (pure-step stepᴾ) out′ ,
        pure-step-return-expand {Σ = scopeStore T} {gas = m}
          notᴾ valᴾ stepᴾ eqᴾ ret′ ,
        downward B (∸-monoʳ-≤ k (n≤1+n gas)) r)
    forward n<k ret | pure-step-return {gas} out bodyRet refl
        | inj₂ (m , blame′) = inj₂ (suc m ,
      pure-step-blame-expand {Σ = scopeStore T} {gas = m}
        notᴾ valᴾ stepᴾ eqᴾ blame′)

    backward : ∀ {n} {out : E.EvalResult N}
      → n < k → interpretFrom (scopeStore T) n N ≡ returned out
      → ∃[ m ] ∃[ out′ ] (interpretFrom (scopeStore S) m M ≡ returned out′)
          × related B (advance S (E.changes out′)) (advance T (E.changes out))
              (k ∸ n) (E.term out′) (E.term out)
    backward {n} n<k ret with pure-step-return-invert
      {Σ = scopeStore T} {n = n} notᴾ valᴾ stepᴾ eqᴾ ret
    backward n<k ret | pure-step-return {gas} out bodyRet refl
        with ObservedComputations.backward-return c
          (≤-trans (s≤s (n≤1+n gas)) n<k) bodyRet
    backward n<k ret | pure-step-return {gas} out bodyRet refl
        | m , out′ , ret′ , r =
      suc m , prepend-result (pure-step stepᴵ) out′ ,
      pure-step-return-expand {Σ = scopeStore S} {gas = m}
        notᴵ valᴵ stepᴵ eqᴵ ret′ ,
      downward B (∸-monoʳ-≤ k (n≤1+n gas)) r

    blames : ∀ {n} → n < k → BlamesFrom (scopeStore S) n M
      → ∃[ m ] BlamesFrom (scopeStore T) m N
    blames {n} n<k blameM with pure-step-blame-invert
      {Σ = scopeStore S} {n = n} notᴵ valᴵ stepᴵ eqᴵ blameM
    blames n<k blameM | pure-step-blame {gas} bodyBlame
        with ObservedComputations.forward-blame c
          (≤-trans (s≤s (n≤1+n gas)) n<k) bodyBlame
    blames n<k blameM | pure-step-blame {gas} bodyBlame | m , blameN =
      suc m , pure-step-blame-expand {Σ = scopeStore T} {gas = m}
        notᴾ valᴾ stepᴾ eqᴾ blameN

  observed-unseals : ∀ {Δᴵ Δᴾ} (B : ScopedType)
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {k M N}
      X Y (entryX : Σᴵ₀ ∋ X ⦂ impreciseTy B)
      (entryY : Σᴾ₀ ∋ Y ⦂ preciseTy B)
    → ⟨ Δᴵ , scopeStore S , [] ⟩ ⊢ M ⦂ ＇ scopeVar S X
    → ⟨ Δᴾ , scopeStore T , [] ⟩ ⊢ N ⦂ ＇ scopeVar T Y
    → ObservedComputations (nominal B X Y entryX entryY) S T k M N
    → ObservedComputations B S T k
        (M ↑ unseal (scopeVar S X) (scopeTy S (impreciseTy B)))
        (N ↑ unseal (scopeVar T Y) (scopeTy T (preciseTy B)))
  observed-unseals B {S} {T} {k} {M} {N} X Y entryX entryY
      typedM typedN c = record
    { forward-return = forward
    ; backward-return = backward
    ; forward-blame = blames
    }
    where
    forward : ∀ {n} {out : E.EvalResult
        (M ↑ unseal (scopeVar S X) (scopeTy S (impreciseTy B)))}
      → n < k → interpretFrom (scopeStore S) n
          (M ↑ unseal (scopeVar S X) (scopeTy S (impreciseTy B)))
          ≡ returned out
      → (∃[ m ] ∃[ out′ ] (interpretFrom (scopeStore T) m
            (N ↑ unseal (scopeVar T Y) (scopeTy T (preciseTy B)))
            ≡ returned out′)
          × related B (advance S (E.changes out)) (advance T (E.changes out′))
              (k ∸ n) (E.term out) (E.term out′))
        ⊎ (∃[ m ] BlamesFrom (scopeStore T) m
            (N ↑ unseal (scopeVar T Y) (scopeTy T (preciseTy B))))
    forward {n} n<k ret
        with scoped-unseal-return-invert S entryX typedM ret
    forward {n} n<k ret | b , χs , trace , bodyRet , budget , scopeEq
        with ObservedComputations.forward-return c
          (≤-trans (s≤s budget) n<k) bodyRet
    forward {n} n<k ret | b , χs , trace , bodyRet , budget , scopeEq
        | inj₂ (m , blameN) = inj₂
      (Frame.operand-blame-expand revealFrame {Σ = scopeStore T}
        {operandGas = m}
        (reveal-frm (unseal (scopeVar T Y) (scopeTy T (preciseTy B)))) blameN)
    forward {n} n<k ret | b , χs , trace , bodyRet , budget , scopeEq
        | inj₁ (m , E.result Δ′ ψs ._ traceV (vV ↓ seal) , retV ,
            related-seals {Uᴾ = V} vU vV′ r)
        with scoped-unseal-return-expand T {gas = m} {Y = Y}
          {B = preciseTy B} vV retV
    forward {n} n<k ret | b , χs , trace , bodyRet , budget , scopeEq
        | inj₁ (m , E.result Δ′ ψs ._ traceV (vV ↓ seal) , retV ,
            related-seals {Uᴾ = V} vU vV′ r)
        | m′ , trace′ , ret′ =
      inj₁ (m′ , E.result Δ′ (ψs ++ˢ (keep ∷ [])) V trace′ vV , ret′ ,
        subst₂≡ (λ S′ T′ → related B S′ T′ (k ∸ n) _ V)
          (sym scopeEq) (sym (advance-keep T ψs))
          (downward B (∸-monoʳ-≤ k budget) r))

    backward : ∀ {n} {out : E.EvalResult
        (N ↑ unseal (scopeVar T Y) (scopeTy T (preciseTy B)))}
      → n < k → interpretFrom (scopeStore T) n
          (N ↑ unseal (scopeVar T Y) (scopeTy T (preciseTy B)))
          ≡ returned out
      → ∃[ m ] ∃[ out′ ] (interpretFrom (scopeStore S) m
            (M ↑ unseal (scopeVar S X) (scopeTy S (impreciseTy B)))
            ≡ returned out′)
          × related B (advance S (E.changes out′)) (advance T (E.changes out))
              (k ∸ n) (E.term out′) (E.term out)
    backward {n} n<k ret
        with scoped-unseal-return-invert T entryY typedN ret
    backward {n} n<k ret | b , ψs , trace , bodyRet , budget , scopeEq
        with ObservedComputations.backward-return c
          (≤-trans (s≤s budget) n<k) bodyRet
    backward {n} n<k ret | b , ψs , trace , bodyRet , budget , scopeEq
        | m , E.result Δ′ χs ._ traceU (vU ↓ seal) , retU ,
            related-seals {Uᴵ = U} vU′ vV r
        with scoped-unseal-return-expand S {gas = m} {Y = X}
          {B = impreciseTy B} vU retU
    backward {n} n<k ret | b , ψs , trace , bodyRet , budget , scopeEq
        | m , E.result Δ′ χs ._ traceU (vU ↓ seal) , retU ,
            related-seals {Uᴵ = U} vU′ vV r
        | m′ , trace′ , ret′ =
      m′ , E.result Δ′ (χs ++ˢ (keep ∷ [])) U trace′ vU , ret′ ,
      subst₂≡ (λ S′ T′ → related B S′ T′ (k ∸ n) U _)
        (sym (advance-keep S χs)) (sym scopeEq)
        (downward B (∸-monoʳ-≤ k budget) r)

    blames : ∀ {n} → n < k → BlamesFrom (scopeStore S) n
        (M ↑ unseal (scopeVar S X) (scopeTy S (impreciseTy B)))
      → ∃[ m ] BlamesFrom (scopeStore T) m
          (N ↑ unseal (scopeVar T Y) (scopeTy T (preciseTy B)))
    blames {n} n<k blameM
        with unseal-blame-invert {Σ = scopeStore S} {gas = n}
          (scope-entry S entryX) typedM blameM
    blames {n} n<k blameM | b , budget , bodyBlame
        with ObservedComputations.forward-blame c
          (≤-trans (s≤s budget) n<k) bodyBlame
    blames n<k blameM | b , budget , bodyBlame | m , blameN =
      Frame.operand-blame-expand revealFrame {Σ = scopeStore T}
        {operandGas = m}
        (reveal-frm (unseal (scopeVar T Y) (scopeTy T (preciseTy B)))) blameN

  observed-function-seals : ∀ {Δᴵ Δᴾ} (A B : ScopedType)
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {k F G U V}
      Xᴵ Xᴾ Yᴵ Yᴾ (entryXᴵ : Σᴵ₀ ∋ Xᴵ ⦂ impreciseTy A)
      (entryXᴾ : Σᴾ₀ ∋ Xᴾ ⦂ preciseTy A)
      (entryYᴵ : Σᴵ₀ ∋ Yᴵ ⦂ impreciseTy B)
      (entryYᴾ : Σᴾ₀ ∋ Yᴾ ⦂ preciseTy B)
    → Value F → Value G → Value U → Value V
    → ⟨ Δᴵ , scopeStore S , [] ⟩ ⊢ F ⦂ scopeTy S (＇ Xᴵ ⇒ ＇ Yᴵ)
    → ⟨ Δᴾ , scopeStore T , [] ⟩ ⊢ G ⦂ scopeTy T (＇ Xᴾ ⇒ ＇ Yᴾ)
    → ⟨ Δᴵ , scopeStore S , [] ⟩ ⊢ U ⦂ scopeTy S (impreciseTy A)
    → ⟨ Δᴾ , scopeStore T , [] ⟩ ⊢ V ⦂ scopeTy T (preciseTy A)
    → ObservedComputations (nominal B Yᴵ Yᴾ entryYᴵ entryYᴾ) S T k
        (F · (U ↓ seal (scopeVar S Xᴵ) (scopeTy S (impreciseTy A))))
        (G · (V ↓ seal (scopeVar T Xᴾ) (scopeTy T (preciseTy A))))
    → ObservedComputations B S T k
        (reveal-function (scopeVar S Xᴵ) (scopeTy S (impreciseTy A))
          (scopeVar S Yᴵ) (scopeTy S (impreciseTy B)) F · U)
        (reveal-function (scopeVar T Xᴾ) (scopeTy T (preciseTy A))
          (scopeVar T Yᴾ) (scopeTy T (preciseTy B)) G · V)
  observed-function-seals A B {S} {T} Xᴵ Xᴾ Yᴵ Yᴾ
      entryXᴵ entryXᴾ entryYᴵ entryYᴾ vF vG vU vV typedF typedG typedU typedV c
      with reveal-fun-app-step-question {Σ = scopeStore S}
        (seal (scopeVar S Xᴵ) (scopeTy S (impreciseTy A)))
        (unseal (scopeVar S Yᴵ) (scopeTy S (impreciseTy B))) vF vU
         | reveal-fun-app-step-question {Σ = scopeStore T}
        (seal (scopeVar T Xᴾ) (scopeTy T (preciseTy A)))
        (unseal (scopeVar T Yᴾ) (scopeTy T (preciseTy B))) vG vV
  observed-function-seals A B {S} {T} Xᴵ Xᴾ Yᴵ Yᴾ
      entryXᴵ entryXᴾ entryYᴵ entryYᴾ vF vG vU vV typedF typedG typedU typedV c
      | vF′ , vU′ , stepᴵ | vG′ , vV′ , stepᴾ =
    observed-pure-steps (λ ()) refl (β-reveal-⇒ vF′ vU′) stepᴵ
      (λ ()) refl (β-reveal-⇒ vG′ vV′) stepᴾ
      (observed-unseals B Yᴵ Yᴾ entryYᴵ entryYᴾ
        (⊢· (abstract-arrow-typed S typedF)
          (⊢conceal (⊢↓-seal (scope-entry S entryXᴵ)) typedU))
        (⊢· (abstract-arrow-typed T typedG)
          (⊢conceal (⊢↓-seal (scope-entry T entryXᴾ)) typedV)) c)

  -- The body observation is obtained from the abstract arrow clause. No
  -- extra body compatibility field is assumed by this value theorem.

  function-seals-related : ∀ {Δᴵ Δᴾ} (A B : ScopedType)
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ} {k F G}
      Xᴵ Xᴾ Yᴵ Yᴾ (entryXᴵ : Σᴵ₀ ∋ Xᴵ ⦂ impreciseTy A)
      (entryXᴾ : Σᴾ₀ ∋ Xᴾ ⦂ preciseTy A)
      (entryYᴵ : Σᴵ₀ ∋ Yᴵ ⦂ impreciseTy B)
      (entryYᴾ : Σᴾ₀ ∋ Yᴾ ⦂ preciseTy B)
    → related (arrow (nominal A Xᴵ Xᴾ entryXᴵ entryXᴾ)
        (nominal B Yᴵ Yᴾ entryYᴵ entryYᴾ)) S T k F G
    → related (arrow A B) S T k
        (reveal-function (scopeVar S Xᴵ) (scopeTy S (impreciseTy A))
          (scopeVar S Yᴵ) (scopeTy S (impreciseTy B)) F)
        (reveal-function (scopeVar T Xᴾ) (scopeTy T (preciseTy A))
          (scopeVar T Yᴾ) (scopeTy T (preciseTy B)) G)
  function-seals-related A B {S} {T} {k} {F} {G} Xᴵ Xᴾ Yᴵ Yᴾ
      entryXᴵ entryXᴾ entryYᴵ entryYᴾ r = arrow-values
    (ArrowValues.functionᴵ-value r ↑ fun) (ArrowValues.functionᴾ-value r ↑ fun)
    (subst≡ (λ C → ⟨ _ , scopeStore S , [] ⟩ ⊢ reveal-function
        (scopeVar S Xᴵ) (scopeTy S (impreciseTy A))
        (scopeVar S Yᴵ) (scopeTy S (impreciseTy B)) F ⦂ C)
      (sym (scope-arrow S (impreciseTy A) (impreciseTy B)))
      (reveal-function-typed (scope-entry S entryXᴵ) (scope-entry S entryYᴵ)
        (abstract-arrow-typed S (ArrowValues.functionᴵ-typed r))))
    (subst≡ (λ C → ⟨ _ , scopeStore T , [] ⟩ ⊢ reveal-function
        (scopeVar T Xᴾ) (scopeTy T (preciseTy A))
        (scopeVar T Yᴾ) (scopeTy T (preciseTy B)) G ⦂ C)
      (sym (scope-arrow T (preciseTy A) (preciseTy B)))
      (reveal-function-typed (scope-entry T entryXᴾ) (scope-entry T entryYᴾ)
        (abstract-arrow-typed T (ArrowValues.functionᴾ-typed r)))) call
    where
    call : ∀ {Δᴵ′ Δᴾ′} {S′ : PhysicalScope Σᴵ₀ Δᴵ′}
        {T′ : PhysicalScope Σᴾ₀ Δᴾ′} {j U V}
      → (p : ScopeFuture S S′) → (q : ScopeFuture T T′)
      → j < k → related A S′ T′ j U V
      → ObservedComputations B S′ T′ j
          (liftTerm p (reveal-function
            (scopeVar S Xᴵ) (scopeTy S (impreciseTy A))
            (scopeVar S Yᴵ) (scopeTy S (impreciseTy B)) F) · U)
          (liftTerm q (reveal-function
            (scopeVar T Xᴾ) (scopeTy T (preciseTy A))
            (scopeVar T Yᴾ) (scopeTy T (preciseTy B)) G) · V)
    call p q j<k args
        rewrite lift-function-seal p Xᴵ (impreciseTy A) Yᴵ (impreciseTy B) F
          | lift-function-seal q Xᴾ (preciseTy A) Yᴾ (preciseTy B) G =
      observed-function-seals A B Xᴵ Xᴾ Yᴵ Yᴾ
        entryXᴵ entryXᴾ entryYᴵ entryYᴾ
        (lift-value p (ArrowValues.functionᴵ-value r))
        (lift-value q (ArrowValues.functionᴾ-value r))
        (imprecise-value A args) (precise-value A args)
        (lift-root-typed p (ArrowValues.functionᴵ-typed r))
        (lift-root-typed q (ArrowValues.functionᴾ-typed r))
        (imprecise-typed A args) (precise-typed A args)
        (ArrowValues.call r p q j<k
          (related-seals (imprecise-value A args) (precise-value A args) args))
