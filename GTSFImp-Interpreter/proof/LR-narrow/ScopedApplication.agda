module proof.LR-narrow.ScopedApplication where

-- File Charter:
--   * Applies scoped related function values to related computations.
--   * Keeps one strict index bound for the function's call clause; argument
--     allocations advance both physical scopes and transport the functions.
--   * Uses generic frame composition, without evaluation equivariance.

open import Data.Nat using (_<_; s≤s)
open import Data.Nat.Properties using (≤-trans)
open import Relation.Binary.PropositionalEquality
  using (sym; trans; cong) renaming (subst₂ to subst₂≡)

open import Types
open import TyStore
open import CastTerms
open import proof.LR-narrow.ArgumentFrame using
  (argumentFrame; argument-frm; transports-function)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior
import proof.LR-narrow.ScopedFrameComposition as FC

module Applications {Δᴵ₀ Δᴾ₀} (Σᴵ₀ : TyStore Δᴵ₀)
    (Σᴾ₀ : TyStore Δᴾ₀) where

  open Model Σᴵ₀ Σᴾ₀
  module C = FC.Composition argumentFrame argumentFrame Σᴵ₀ Σᴾ₀

  application-observed : ∀ {Δᴵ Δᴾ} (A B : ScopedType)
      {S : PhysicalScope Σᴵ₀ Δᴵ} {T : PhysicalScope Σᴾ₀ Δᴾ}
      {j k F G M N}
    → j < k → related (arrow A B) S T k F G
    → ObservedComputations A S T j M N
    → ObservedComputations B S T j (F · M) (G · N)
  application-observed A B {S} {T} {F = F} {G} j<k r c =
    C.frame-observed
      (argument-frm F (ArrowValues.functionᴵ-value r))
      (argument-frm G (ArrowValues.functionᴾ-value r))
      (λ { χsᴵ χsᴾ {U = U} {V} j′≤j args →
        subst₂≡ (ObservedComputations B (advance S χsᴵ) (advance T χsᴾ) _)
          (cong (_· U) (trans (advance-term S χsᴵ F)
            (sym (transports-function χsᴵ F (ArrowValues.functionᴵ-value r)))))
          (cong (_· V) (trans (advance-term T χsᴾ G)
            (sym (transports-function χsᴾ G (ArrowValues.functionᴾ-value r)))))
          (ArrowValues.call r (advance-future S χsᴵ) (advance-future T χsᴾ)
            (≤-trans (s≤s j′≤j) j<k) args) }) c
