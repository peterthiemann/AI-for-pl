module proof.DGG.Catchup.StructuralWorldLiftLeftProof where

-- File Charter:
--   * Lifts a structural target-extension trace under a source binder.
--   * Uses the canonical lifted target insertion at every bind.

import Data.Nat as Nat
import proof.DGG.CtxImp as CTI2
import proof.DGG.TargetExtend as TE
import Imprecision
open import Reduction using (StoreChanges)
open import proof.DGG.Catchup.StructuralWorldExtendDef


structural-lift-left : ∀ {Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
  → (plan : StructuralWorldExtendᴿ χs W W′)
  → (c : CTI2.VarImpᶜ)
  → StructuralWorldExtendᴿ χs
      (CTI2.liftWorldLeft CTI2.⟦ c ⟧ᶜ W)
      (CTI2.liftWorldLeft CTI2.⟦ c ⟧ᶜ W′)
structural-lift-left structural-[] c = structural-[]
structural-lift-left (structural-keep plan) c =
  structural-keep (structural-lift-left plan c)
structural-lift-left
    (structural-bind ins follows plan) CTI2.cX⊑X =
  structural-bind
    (TE.liftLeftTargetInsert {v = Imprecision.X⊑X} ins) follows
    (structural-lift-left plan CTI2.cX⊑X)
structural-lift-left
    (structural-bind ins follows plan) CTI2.cX⊑★ =
  structural-bind
    (TE.liftLeftTargetInsert {v = Imprecision.X⊑★} ins) follows
    (structural-lift-left plan CTI2.cX⊑★)


structural-lift-left-frozen : ∀ {k Δᴸ Δᴿ Δᴿ′ Δ Δ′}
    {χs : StoreChanges Δᴿ Δᴿ′}
    {W : CTI2.World Δᴸ Δᴿ Δ}
    {W′ : CTI2.World Δᴸ Δᴿ′ Δ′}
    {plan : StructuralWorldExtendᴿ χs W W′}
  → FrozenStructuralTraceᴿ k plan
  → {c : CTI2.VarImpᶜ}
  → FrozenStructuralTraceᴿ (Nat.suc k)
      (structural-lift-left plan c)
structural-lift-left-frozen frozen-trace-[] = frozen-trace-[]
structural-lift-left-frozen (frozen-trace-keep frozen) =
  frozen-trace-keep (structural-lift-left-frozen frozen)
structural-lift-left-frozen
    (frozen-trace-bind frozen-ins frozen) {c = CTI2.cX⊑X} =
  frozen-trace-bind (frozen-embedding-keep frozen-ins)
    (structural-lift-left-frozen frozen)
structural-lift-left-frozen
    (frozen-trace-bind frozen-ins frozen) {c = CTI2.cX⊑★} =
  frozen-trace-bind (frozen-embedding-keep frozen-ins)
    (structural-lift-left-frozen frozen)
