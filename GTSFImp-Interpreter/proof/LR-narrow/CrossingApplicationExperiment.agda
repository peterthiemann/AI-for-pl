module proof.LR-narrow.CrossingApplicationExperiment where

-- File Charter:
--   * Constructs the function/argument allocation-order crossing that tests
--     whether logical worlds may use only order-preserving embeddings.
--   * The precise function eagerly instantiates a polymorphic applicative map;
--     the imprecise function is an eta-delayed dynamic map value.
--   * Both arguments instantiate polymorphic identity before the outer call.
--   * Contains no change to cast-term imprecision or the logical relation.

open import Data.List using ([]; _∷_)
import Data.Fin as Fin
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore using (store-empty)
open import TermCtx using (TermCtx; Z; S)
open import Consistency
open import CastTerms
open import Primitives using (κℕ)
import Imprecision as I
open I using () renaming (_⊢_⊑_ to _⊢ᴵ_⊑_)
import Eval as E
import Reduction as R
open import Interpreter using (Outcome; timed; returned; blamed; run)
import proof.DGG.CastTermImprecision as CTI
open CTI using (_∣_⊢²_⊑_∶_)
import proof.DGG.CtxImp as CTX
import proof.DGG.Examples2 as Ex2

------------------------------------------------------------------------
-- Types and polymorphic producers
------------------------------------------------------------------------

ℕᵗ : Ty 0
ℕᵗ = ‵ `ℕ

ℕ! : idᶜ {Δ = 0} ⊢ ℕᵗ ∼ ★
ℕ! = id (‵ `ℕ) !

IdBody : Ty 1
IdBody = ＇ Fin.zero ⇒ ＇ Fin.zero

PolyId : Ty 0
PolyId = `∀ IdBody

StarFun : Ty 0
StarFun = ★ ⇒ ★

MapBody : Ty 2
MapBody = (＇ (Fin.suc Fin.zero) ⇒ ＇ Fin.zero) ⇒
  (＇ (Fin.suc Fin.zero) ⇒ ＇ Fin.zero)

MapAfterXBody : Ty 1
MapAfterXBody = (‵ `ℕ ⇒ ＇ Fin.zero) ⇒ (‵ `ℕ ⇒ ＇ Fin.zero)

MapOuterBody : Ty 1
MapOuterBody = `∀ MapBody

PolyMap : Ty 0
PolyMap = `∀ MapOuterBody

DynamicMap : Ty 0
DynamicMap = StarFun ⇒ StarFun

poly-id : Term 0
poly-id = Λ (ƛ (` Nat.zero))

poly-id-value : Value poly-id
poly-id-value = Λ (ƛ (` Nat.zero))

poly-id-typed : ⟨ 0 , store-empty , [] ⟩ ⊢ poly-id ⦂ PolyId
poly-id-typed = ⊢Λ (ƛ (` Nat.zero)) (⊢ƛ (⊢` Z))

poly-map : Term 0
poly-map = Λ (Λ (ƛ (ƛ (` (Nat.suc Nat.zero) · ` Nat.zero))))

poly-map-value : Value poly-map
poly-map-value =
  Λ (Λ (ƛ (ƛ (` (Nat.suc Nat.zero) · ` Nat.zero))))

poly-map-typed : ∀ {Γ : TermCtx 0}
  → ⟨ 0 , store-empty , Γ ⟩ ⊢ poly-map ⦂ PolyMap
poly-map-typed =
  ⊢Λ (Λ (ƛ (ƛ (` (Nat.suc Nat.zero) · ` Nat.zero))))
    (⊢Λ (ƛ (ƛ (` (Nat.suc Nat.zero) · ` Nat.zero)))
      (⊢ƛ (⊢ƛ (⊢· (⊢` (S Z)) (⊢` Z)))))

------------------------------------------------------------------------
-- The dynamic map is a value.  Its two polymorphic instantiations are
-- underneath both lambdas and therefore happen only after both arguments
-- have been evaluated.
------------------------------------------------------------------------

private
  XY∼StarFun : instᵐ (instᵐ (idᶜ {Δ = 0})) ⊢
    (＇ (Fin.suc Fin.zero) ⇒ ＇ Fin.zero) ∼ ⇑ᵗ (⇑ᵗ StarFun)
  XY∼StarFun =
    ？ (id (＇ (Fin.suc Fin.zero))) ↦ id (＇ Fin.zero) !

  MapBody∼Dynamic : instᵐ (instᵐ (idᶜ {Δ = 0})) ⊢
    MapBody ∼ ⇑ᵗ (⇑ᵗ DynamicMap)
  MapBody∼Dynamic = sym∼ XY∼StarFun ↦ XY∼StarFun

  MapOuterBody∼Dynamic : instᵐ (idᶜ {Δ = 0}) ⊢
    MapOuterBody ∼ ⇑ᵗ DynamicMap
  MapOuterBody∼Dynamic =
    (inst_ ⦃ z∈A = ∈-fun-left
        (∈-fun-right (∉-var fin-zero≢suc) var-∈) ⦄
      MapBody∼Dynamic) (λ ())

  PolyMap∼Dynamic : PolyMap ∼ DynamicMap
  PolyMap∼Dynamic =
    (inst_ ⦃ z∈A = ∈-all
        (∈-fun-left (∈-fun-left var-∈)) ⦄
      MapOuterBody∼Dynamic) (λ ())

dynamic-map : Term 0
dynamic-map =
  ƛ (ƛ (((poly-map ⟨ PolyMap∼Dynamic ⟩) · ` (Nat.suc Nat.zero))
    · ` Nat.zero))

dynamic-map-value : Value dynamic-map
dynamic-map-value =
  ƛ (ƛ (((poly-map ⟨ PolyMap∼Dynamic ⟩) · ` (Nat.suc Nat.zero))
    · ` Nat.zero))

dynamic-map-typed : ⟨ 0 , store-empty , [] ⟩ ⊢
  dynamic-map ⦂ DynamicMap
dynamic-map-typed =
  ⊢ƛ (⊢ƛ
    (⊢· (⊢· (⊢⟨⟩ poly-map-typed PolyMap∼Dynamic) (⊢` (S Z)))
      (⊢` Z)))

------------------------------------------------------------------------
-- Closed programs
------------------------------------------------------------------------

precise-map : Term 0
precise-map =
  (poly-map ⦂∀ MapOuterBody [ ℕᵗ ]) ⦂∀ MapAfterXBody [ ℕᵗ ]

precise-map-typed : ⟨ 0 , store-empty , [] ⟩ ⊢ precise-map ⦂
  ((ℕᵗ ⇒ ℕᵗ) ⇒ (ℕᵗ ⇒ ℕᵗ))
precise-map-typed = ⊢• (⊢• poly-map-typed)

precise-id : Term 0
precise-id = poly-id ⦂∀ IdBody [ ℕᵗ ]

precise-id-typed : ⟨ 0 , store-empty , [] ⟩ ⊢ precise-id ⦂
  (ℕᵗ ⇒ ℕᵗ)
precise-id-typed = ⊢• poly-id-typed

dynamic-id : Term 0
dynamic-id = poly-id ⦂∀ IdBody [ ★ ]

dynamic-id-typed : ⟨ 0 , store-empty , [] ⟩ ⊢ dynamic-id ⦂ StarFun
dynamic-id-typed = ⊢• poly-id-typed

precise-program : Term 0
precise-program = (precise-map · precise-id) · $ (κℕ 7)

precise-program-typed : ⟨ 0 , store-empty , [] ⟩ ⊢
  precise-program ⦂ ℕᵗ
precise-program-typed =
  ⊢· (⊢· precise-map-typed precise-id-typed) (⊢$ (κℕ 7))

dynamic-program : Term 0
dynamic-program =
  (dynamic-map · dynamic-id) · (($ (κℕ 7)) ⟨ ℕ! ⟩)

dynamic-program-typed : ⟨ 0 , store-empty , [] ⟩ ⊢
  dynamic-program ⦂ ★
dynamic-program-typed =
  ⊢· (⊢· dynamic-map-typed dynamic-id-typed)
    (⊢⟨⟩ (⊢$ (κℕ 7)) ℕ!)

------------------------------------------------------------------------
-- The open CTI instance used by the fundamental property
------------------------------------------------------------------------

W₀ : CTX.World 0 0 0
W₀ = Ex2.reflWorld store-empty

PolyId⊑PolyId : PolyId CTX.⊑ᵂ⟨ W₀ ⟩ PolyId
PolyId⊑PolyId = I.∀⊑∀ (I.⇒⊑⇒ I.X⊑X I.X⊑X)

private
  XY⊑StarFun : I.instᵐ (I.instᵐ (I.idᵐ {Δ = 0}))
    ⊢ᴵ (＇ (Fin.suc Fin.zero) ⇒ ＇ Fin.zero) ⊑ ⇑ᵗ (⇑ᵗ StarFun)
  XY⊑StarFun =
    I.⇒⊑⇒ (I.X⊑★ refl) (I.X⊑★ refl)

  MapBody⊑Dynamic : I.instᵐ (I.instᵐ (I.idᵐ {Δ = 0}))
    ⊢ᴵ MapBody ⊑ ⇑ᵗ (⇑ᵗ DynamicMap)
  MapBody⊑Dynamic = I.⇒⊑⇒ XY⊑StarFun XY⊑StarFun

  MapOuterBody⊑Dynamic : I.instᵐ (I.idᵐ {Δ = 0})
    ⊢ᴵ MapOuterBody ⊑ ⇑ᵗ DynamicMap
  MapOuterBody⊑Dynamic =
    I.∀⊑ nonvar-fun
      (∈-fun-left (∈-fun-right (∉-var fin-zero≢suc) var-∈))
      MapBody⊑Dynamic

PolyMap⊑Dynamic : PolyMap CTX.⊑ᵂ⟨ W₀ ⟩ DynamicMap
PolyMap⊑Dynamic =
  I.∀⊑ nonvar-all
    (∈-all (∈-fun-left (∈-fun-left var-∈)))
    MapOuterBody⊑Dynamic

private
  NatY⊑StarFun : I.instᵐ (I.idᵐ {Δ = 0})
    ⊢ᴵ (‵ `ℕ ⇒ ＇ Fin.zero) ⊑ ⇑ᵗ StarFun
  NatY⊑StarFun = I.⇒⊑⇒ I.ι⊑★ (I.X⊑★ refl)

  MapAfterXBody⊑Dynamic : I.instᵐ (I.idᵐ {Δ = 0})
    ⊢ᴵ MapAfterXBody ⊑ ⇑ᵗ DynamicMap
  MapAfterXBody⊑Dynamic = I.⇒⊑⇒ NatY⊑StarFun NatY⊑StarFun

MapAfterXAll⊑Dynamic :
  (`∀ MapAfterXBody) CTX.⊑ᵂ⟨ W₀ ⟩ DynamicMap
MapAfterXAll⊑Dynamic =
  I.∀⊑ nonvar-fun
    (∈-fun-left (∈-fun-right ∉-base var-∈))
    MapAfterXBody⊑Dynamic

NatFun⊑StarFun : (ℕᵗ ⇒ ℕᵗ) CTX.⊑ᵂ⟨ W₀ ⟩ StarFun
NatFun⊑StarFun = I.⇒⊑⇒ I.ι⊑★ I.ι⊑★

NatMap⊑Dynamic :
  ((ℕᵗ ⇒ ℕᵗ) ⇒ (ℕᵗ ⇒ ℕᵗ))
    CTX.⊑ᵂ⟨ W₀ ⟩ DynamicMap
NatMap⊑Dynamic = I.⇒⊑⇒ NatFun⊑StarFun NatFun⊑StarFun

ℕ⊑★ : ℕᵗ CTX.⊑ᵂ⟨ W₀ ⟩ ★
ℕ⊑★ = I.ι⊑★

open-context : CTX.CtxImp W₀
open-context =
  CTX.ctx-imp PolyId PolyId PolyId⊑PolyId ∷
  CTX.ctx-imp PolyMap DynamicMap PolyMap⊑Dynamic ∷ []

precise-open-function : Term 0
precise-open-function =
  ((` (Nat.suc Nat.zero)) ⦂∀ MapOuterBody [ ℕᵗ ])
    ⦂∀ MapAfterXBody [ ℕᵗ ]

dynamic-open-function : Term 0
dynamic-open-function = ` (Nat.suc Nat.zero)

open-function² :
  W₀ ∣ open-context ⊢² precise-open-function
    ⊑ dynamic-open-function ∶ NatMap⊑Dynamic
open-function² =
  CTI.•⊑² MapAfterXAll⊑Dynamic
    (CTI.•⊑² PolyMap⊑Dynamic
      (CTI.x⊑x² (CTX.Sʷ CTX.Zʷ)) ℕ⊑★ MapAfterXAll⊑Dynamic)
    ℕ⊑★ NatMap⊑Dynamic

precise-open-argument : Term 0
precise-open-argument = (` Nat.zero) ⦂∀ IdBody [ ℕᵗ ]

dynamic-open-argument : Term 0
dynamic-open-argument = (` Nat.zero) ⦂∀ IdBody [ ★ ]

open-argument² :
  W₀ ∣ open-context ⊢² precise-open-argument
    ⊑ dynamic-open-argument ∶ NatFun⊑StarFun
open-argument² =
  CTI.•⊑•² PolyId⊑PolyId (CTI.x⊑x² CTX.Zʷ)
    ℕ⊑★ NatFun⊑StarFun

precise-open-program : Term 0
precise-open-program =
  (precise-open-function · precise-open-argument) · $ (κℕ 7)

dynamic-open-program : Term 0
dynamic-open-program =
  (dynamic-open-function · dynamic-open-argument) ·
    (($ (κℕ 7)) ⟨ ℕ! ⟩)

open-program² :
  W₀ ∣ open-context ⊢² precise-open-program
    ⊑ dynamic-open-program ∶ ℕ⊑★
open-program² =
  CTI.·⊑·²
    (CTI.·⊑·² open-function² open-argument²)
    (CTI.⊑cast² ℕ!
      (CTI.κ⊑κ² (κℕ 7) I.ι⊑ι) ℕ⊑★)

precise-closing : Subst 0
precise-closing Nat.zero = poly-id
precise-closing (Nat.suc Nat.zero) = poly-map
precise-closing (Nat.suc (Nat.suc x)) = blame

dynamic-closing : Subst 0
dynamic-closing Nat.zero = poly-id
dynamic-closing (Nat.suc Nat.zero) = dynamic-map
dynamic-closing (Nat.suc (Nat.suc x)) = blame

precise-open-closes :
  subst precise-closing precise-open-program ≡ precise-program
precise-open-closes = refl

dynamic-open-closes :
  subst dynamic-closing dynamic-open-program ≡ dynamic-program
dynamic-open-closes = refl

------------------------------------------------------------------------
-- Executable allocation observations
------------------------------------------------------------------------

allocation-count : ∀ {Δ Δ′} → R.StoreChanges Δ Δ′ → Nat.ℕ
allocation-count R.[] = Nat.zero
allocation-count (R.keep R.∷ changes) = allocation-count changes
allocation-count (R.bind A R.∷ changes) =
  Nat.suc (allocation-count changes)

outcome-allocation-count : ∀ {Δ} {M : Term Δ} → Outcome M → Nat.ℕ
outcome-allocation-count timed = Nat.zero
outcome-allocation-count (returned eval-result) =
  allocation-count (E.changes eval-result)
outcome-allocation-count (blamed changes trace) = allocation-count changes

precise-function-allocations :
  outcome-allocation-count (run 30 precise-map) ≡ 3
precise-function-allocations = refl

precise-argument-allocations :
  outcome-allocation-count (run 20 precise-id) ≡ 1
precise-argument-allocations = refl

dynamic-function-allocations :
  outcome-allocation-count (run 0 dynamic-map) ≡ 0
dynamic-function-allocations = refl

dynamic-argument-allocations :
  outcome-allocation-count (run 20 dynamic-id) ≡ 1
dynamic-argument-allocations = refl

star-id : Term 0
star-id = ƛ (` Nat.zero)

dynamic-call : Term 0
dynamic-call =
  (dynamic-map · star-id) · (($ (κℕ 7)) ⟨ ℕ! ⟩)

dynamic-call-delayed-allocations :
  outcome-allocation-count (run 150 dynamic-call) ≡ 6
dynamic-call-delayed-allocations = refl

precise-total-allocations :
  outcome-allocation-count (run 80 precise-program) ≡ 4
precise-total-allocations = refl

dynamic-total-allocations :
  outcome-allocation-count (run 160 dynamic-program) ≡ 7
dynamic-total-allocations = refl
