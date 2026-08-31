module proof.LR-narrow.RepeatedCastExamples where

-- File Charter:
--   * Whole-program CTI examples for repeated nonidentity casts.
--   * Exercises first-order, higher-order, and universal/function cast cycles
--     without changing CTI, LR, or evaluator definitions.
--   * Each executable program has typing and an evaluator witness ending in
--     first-order data or blame.

open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import TermCtx using (Z)
open import Consistency using
  (_⊢_∼_; _∼_; idᶜ; instᵐ; genᵐ; flipᵐ; id; _!; ？_; _↦_)
open import CastTerms
open import Imprecision using
  (ι⊑ι; ι⊑★; ★⊑★; ⇒⊑⇒)
open import Primitives using (κℕ; addℕ)
open import Reduction
open import Interpreter
import Eval as E
import proof.DGG.CastTermImprecision as CTI
open CTI using (_∣_⊢²_⊑_∶_)
import proof.DGG.CtxImp as CTX
import proof.DGG.ExampleTerms as Ex
import proof.DGG.Examples2 as Ex2

W₀ : CTX.World 0 0 0
W₀ = Ex2.reflWorld store-empty

ℕᵗ : Ty 0
ℕᵗ = ‵ `ℕ

ℕ! : idᶜ {Δ = 0} ⊢ ℕᵗ ∼ ★
ℕ! = id (‵ `ℕ) !

ℕ? : idᶜ {Δ = 0} ⊢ ★ ∼ ℕᵗ
ℕ? = ？ (id (‵ `ℕ))

natFun : Ty 0
natFun = ℕᵗ ⇒ ℕᵗ

starFun : Ty 0
starFun = ★ ⇒ ★

ℕ⇒ℕ! : idᶜ {Δ = 0} ⊢ natFun ∼ starFun
ℕ⇒ℕ! = ℕ? ↦ ℕ!

ℕ⇒ℕ? : idᶜ {Δ = 0} ⊢ starFun ∼ natFun
ℕ⇒ℕ? = ℕ! ↦ ℕ?

add-one : Term 0
add-one = ƛ (` zero ⊕[ addℕ ] $ (κℕ 1))

add-one-value : Value add-one
add-one-value = ƛ (` zero ⊕[ addℕ ] $ (κℕ 1))

add-one-⊢ : ⟨ 0 , store-empty , [] ⟩ ⊢ add-one ⦂ natFun
add-one-⊢ = ⊢ƛ (⊢⊕ addℕ (⊢` Z) (⊢$ (κℕ 1)))

add-one-cycle₃ : Term 0
add-one-cycle₃ =
  ((((((add-one ⟨ ℕ⇒ℕ! ⟩) ⟨ ℕ⇒ℕ? ⟩)
      ⟨ ℕ⇒ℕ! ⟩) ⟨ ℕ⇒ℕ? ⟩)
    ⟨ ℕ⇒ℕ! ⟩) ⟨ ℕ⇒ℕ? ⟩)

add-one-cycle₃-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ add-one-cycle₃ ⦂ natFun
add-one-cycle₃-⊢ =
  ⊢⟨⟩ (⊢⟨⟩ (⊢⟨⟩ (⊢⟨⟩ (⊢⟨⟩ (⊢⟨⟩ add-one-⊢
    ℕ⇒ℕ!) ℕ⇒ℕ?) ℕ⇒ℕ!) ℕ⇒ℕ?) ℕ⇒ℕ!) ℕ⇒ℕ?

ℕ⇒ℕ⊑ℕ⇒ℕ : natFun CTX.⊑ᵂ⟨ W₀ ⟩ natFun
ℕ⇒ℕ⊑ℕ⇒ℕ = ⇒⊑⇒ ι⊑ι ι⊑ι

ℕ⇒ℕ⊑★⇒★ : natFun CTX.⊑ᵂ⟨ W₀ ⟩ starFun
ℕ⇒ℕ⊑★⇒★ = ⇒⊑⇒ ι⊑★ ι⊑★

add-one-refl² : W₀ ∣ [] ⊢² add-one ⊑ add-one ∶ ℕ⇒ℕ⊑ℕ⇒ℕ
add-one-refl² =
  CTI.ƛ⊑ƛ²
    (CTI.⊕⊑⊕² addℕ
      (CTI.x⊑x² {p = ι⊑ι} CTX.Zʷ)
      (CTI.κ⊑κ² (κℕ 1) ι⊑ι)
      ι⊑ι)

add-one-cycle₃² :
  W₀ ∣ [] ⊢² add-one ⊑ add-one-cycle₃ ∶ ℕ⇒ℕ⊑ℕ⇒ℕ
add-one-cycle₃² =
  CTI.⊑cast² ℕ⇒ℕ?
    (CTI.⊑cast² ℕ⇒ℕ!
      (CTI.⊑cast² ℕ⇒ℕ?
        (CTI.⊑cast² ℕ⇒ℕ!
          (CTI.⊑cast² ℕ⇒ℕ?
            (CTI.⊑cast² ℕ⇒ℕ! add-one-refl² ℕ⇒ℕ⊑★⇒★)
            ℕ⇒ℕ⊑ℕ⇒ℕ)
          ℕ⇒ℕ⊑★⇒★)
        ℕ⇒ℕ⊑ℕ⇒ℕ)
      ℕ⇒ℕ⊑★⇒★)
    ℕ⇒ℕ⊑ℕ⇒ℕ

first-order-source : ℕ → Term 0
first-order-source n = add-one · $ (κℕ n)

first-order-target : ℕ → Term 0
first-order-target n = add-one-cycle₃ · $ (κℕ n)

first-order-source-⊢ : ∀ n
  → ⟨ 0 , store-empty , [] ⟩ ⊢ first-order-source n ⦂ ℕᵗ
first-order-source-⊢ n = ⊢· add-one-⊢ (⊢$ (κℕ n))

first-order-target-⊢ : ∀ n
  → ⟨ 0 , store-empty , [] ⟩ ⊢ first-order-target n ⦂ ℕᵗ
first-order-target-⊢ n = ⊢· add-one-cycle₃-⊢ (⊢$ (κℕ n))

first-order² : ∀ n
  → W₀ ∣ [] ⊢² first-order-source n
      ⊑ first-order-target n ∶ ι⊑ι
first-order² n =
  CTI.·⊑·² add-one-cycle₃² (CTI.κ⊑κ² (κℕ n) ι⊑ι)

first-order-source-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 0 Δ′ ]
    Σ[ trace ∈ first-order-source n —↠[ changes ] $ (κℕ (n + 1)) ]
      interpretFrom store-empty 4 (first-order-source n)
        ≡ returned
          (E.result Δ′ changes ($ (κℕ (n + 1))) trace ($ (κℕ (n + 1))))
first-order-source-return n = _ , _ , _ , refl

first-order-target-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 0 Δ′ ]
    Σ[ trace ∈ first-order-target n —↠[ changes ] $ (κℕ (n + 1)) ]
      interpretFrom store-empty 40 (first-order-target n)
        ≡ returned
          (E.result Δ′ changes ($ (κℕ (n + 1))) trace ($ (κℕ (n + 1))))
first-order-target-return n = _ , _ , _ , refl

------------------------------------------------------------------------
-- C2: two higher-order cycles around (ℕ⇒ℕ)⇒ℕ, then apply a casted
--     function.
------------------------------------------------------------------------

hoNat : Ty 0
hoNat = natFun ⇒ ℕᵗ

hoStar : Ty 0
hoStar = starFun ⇒ ★

hoNat! : idᶜ {Δ = 0} ⊢ hoNat ∼ hoStar
hoNat! = ℕ⇒ℕ? ↦ ℕ!

hoNat? : idᶜ {Δ = 0} ⊢ hoStar ∼ hoNat
hoNat? = ℕ⇒ℕ! ↦ ℕ?

apply-to-one : Term 0
apply-to-one = ƛ (` zero · $ (κℕ 1))

apply-to-one-value : Value apply-to-one
apply-to-one-value = ƛ (` zero · $ (κℕ 1))

apply-to-one-⊢ : ⟨ 0 , store-empty , [] ⟩ ⊢ apply-to-one ⦂ hoNat
apply-to-one-⊢ = ⊢ƛ (⊢· (⊢` Z) (⊢$ (κℕ 1)))

apply-to-one-cycle₂ : Term 0
apply-to-one-cycle₂ =
  ((((apply-to-one ⟨ hoNat! ⟩) ⟨ hoNat? ⟩)
    ⟨ hoNat! ⟩) ⟨ hoNat? ⟩)

apply-to-one-cycle₂-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ apply-to-one-cycle₂ ⦂ hoNat
apply-to-one-cycle₂-⊢ =
  ⊢⟨⟩ (⊢⟨⟩ (⊢⟨⟩ (⊢⟨⟩ apply-to-one-⊢
    hoNat!) hoNat?) hoNat!) hoNat?

hoNat⊑hoNat : hoNat CTX.⊑ᵂ⟨ W₀ ⟩ hoNat
hoNat⊑hoNat = ⇒⊑⇒ ℕ⇒ℕ⊑ℕ⇒ℕ ι⊑ι

hoNat⊑hoStar : hoNat CTX.⊑ᵂ⟨ W₀ ⟩ hoStar
hoNat⊑hoStar = ⇒⊑⇒ ℕ⇒ℕ⊑★⇒★ ι⊑★

apply-to-one-refl² :
  W₀ ∣ [] ⊢² apply-to-one ⊑ apply-to-one ∶ hoNat⊑hoNat
apply-to-one-refl² =
  CTI.ƛ⊑ƛ²
    (CTI.·⊑·²
      (CTI.x⊑x² {p = ℕ⇒ℕ⊑ℕ⇒ℕ} CTX.Zʷ)
      (CTI.κ⊑κ² (κℕ 1) ι⊑ι))

apply-to-one-cycle₂² :
  W₀ ∣ [] ⊢² apply-to-one ⊑ apply-to-one-cycle₂ ∶ hoNat⊑hoNat
apply-to-one-cycle₂² =
  CTI.⊑cast² hoNat?
    (CTI.⊑cast² hoNat!
      (CTI.⊑cast² hoNat?
        (CTI.⊑cast² hoNat! apply-to-one-refl² hoNat⊑hoStar)
        hoNat⊑hoNat)
      hoNat⊑hoStar)
    hoNat⊑hoNat

higher-order-source : Term 0
higher-order-source = apply-to-one · add-one

higher-order-target : Term 0
higher-order-target = apply-to-one-cycle₂ · add-one-cycle₃

higher-order-source-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ higher-order-source ⦂ ℕᵗ
higher-order-source-⊢ = ⊢· apply-to-one-⊢ add-one-⊢

higher-order-target-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ higher-order-target ⦂ ℕᵗ
higher-order-target-⊢ = ⊢· apply-to-one-cycle₂-⊢ add-one-cycle₃-⊢

higher-order² :
  W₀ ∣ [] ⊢² higher-order-source ⊑ higher-order-target ∶ ι⊑ι
higher-order² =
  CTI.·⊑·² apply-to-one-cycle₂² add-one-cycle₃²

higher-order-source-return :
  Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 0 Δ′ ]
    Σ[ trace ∈ higher-order-source —↠[ changes ] $ (κℕ 2) ]
      interpretFrom store-empty 8 higher-order-source
        ≡ returned (E.result Δ′ changes ($ (κℕ 2)) trace ($ (κℕ 2)))
higher-order-source-return = _ , _ , _ , refl

higher-order-target-return :
  Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 0 Δ′ ]
    Σ[ trace ∈ higher-order-target —↠[ changes ] $ (κℕ 2) ]
      interpretFrom store-empty 100 higher-order-target
        ≡ returned (E.result Δ′ changes ($ (κℕ 2)) trace ($ (κℕ 2)))
higher-order-target-return = _ , _ , _ , refl

------------------------------------------------------------------------
-- C3: two universal/function inst-gen cycles, then instantiate and apply
------------------------------------------------------------------------

polyFun : Ty 0
polyFun = `∀ Ex.X⇒X

polyId-cycle₂ : Term 0
polyId-cycle₂ =
  ((((Ex.polyId ⟨ Ex.ν̅α-α♯→α♭ ⟩) ⟨ Ex.να-α!→α? ⟩)
    ⟨ Ex.ν̅α-α♯→α♭ ⟩) ⟨ Ex.να-α!→α? ⟩)

polyId-cycle₂-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ polyId-cycle₂ ⦂ polyFun
polyId-cycle₂-⊢ =
  ⊢⟨⟩ (⊢⟨⟩ (⊢⟨⟩ (⊢⟨⟩ Ex.polyId-⊢
    Ex.ν̅α-α♯→α♭) Ex.να-α!→α?)
    Ex.ν̅α-α♯→α♭) Ex.να-α!→α?

polyFun⊑polyFun : polyFun CTX.⊑ᵂ⟨ W₀ ⟩ polyFun
polyFun⊑polyFun = Ex2.∀X⇒X⊑∀X⇒X² {W = W₀}

polyFun⊑starFun : polyFun CTX.⊑ᵂ⟨ W₀ ⟩ starFun
polyFun⊑starFun = Ex2.∀X⇒X⊑★⇒★² {W = W₀}

polyId-cycle₂² :
  W₀ ∣ [] ⊢² Ex.polyId ⊑ polyId-cycle₂ ∶ polyFun⊑polyFun
polyId-cycle₂² =
  CTI.⊑cast² Ex.να-α!→α?
    (CTI.⊑cast² Ex.ν̅α-α♯→α♭
      (CTI.⊑cast² Ex.να-α!→α?
        (CTI.⊑cast² Ex.ν̅α-α♯→α♭
          (Ex2.polyId-refl²ʷ {W = W₀})
          polyFun⊑starFun)
        polyFun⊑polyFun)
      polyFun⊑starFun)
    polyFun⊑polyFun

poly-cycle-source : ℕ → Term 0
poly-cycle-source n = (Ex.polyId ⦂∀ Ex.X⇒X [ ℕᵗ ]) · $ (κℕ n)

poly-cycle-target : ℕ → Term 0
poly-cycle-target n =
  (polyId-cycle₂ ⦂∀ Ex.X⇒X [ ℕᵗ ]) · $ (κℕ n)

poly-cycle-source-⊢ : ∀ n
  → ⟨ 0 , store-empty , [] ⟩ ⊢ poly-cycle-source n ⦂ ℕᵗ
poly-cycle-source-⊢ n = ⊢· (⊢• Ex.polyId-⊢) (⊢$ (κℕ n))

poly-cycle-target-⊢ : ∀ n
  → ⟨ 0 , store-empty , [] ⟩ ⊢ poly-cycle-target n ⦂ ℕᵗ
poly-cycle-target-⊢ n = ⊢· (⊢• polyId-cycle₂-⊢) (⊢$ (κℕ n))

poly-cycle² : ∀ n
  → W₀ ∣ [] ⊢² poly-cycle-source n ⊑ poly-cycle-target n ∶ ι⊑ι
poly-cycle² n =
  CTI.·⊑·²
    (CTI.•⊑•² polyFun⊑polyFun polyId-cycle₂²
      ι⊑ι ℕ⇒ℕ⊑ℕ⇒ℕ)
    (CTI.κ⊑κ² (κℕ n) ι⊑ι)

poly-cycle-source-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 0 Δ′ ]
    Σ[ trace ∈ poly-cycle-source n —↠[ changes ] $ (κℕ n) ]
      interpretFrom store-empty 6 (poly-cycle-source n)
        ≡ returned (E.result Δ′ changes ($ (κℕ n)) trace ($ (κℕ n)))
poly-cycle-source-return n = _ , _ , _ , refl

poly-cycle-target-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 0 Δ′ ]
    Σ[ trace ∈ poly-cycle-target n —↠[ changes ] $ (κℕ n) ]
      interpretFrom store-empty 120 (poly-cycle-target n)
        ≡ returned (E.result Δ′ changes ($ (κℕ n)) trace ($ (κℕ n)))
poly-cycle-target-return n = _ , _ , _ , refl
