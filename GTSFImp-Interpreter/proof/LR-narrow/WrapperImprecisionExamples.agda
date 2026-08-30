module proof.LR-narrow.WrapperImprecisionExamples where

-- File Charter:
--   * Closed CTI examples for constant and identity universal wrappers.
--   * Keeps CTI imprecision examples separate from semantic closure tests:
--     these derivations exercise syntax-directed imprecision constructors,
--     not a fundamental-property theorem.
--   * Gives each executable fixture a typing derivation and an evaluator
--     witness that ends in first-order natural data.

open import Data.List using (_∷_; [])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _,_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types
open import TyStore
open import TermCtx using (Z)
open import CastTerms
open import Conversion
open import Primitives using (κℕ)
open import Imprecision using (X⊑X; ι⊑ι; ⇒⊑⇒; ∀⊑∀)
open import Reduction
open import Interpreter
import Eval as E
import proof.DGG.CastTermImprecision as CTI
open CTI using (_∣_⊢²_⊑_∶_)
import proof.DGG.CtxImp as CTX
import proof.DGG.Examples2 as Ex2
import proof.LR-narrow.ScopedUniversalExperiment as SU
import proof.LR-narrow.ScopedRightUniversalWrapperExperiment as RW

W₀ : CTX.World 0 0 0
W₀ = Ex2.reflWorld store-empty

nat∀ : Ty 0
nat∀ = `∀ (‵ `ℕ)

id∀ : Ty 0
id∀ = `∀ (＇ Fin.zero ⇒ ＇ Fin.zero)

id-body : Ty 1
id-body = ＇ Fin.zero ⇒ ＇ Fin.zero

ho-body : Ty 1
ho-body = id-body ⇒ id-body

id∀-reveal : Conv↑ 0 id∀ id∀
id∀-reveal = `∀↑ id↑ id-body

id∀-conceal : Conv↓ 0 id∀ id∀
id∀-conceal = `∀↓ id↓ id-body

ho-reveal : Conv↑ 0 (`∀ ho-body) (`∀ ho-body)
ho-reveal = `∀↑ id↑ ho-body

mono-refl : CTX.ImpEnvMono W₀ W₀
mono-refl _ eq = eq

nat∀⊑nat∀ : nat∀ CTX.⊑ᵂ⟨ W₀ ⟩ nat∀
nat∀⊑nat∀ = ∀⊑∀ ι⊑ι

id∀⊑id∀ : id∀ CTX.⊑ᵂ⟨ W₀ ⟩ id∀
id∀⊑id∀ = Ex2.∀X⇒X⊑∀X⇒X² {W = W₀}

ho-body⊑ho-body :
  ho-body CTX.⊑ᵂ⟨ CTX.liftWorldBoth X⊑X W₀ ⟩ ho-body
ho-body⊑ho-body =
  ⇒⊑⇒ (Ex2.X⇒X⊑X⇒X-lift² {W = W₀})
    (Ex2.X⇒X⊑X⇒X-lift² {W = W₀})

ho∀⊑ho∀ : `∀ ho-body CTX.⊑ᵂ⟨ W₀ ⟩ `∀ ho-body
ho∀⊑ho∀ = ∀⊑∀ ho-body⊑ho-body

constant-refl² : ∀ n
  → W₀ ∣ [] ⊢² SU.constant-polymorphic n
      ⊑ SU.constant-polymorphic n ∶ nat∀⊑nat∀
constant-refl² n =
  CTI.Λ⊑Λ² CTX.lift-[] ($ (κℕ n)) ($ (κℕ n))
    (CTI.κ⊑κ² (κℕ n) ι⊑ι) nat∀⊑nat∀

constant-reveal² : ∀ n
  → W₀ ∣ [] ⊢² SU.constant-polymorphic n
      ⊑ SU.wrapped-constant n ∶ nat∀⊑nat∀
constant-reveal² n =
  CTI.⊑reveal² mono-refl CTX.rebase-idᴿ CTX.same-[]
    (⊢↑-∀-idˣ ⊢↑-idˣ) (constant-refl² n) nat∀⊑nat∀

identity-refl² :
  W₀ ∣ [] ⊢² SU.polymorphic-identity
    ⊑ SU.polymorphic-identity ∶ id∀⊑id∀
identity-refl² =
  CTI.Λ⊑Λ² CTX.lift-[] (ƛ (` zero)) (ƛ (` zero))
    (CTI.ƛ⊑ƛ² {pA = Ex2.X⊑X-lift² {W = W₀}}
      {pB = Ex2.X⊑X-lift² {W = W₀}}
      (CTI.x⊑x² {p = Ex2.X⊑X-lift² {W = W₀}} CTX.Zʷ))
    id∀⊑id∀

identity-reveal² :
  W₀ ∣ [] ⊢² SU.polymorphic-identity
    ⊑ SU.polymorphic-identity ↑ id∀-reveal ∶ id∀⊑id∀
identity-reveal² =
  CTI.⊑reveal² mono-refl CTX.rebase-idᴿ CTX.same-[]
    (⊢↑-∀-idˣ ⊢↑-idˣ) identity-refl² id∀⊑id∀

identity-conceal² :
  W₀ ∣ [] ⊢² SU.polymorphic-identity
    ⊑ (SU.polymorphic-identity ↑ id∀-reveal) ↓ id∀-conceal
    ∶ id∀⊑id∀
identity-conceal² =
  CTI.⊑conceal² mono-refl CTX.rebase-idᴿ CTX.same-[]
    (⊢↓-∀-idˣ ⊢↓-idˣ) identity-reveal² id∀⊑id∀

identity-mixed² :
  W₀ ∣ [] ⊢² SU.polymorphic-identity
    ⊑ ((SU.polymorphic-identity ↑ id∀-reveal) ↓ id∀-conceal)
      ↑ id∀-reveal
    ∶ id∀⊑id∀
identity-mixed² =
  CTI.⊑reveal² mono-refl CTX.rebase-idᴿ CTX.same-[]
    (⊢↑-∀-idˣ ⊢↑-idˣ) identity-conceal² id∀⊑id∀

higher-identity : Term 0
higher-identity = Λ (ƛ (` zero))

higher-identity-value : Value higher-identity
higher-identity-value = Λ (ƛ (` zero))

higher-identity-⊢ :
  ⟨ 0 , store-empty , [] ⟩ ⊢ higher-identity ⦂ `∀ ho-body
higher-identity-⊢ = ⊢Λ (ƛ (` zero)) (⊢ƛ (⊢` Z))

higher-identity-refl² :
  W₀ ∣ [] ⊢² higher-identity
    ⊑ higher-identity ∶ ho∀⊑ho∀
higher-identity-refl² =
  CTI.Λ⊑Λ² CTX.lift-[] (ƛ (` zero)) (ƛ (` zero))
    (CTI.ƛ⊑ƛ² {pA = Ex2.X⇒X⊑X⇒X-lift² {W = W₀}}
      {pB = Ex2.X⇒X⊑X⇒X-lift² {W = W₀}}
      (CTI.x⊑x² {p = Ex2.X⇒X⊑X⇒X-lift² {W = W₀}} CTX.Zʷ))
    ho∀⊑ho∀

higher-identity-reveal² :
  W₀ ∣ [] ⊢² higher-identity
    ⊑ higher-identity ↑ ho-reveal ∶ ho∀⊑ho∀
higher-identity-reveal² =
  CTI.⊑reveal² mono-refl CTX.rebase-idᴿ CTX.same-[]
    (⊢↑-∀-idˣ ⊢↑-idˣ) higher-identity-refl² ho∀⊑ho∀

constant-source-runtime : ℕ → Term 0
constant-source-runtime n =
  SU.constant-polymorphic n ⦂∀ (‵ `ℕ) [ ‵ `ℕ ]

constant-source-runtime-⊢ : ∀ n
  → ⟨ 0 , store-empty , [] ⟩ ⊢ constant-source-runtime n ⦂ ‵ `ℕ
constant-source-runtime-⊢ n = ⊢• (SU.constant-polymorphic-⊢ n)

constant-source-runtime-return : ∀ n
  → interpretFrom store-empty 2 (constant-source-runtime n)
      ≡ returned (E.result 1 (bind (‵ `ℕ) ∷ keep ∷ [])
        ($ (κℕ n)) _ ($ (κℕ n)))
constant-source-runtime-return n = SU.constant-return store-empty (‵ `ℕ) n

constant-reveal-runtime : ℕ → Term 0
constant-reveal-runtime n =
  SU.wrapped-constant n ⦂∀ (‵ `ℕ) [ ‵ `ℕ ]

constant-reveal-runtime-⊢ : ∀ n
  → ⟨ 0 , store-empty , [] ⟩ ⊢ constant-reveal-runtime n ⦂ ‵ `ℕ
constant-reveal-runtime-⊢ n = ⊢• (SU.wrapped-constant-⊢ n)

constant-reveal-runtime-return : ∀ n
  → interpretFrom store-empty 5 (constant-reveal-runtime n)
      ≡ returned (E.result 2
        (bind (‵ `ℕ) ∷ bind (＇ Fin.zero) ∷
          keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ n)) _ ($ (κℕ n)))
constant-reveal-runtime-return n =
  SU.wrapped-constant-return store-empty (‵ `ℕ) n

identity-source-runtime : ℕ → Term 0
identity-source-runtime = SU.identity-natural-call

identity-source-runtime-⊢ : ∀ n
  → ⟨ 0 , store-empty , [] ⟩ ⊢ identity-source-runtime n ⦂ ‵ `ℕ
identity-source-runtime-⊢ = SU.identity-natural-call-⊢

identity-source-runtime-return : ∀ n
  → interpretFrom store-empty 4 (identity-source-runtime n)
      ≡ returned (E.result 1
        (bind (‵ `ℕ) ∷ keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ n)) _ ($ (κℕ n)))
identity-source-runtime-return n =
  SU.identity-natural-call-return store-empty n

identity-reveal-runtime : ℕ → Term 0
identity-reveal-runtime = RW.target-runtime

identity-reveal-runtime-⊢ : ∀ n
  → ⟨ 0 , store-empty , [] ⟩ ⊢ identity-reveal-runtime n ⦂ ‵ `ℕ
identity-reveal-runtime-⊢ = RW.target-runtime-⊢

identity-reveal-runtime-return : ∀ n
  → interpretFrom store-empty 8 (identity-reveal-runtime n)
      ≡ returned (E.result 2
        (bind (‵ `ℕ) ∷ bind (＇ Fin.zero) ∷
          keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ keep ∷ [])
        ($ (κℕ n)) _ ($ (κℕ n)))
identity-reveal-runtime-return = RW.target-runtime-return

identity-reveal-same-fuel-times-out : ∀ n
  → interpretFrom store-empty 4 (identity-reveal-runtime n) ≡ timed
identity-reveal-same-fuel-times-out n = refl

identity-conceal-runtime : ℕ → Term 0
identity-conceal-runtime n =
  (((SU.polymorphic-identity ↑ id∀-reveal) ↓ id∀-conceal)
    ⦂∀ id-body [ ‵ `ℕ ]) · $ (κℕ n)

identity-conceal-runtime-⊢ : ∀ n
  → ⟨ 0 , store-empty , [] ⟩ ⊢ identity-conceal-runtime n ⦂ ‵ `ℕ
identity-conceal-runtime-⊢ n =
  ⊢· (⊢• (⊢conceal (⊢↓-∀ ⊢↓-id)
    (⊢reveal (⊢↑-∀ ⊢↑-id) SU.polymorphic-identity-⊢))) (⊢$ (κℕ n))

identity-conceal-runtime-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 0 Δ′ ]
    Σ[ trace ∈ identity-conceal-runtime n —↠[ changes ] $ (κℕ n) ]
      interpretFrom store-empty 16 (identity-conceal-runtime n)
        ≡ returned (E.result Δ′ changes ($ (κℕ n)) trace ($ (κℕ n)))
identity-conceal-runtime-return n = _ , _ , _ , refl

identity-mixed-runtime : ℕ → Term 0
identity-mixed-runtime n =
  ((((SU.polymorphic-identity ↑ id∀-reveal) ↓ id∀-conceal) ↑ id∀-reveal)
    ⦂∀ id-body [ ‵ `ℕ ]) · $ (κℕ n)

identity-mixed-runtime-⊢ : ∀ n
  → ⟨ 0 , store-empty , [] ⟩ ⊢ identity-mixed-runtime n ⦂ ‵ `ℕ
identity-mixed-runtime-⊢ n =
  ⊢· (⊢• (⊢reveal (⊢↑-∀ ⊢↑-id)
    (⊢conceal (⊢↓-∀ ⊢↓-id)
      (⊢reveal (⊢↑-∀ ⊢↑-id) SU.polymorphic-identity-⊢))))
    (⊢$ (κℕ n))

identity-mixed-runtime-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 0 Δ′ ]
    Σ[ trace ∈ identity-mixed-runtime n —↠[ changes ] $ (κℕ n) ]
      interpretFrom store-empty 20 (identity-mixed-runtime n)
        ≡ returned (E.result Δ′ changes ($ (κℕ n)) trace ($ (κℕ n)))
identity-mixed-runtime-return n = _ , _ , _ , refl

higher-runtime : ℕ → Term 0
higher-runtime n =
  (((higher-identity ↑ ho-reveal) ⦂∀ ho-body [ ‵ `ℕ ])
    · (ƛ (` zero))) · $ (κℕ n)

higher-runtime-⊢ : ∀ n
  → ⟨ 0 , store-empty , [] ⟩ ⊢ higher-runtime n ⦂ ‵ `ℕ
higher-runtime-⊢ n =
  ⊢· (⊢· (⊢• (⊢reveal (⊢↑-∀ ⊢↑-id) higher-identity-⊢))
    (⊢ƛ (⊢` Z))) (⊢$ (κℕ n))

higher-runtime-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 0 Δ′ ]
    Σ[ trace ∈ higher-runtime n —↠[ changes ] $ (κℕ n) ]
      interpretFrom store-empty 16 (higher-runtime n)
        ≡ returned (E.result Δ′ changes ($ (κℕ n)) trace ($ (κℕ n)))
higher-runtime-return n = _ , _ , _ , refl

higher-source-runtime : ℕ → Term 0
higher-source-runtime n =
  ((higher-identity ⦂∀ ho-body [ ‵ `ℕ ]) · (ƛ (` zero))) · $ (κℕ n)

higher-source-runtime-⊢ : ∀ n
  → ⟨ 0 , store-empty , [] ⟩ ⊢ higher-source-runtime n ⦂ ‵ `ℕ
higher-source-runtime-⊢ n =
  ⊢· (⊢· (⊢• higher-identity-⊢) (⊢ƛ (⊢` Z))) (⊢$ (κℕ n))

higher-source-runtime-return : ∀ n
  → Σ[ Δ′ ∈ ℕ ] Σ[ changes ∈ StoreChanges 0 Δ′ ]
    Σ[ trace ∈ higher-source-runtime n —↠[ changes ] $ (κℕ n) ]
      interpretFrom store-empty 16 (higher-source-runtime n)
        ≡ returned (E.result Δ′ changes ($ (κℕ n)) trace ($ (κℕ n)))
higher-source-runtime-return n = _ , _ , _ , refl

-- The complete data-observing programs, not just their operands, have CTI
-- derivations. CTI writes the precise program first and the imprecise one last.

constant-runtime² : ∀ n → W₀ ∣ []
  ⊢² constant-source-runtime n ⊑ constant-reveal-runtime n ∶ ι⊑ι
constant-runtime² n =
  CTI.•⊑•² nat∀⊑nat∀ (constant-reveal² n) ι⊑ι ι⊑ι

identity-reveal-runtime² : ∀ n → W₀ ∣ []
  ⊢² identity-source-runtime n ⊑ identity-reveal-runtime n ∶ ι⊑ι
identity-reveal-runtime² n = CTI.·⊑·²
  (CTI.•⊑•² id∀⊑id∀ identity-reveal² ι⊑ι (⇒⊑⇒ ι⊑ι ι⊑ι))
  (CTI.κ⊑κ² (κℕ n) ι⊑ι)

identity-conceal-runtime² : ∀ n → W₀ ∣ []
  ⊢² identity-source-runtime n ⊑ identity-conceal-runtime n ∶ ι⊑ι
identity-conceal-runtime² n = CTI.·⊑·²
  (CTI.•⊑•² id∀⊑id∀ identity-conceal² ι⊑ι (⇒⊑⇒ ι⊑ι ι⊑ι))
  (CTI.κ⊑κ² (κℕ n) ι⊑ι)

identity-mixed-runtime² : ∀ n → W₀ ∣ []
  ⊢² identity-source-runtime n ⊑ identity-mixed-runtime n ∶ ι⊑ι
identity-mixed-runtime² n = CTI.·⊑·²
  (CTI.•⊑•² id∀⊑id∀ identity-mixed² ι⊑ι (⇒⊑⇒ ι⊑ι ι⊑ι))
  (CTI.κ⊑κ² (κℕ n) ι⊑ι)

higher-runtime² : ∀ n → W₀ ∣ []
  ⊢² higher-source-runtime n ⊑ higher-runtime n ∶ ι⊑ι
higher-runtime² n = CTI.·⊑·²
  (CTI.·⊑·² (CTI.•⊑•² ho∀⊑ho∀ higher-identity-reveal² ι⊑ι
      (⇒⊑⇒ (⇒⊑⇒ ι⊑ι ι⊑ι) (⇒⊑⇒ ι⊑ι ι⊑ι)))
    (CTI.ƛ⊑ƛ² (CTI.x⊑x² CTX.Zʷ)))
  (CTI.κ⊑κ² (κℕ n) ι⊑ι)
