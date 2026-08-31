module proof.LR-narrow.IntegratedData where

-- File Charter:
--   * Data-only dynamic semantic type for the integrated world-indexed model.
--   * Admits only natural data and nominal packets carrying natural payloads
--     through finite seal chains, including alias chains such as `Y ↦ X ↦ ℕ`.
--   * Supports arbitrary ground-injection environments on the dynamic
--     boundary and proves value, typing, index, and future closure.
--   * No function, universal, or dynamic-in-dynamic payloads are claimed.

open import Data.List using ([])
open import Data.Nat using (ℕ; _≤_)
open import Data.Product using (_,_; ∃-syntax)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans)
  renaming (subst to subst≡)

open import Types
open import TyStore
open import CastTerms
open import Conversion
open import Primitives using (κℕ)
open import LR-narrow.LogicalRelation using (groundInjection)
open import proof.Consistency as PC using (renameGroundᵐ; rename∼★ᵐ)
open import proof.TypeInTermSubst using (toRename-wk-eq; renameᵗ-wk-eq)
open import proof.LR-narrow.Closure using (rename-ground-injection)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.IntegratedModel
import proof.LR-narrow.IntegratedWorld as IW
import Consistency as C

module Unary {Δ0} (Σ0 : TyStore Δ0) where

  data NaturalPayload : ∀ {Δ}
      (S : PhysicalScope Σ0 Δ) → Ty Δ → ℕ → Term Δ → Set where
    payload-natural : ∀ {Δ} {S : PhysicalScope Σ0 Δ} {n}
      → NaturalPayload S (‵ `ℕ) n ($ (κℕ n))

    payload-seal : ∀ {Δ} {S : PhysicalScope Σ0 Δ} {n X R M}
      → scopeStore S ∋ X ⦂ R
      → NaturalPayload S R n M
      → NaturalPayload S (＇ X) n (M ↓ seal X R)

  payload-ground : ∀ {Δ} {S : PhysicalScope Σ0 Δ} {A n M}
    → NaturalPayload S A n M → Ground A
  payload-ground payload-natural = ‵ `ℕ
  payload-ground (payload-seal {X = X} entry p) = ＇ X

  payload-value : ∀ {Δ} {S : PhysicalScope Σ0 Δ} {A n M}
    → NaturalPayload S A n M → Value M
  payload-value payload-natural = $ _
  payload-value (payload-seal entry p) = payload-value p ↓ seal

  payload-typed : ∀ {Δ} {S : PhysicalScope Σ0 Δ} {A n M}
    → NaturalPayload S A n M
    → ⟨ Δ , scopeStore S , [] ⟩ ⊢ M ⦂ A
  payload-typed payload-natural = ⊢$ (κℕ _)
  payload-typed (payload-seal entry p) =
    ⊢conceal (⊢↓-seal entry) (payload-typed p)

  private
    weaken-entry : ∀ {Δ} {S : PhysicalScope Σ0 Δ} {X R B}
      → scopeStore S ∋ X ⦂ R
      → scopeStore (allocate S B) ∋ C.toRenameᵗ C.wk↪ᵗ X
          ⦂ renameᵗ (C.toRenameᵗ C.wk↪ᵗ) R
    weaken-entry {X = X} {R = R} entry
        rewrite toRename-wk-eq X | renameᵗ-wk-eq R = S-bind∋ entry refl

  payload-weaken : ∀ {Δ} {S : PhysicalScope Σ0 Δ} {A n M B}
    → NaturalPayload S A n M
    → NaturalPayload (allocate S B)
        (renameᵗ (C.toRenameᵗ C.wk↪ᵗ) A) n (⇑ᵗᵐ M)
  payload-weaken payload-natural = payload-natural
  payload-weaken (payload-seal entry p) =
    payload-seal (weaken-entry entry) (payload-weaken p)

  payload-weaken-ground : ∀ {Δ} {S : PhysicalScope Σ0 Δ} {A n M B}
      (p : NaturalPayload S A n M)
    → payload-ground (payload-weaken {B = B} p)
        ≡ renameGroundᵐ C.wk↪ᵗ (payload-ground p)
  payload-weaken-ground payload-natural = refl
  payload-weaken-ground (payload-seal entry p) = refl

  payload-lift : ∀ {Δ} {S : PhysicalScope Σ0 Δ} {A n M B}
    → NaturalPayload S A n M
    → NaturalPayload (allocate S B) (⇑ᵗ A) n (⇑ᵗᵐ M)
  payload-lift {S = S} {A = A} {n} {M} {B} p =
    subst≡ (λ A′ → NaturalPayload (allocate S B) A′ n (⇑ᵗᵐ M))
      (renameᵗ-wk-eq A) (payload-weaken p)

  scope-star : ∀ {Δ} (S : PhysicalScope Σ0 Δ) → scopeTy S ★ ≡ ★
  scope-star root = refl
  scope-star (allocate S A) = cong ⇑ᵗ (scope-star S)

  lift-natural : ∀ {Δ Δ′} {S : PhysicalScope Σ0 Δ}
      {T : PhysicalScope Σ0 Δ′} (p : ScopeFuture S T)
    → liftTy p (‵ `ℕ) ≡ ‵ `ℕ
  lift-natural stay = refl
  lift-natural (grow p) = lift-natural p

  lift-variable : ∀ {Δ Δ′} {S : PhysicalScope Σ0 Δ}
      {T : PhysicalScope Σ0 Δ′} (p : ScopeFuture S T) X
    → liftTy p (＇ X) ≡ ＇ liftVar p X
  lift-variable stay X = refl
  lift-variable (grow p) X = lift-variable p (Fin.suc X)

  payload-future : ∀ {Δ Δ′} {S : PhysicalScope Σ0 Δ}
      {T : PhysicalScope Σ0 Δ′} {A n M}
    → (p : ScopeFuture S T)
    → NaturalPayload S A n M
    → NaturalPayload T (liftTy p A) n (liftTerm p M)
  payload-future stay pl = pl
  payload-future (grow p) pl = payload-future p (payload-lift pl)

  futureEnv : ∀ {Δ Δ′} {S : PhysicalScope Σ0 Δ}
      {T : PhysicalScope Σ0 Δ′}
    → ScopeFuture S T → C.Env∼ Δ → C.Env∼ Δ′
  futureEnv stay μ = μ
  futureEnv (grow p) μ = futureEnv p (C.renameEnv∼ C.wk↪ᵗ μ)

  future-star : ∀ {Δ Δ′} {S : PhysicalScope Σ0 Δ}
      {T : PhysicalScope Σ0 Δ′} {μ : C.Env∼ Δ} {A : Ty Δ}
    → (p : ScopeFuture S T) → μ C.⊢ A ∼★
    → futureEnv p μ C.⊢ liftTy p A ∼★
  future-star stay c = c
  future-star {A = A} (grow p) c = future-star p
    (subst≡ (λ B → C.renameEnv∼ C.wk↪ᵗ _ C.⊢ B ∼★)
      (renameᵗ-wk-eq A) (rename∼★ᵐ C.wk↪ᵗ c))

  record GroundPacket {Δ} (S : PhysicalScope Σ0 Δ)
      (A : Ty Δ) (n : ℕ) (M : Term Δ) : Set where
    constructor ground-packet
    field
      μ : C.Env∼ Δ
      payload : Term Δ
      payload-shape : NaturalPayload S A n payload
      A∼★ : μ C.⊢ A ∼★
      exact :
        M ≡ payload ⟨ groundInjection (payload-ground payload-shape) A∼★ ⟩

  open GroundPacket public

  NaturalPacket : ∀ {Δ}
    → (S : PhysicalScope Σ0 Δ) → ℕ → Term Δ → Set
  NaturalPacket S n M = GroundPacket S (‵ `ℕ) n M

  NominalPacket : ∀ {Δ}
    → (S : PhysicalScope Σ0 Δ) → TyVar Δ → ℕ → Term Δ → Set
  NominalPacket S X n M = GroundPacket S (＇ X) n M

  packet-value : ∀ {Δ} {S : PhysicalScope Σ0 Δ} {A n M}
    → GroundPacket S A n M → Value M
  packet-value gp =
    subst≡ Value (sym (exact gp))
      (payload-value (payload-shape gp) 《 inj
        ⦃ Gᵍ = payload-ground (payload-shape gp) ⦄
        ⦃ G∼★ = A∼★ gp ⦄
        ⦃ Gns = C.ground-nonstar (payload-ground (payload-shape gp)) ⦄ 》)

  packet-typed : ∀ {Δ} {S : PhysicalScope Σ0 Δ} {A n M}
    → GroundPacket S A n M
    → ⟨ Δ , scopeStore S , [] ⟩ ⊢ M ⦂ ★
  packet-typed {S = S} gp =
    subst≡ (λ N → ⟨ _ , scopeStore S , [] ⟩ ⊢ N ⦂ ★)
      (sym (exact gp))
      (⊢⟨⟩ (payload-typed (payload-shape gp))
        (groundInjection (payload-ground (payload-shape gp)) (A∼★ gp)))

  packet-weaken : ∀ {Δ} {S : PhysicalScope Σ0 Δ} {A n M B}
    → GroundPacket S A n M
    → GroundPacket (allocate S B)
        (renameᵗ (C.toRenameᵗ C.wk↪ᵗ) A) n (⇑ᵗᵐ M)
  packet-weaken gp = ground-packet
    (C.renameEnv∼ C.wk↪ᵗ (μ gp)) (⇑ᵗᵐ (payload gp))
    (payload-weaken (payload-shape gp)) (rename∼★ᵐ C.wk↪ᵗ (A∼★ gp))
    (trans (cong ⇑ᵗᵐ (exact gp))
      (trans (cong (λ c → ⇑ᵗᵐ (payload gp) ⟨ c ⟩)
        (rename-ground-injection (payload-ground (payload-shape gp)) (A∼★ gp)))
        (cong (λ g → ⇑ᵗᵐ (payload gp)
            ⟨ groundInjection g (rename∼★ᵐ C.wk↪ᵗ (A∼★ gp)) ⟩)
          (sym (payload-weaken-ground (payload-shape gp))))))

  packet-lift : ∀ {Δ} {S : PhysicalScope Σ0 Δ} {A n M B}
    → GroundPacket S A n M
    → GroundPacket (allocate S B) (⇑ᵗ A) n (⇑ᵗᵐ M)
  packet-lift {S = S} {A = A} {n} {M} {B} gp =
    subst≡ (λ A′ → GroundPacket (allocate S B) A′ n (⇑ᵗᵐ M))
      (renameᵗ-wk-eq A) (packet-weaken gp)

  packet-future : ∀ {Δ Δ′} {S : PhysicalScope Σ0 Δ}
      {T : PhysicalScope Σ0 Δ′} {A n M}
    → (p : ScopeFuture S T)
    → GroundPacket S A n M
    → GroundPacket T (liftTy p A) n (liftTerm p M)
  packet-future stay gp = gp
  packet-future (grow p) gp = packet-future p (packet-lift gp)

module Data {ΔI0 ΔP0} (ΣI0 : TyStore ΔI0) (ΣP0 : TyStore ΔP0) where

  module Worlds = IW.Worlds ΣI0 ΣP0
  open Worlds
  open Model ΣI0 ΣP0
  module I = Unary ΣI0
  module P = Unary ΣP0

  data DynamicValues : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
      {T : PhysicalScope ΣP0 ΔP}
    → World S T → ℕ → Term ΔI → Term ΔP → Set where

    same-natural-tagged : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
        {T : PhysicalScope ΣP0 ΔP} {W : World S T} {k n M N}
      → I.NaturalPacket S n M → P.NaturalPacket T n N
      → DynamicValues W k M N

    matched-name-tagged : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
        {T : PhysicalScope ΣP0 ΔP} {W : World S T} {k n X Y M N}
      → Matched W X Y
      → I.NominalPacket S X n M
      → P.NominalPacket T Y n N
      → DynamicValues W k M N

    precise-only-tagged : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
        {T : PhysicalScope ΣP0 ΔP} {W : World S T} {k n Y M N}
      → PreciseOnly W Y
      → I.NaturalPacket S n M
      → P.NominalPacket T Y n N
      → DynamicValues W k M N

  dynamic-valueI : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
      {T : PhysicalScope ΣP0 ΔP} {W : World S T} {k U V}
    → DynamicValues W k U V → Value U
  dynamic-valueI (same-natural-tagged p q) = I.packet-value p
  dynamic-valueI (matched-name-tagged m p q) = I.packet-value p
  dynamic-valueI (precise-only-tagged o p q) = I.packet-value p

  dynamic-valueP : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
      {T : PhysicalScope ΣP0 ΔP} {W : World S T} {k U V}
    → DynamicValues W k U V → Value V
  dynamic-valueP (same-natural-tagged p q) = P.packet-value q
  dynamic-valueP (matched-name-tagged m p q) = P.packet-value q
  dynamic-valueP (precise-only-tagged o p q) = P.packet-value q

  dynamic-typedI : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
      {T : PhysicalScope ΣP0 ΔP} {W : World S T} {k U V}
    → DynamicValues W k U V
    → ⟨ ΔI , scopeStore S , [] ⟩ ⊢ U ⦂ ★
  dynamic-typedI (same-natural-tagged p q) = I.packet-typed p
  dynamic-typedI (matched-name-tagged m p q) = I.packet-typed p
  dynamic-typedI (precise-only-tagged o p q) = I.packet-typed p

  dynamic-typedP : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
      {T : PhysicalScope ΣP0 ΔP} {W : World S T} {k U V}
    → DynamicValues W k U V
    → ⟨ ΔP , scopeStore T , [] ⟩ ⊢ V ⦂ ★
  dynamic-typedP (same-natural-tagged p q) = P.packet-typed q
  dynamic-typedP (matched-name-tagged m p q) = P.packet-typed q
  dynamic-typedP (precise-only-tagged o p q) = P.packet-typed q

  dynamic-downward : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
      {T : PhysicalScope ΣP0 ΔP} {W : World S T} {j k U V}
    → j ≤ k → DynamicValues W k U V → DynamicValues W j U V
  dynamic-downward j≤k (same-natural-tagged p q) = same-natural-tagged p q
  dynamic-downward j≤k (matched-name-tagged m p q) =
    matched-name-tagged m p q
  dynamic-downward j≤k (precise-only-tagged o p q) =
    precise-only-tagged o p q

  dynamic-future : ∀ {ΔI ΔP ΔI′ ΔP′}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {S′ : PhysicalScope ΣI0 ΔI′} {T′ : PhysicalScope ΣP0 ΔP′}
      {W : World S T} {W′ : World S′ T′} {k U V}
    → (p : ScopeFuture S S′) → (q : ScopeFuture T T′)
    → Future p q W W′ → DynamicValues W k U V
    → DynamicValues W′ k (liftTerm p U) (liftTerm q V)
  dynamic-future {S′ = S′} {T′ = T′} {U = U} {V = V} p q ext
      (same-natural-tagged {n = n} pI pP) = same-natural-tagged
    (subst≡ (λ A → I.GroundPacket S′ A n (liftTerm p U))
      (I.lift-natural p)
      (I.packet-future p pI))
    (subst≡ (λ A → P.GroundPacket T′ A n (liftTerm q V))
      (P.lift-natural q)
      (P.packet-future q pP))
  dynamic-future {S′ = S′} {T′ = T′} {U = U} {V = V} p q ext
      (matched-name-tagged {n = n} {X = X} {Y = Y} m pI pP) =
    matched-name-tagged (matched-future ext m)
      (subst≡ (λ A → I.GroundPacket S′ A n (liftTerm p U))
        (I.lift-variable p X)
        (I.packet-future p pI))
      (subst≡ (λ A → P.GroundPacket T′ A n (liftTerm q V))
        (P.lift-variable q Y)
        (P.packet-future q pP))
  dynamic-future {S′ = S′} {T′ = T′} {U = U} {V = V} p q ext
      (precise-only-tagged {n = n} {Y = Y} o pI pP) =
    precise-only-tagged (only-future ext o)
      (subst≡ (λ A → I.GroundPacket S′ A n (liftTerm p U))
        (I.lift-natural p)
        (I.packet-future p pI))
      (subst≡ (λ A → P.GroundPacket T′ A n (liftTerm q V))
        (P.lift-variable q Y)
        (P.packet-future q pP))

  dataDynamic : SemanticType
  dataDynamic = record
    { impreciseTy = ★
    ; preciseTy = ★
    ; related = DynamicValues
    ; imprecise-value = dynamic-valueI
    ; precise-value = dynamic-valueP
    ; imprecise-typed = λ { {S = S} r →
        subst≡ (λ A → ⟨ _ , scopeStore S , [] ⟩ ⊢ _ ⦂ A)
          (sym (I.scope-star S)) (dynamic-typedI r) }
    ; precise-typed = λ { {T = T} r →
        subst≡ (λ A → ⟨ _ , scopeStore T , [] ⟩ ⊢ _ ⦂ A)
          (sym (P.scope-star T)) (dynamic-typedP r) }
    ; downward = dynamic-downward
    ; future-closed = dynamic-future
    }
