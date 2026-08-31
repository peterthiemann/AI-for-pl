module proof.LR-narrow.GroundTagSteps where

-- File Charter:
--   * Operational ground-tag/projection steps without semantic LR premises.
--   * Extracted unchanged from Cast so both the live proof and experimental
--     model share the same evaluator facts without cast obligations.
--   * Covers successful/mismatching tags and exposes actual step equations.

open import Data.Empty using (⊥-elim)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _,_)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans)
open import Relation.Nullary using (yes; no)

open import Types
open import TyStore
open import CastTerms
open import Reduction
import Consistency as C
import Eval as E
open import LR-narrow.LogicalRelation using (groundInjection)
open import proof.LR-narrow.ImmediateReturn using (value-question-complete)
open import proof.LR-narrow.BetaExpansion using (value-step-none)

groundProjection : ∀ {Δ} {μ : C.Env∼ Δ} {G B : Ty Δ}
  → (g : Ground G)
  → μ C.⊢★∼ G
  → μ C.⊢ G ∼ B
  → NonStar B
  → μ C.⊢ ★ ∼ B
groundProjection g ★∼G G∼B Bns =
  let instance
        ground-instance = g
        star-to-ground-instance = ★∼G
        target-nonstar-instance = Bns
  in C.？ G∼B

projection-cast-value-none : ∀ {Δ} {V : Term Δ}
    {μ : C.Env∼ Δ} {G B : Ty Δ}
    (g : Ground G) (★∼G : μ C.⊢★∼ G)
    (c : μ C.⊢ G ∼ B) (Bns : NonStar B)
  → Value V
  → E.value? (V ⟨ groundProjection g ★∼G c Bns ⟩) ≡ nothing
projection-cast-value-none g ★∼G c Bns vV
    with value-question-complete vV
projection-cast-value-none g ★∼G c Bns vV | vV′ , value-eq
    rewrite value-eq = refl

identity-cast-value-none : ∀ {Δ} {V : Term Δ}
    {μ : C.Env∼ Δ} {A : Ty Δ} (a : Atom A)
  → Value V
  → E.value? (V ⟨ C.id {μ = μ} a ⟩) ≡ nothing
identity-cast-value-none a vV with value-question-complete vV
identity-cast-value-none a vV | vV′ , value-eq
    rewrite value-eq = refl

cast-redex-step-question : ∀ {Δ} {Σ : TyStore Δ}
    {V N : Term Δ} {μ : C.Env∼ Δ} {A B : Ty Δ}
    {c : μ C.⊢ A ∼ B} {step : V ⟨ c ⟩ —→ N}
  → Value V
  → E.cast-redex? V c ≡
      just (E.step-result keep N (pure-step step))
  → E.step? Σ (V ⟨ c ⟩) ≡
      just (E.step-result keep N (pure-step step))
cast-redex-step-question {Σ = Σ} {V = V} vV redex-eq
    with E.step? Σ V | value-step-none {Σ = Σ} vV
cast-redex-step-question vV redex-eq | nothing | refl = redex-eq
cast-redex-step-question vV redex-eq | just step | ()

step-question-value-none : ∀ {Δ} {Σ : TyStore Δ}
    {M : Term Δ} {step : E.Step M}
  → E.step? Σ M ≡ just step
  → E.value? M ≡ nothing
step-question-value-none {Σ = Σ} {M = M} step-eq
    with E.value? M
step-question-value-none step-eq | nothing = refl
step-question-value-none {Σ = Σ} step-eq | just vM
    with value-step-none {Σ = Σ} vM
step-question-value-none step-eq | just vM | value-step-eq
    with trans (sym value-step-eq) step-eq
step-question-value-none step-eq | just vM | value-step-eq | ()

data TagProjectionStepView {Δ : TyCtx} (Σ : TyStore Δ)
    {U : Term Δ} {μ ν : C.Env∼ Δ} {H G : Ty Δ}
    (h : Ground H) (g : Ground G)
    (H∼★ : μ C.⊢ H ∼★) (★∼G : ν C.⊢★∼ G)
    (vU : Value U) : Set where
  tag-matched : H ≡ G
    → (step :
      ((U ⟨ groundInjection h H∼★ ⟩)
        ⟨ groundProjection g ★∼G (C.idᵍ g)
          (C.ground-nonstar g) ⟩) —→ U)
    → E.step? Σ
        ((U ⟨ groundInjection h H∼★ ⟩)
          ⟨ groundProjection g ★∼G (C.idᵍ g)
            (C.ground-nonstar g) ⟩) ≡
        just (E.step-result keep U (pure-step step))
    → TagProjectionStepView Σ h g H∼★ ★∼G vU

  tag-mismatched : H ≢ G
    → (step :
      ((U ⟨ groundInjection h H∼★ ⟩)
        ⟨ groundProjection g ★∼G (C.idᵍ g)
          (C.ground-nonstar g) ⟩) —→ blame)
    → E.step? Σ
        ((U ⟨ groundInjection h H∼★ ⟩)
          ⟨ groundProjection g ★∼G (C.idᵍ g)
            (C.ground-nonstar g) ⟩) ≡
        just (E.step-result keep blame (pure-step step))
    → TagProjectionStepView Σ h g H∼★ ★∼G vU

tag-matched-redex-question : ∀ {Δ} {U : Term Δ}
    {μ ν : C.Env∼ Δ} {H : Ty Δ}
    (h : Ground H) (H∼★ : μ C.⊢ H ∼★) (★∼H : ν C.⊢★∼ H)
  → Value U
  → Σ[ vU′ ∈ Value U ]
      E.cast-redex? (U ⟨ groundInjection h H∼★ ⟩)
        (groundProjection h ★∼H (C.idᵍ h)
          (C.ground-nonstar h)) ≡
        just (E.step-result keep U
          (pure-step (tag-untag ⦃ Gᵍ = h ⦄ ⦃ G∼★ = H∼★ ⦄
            ⦃ ★∼G = ★∼H ⦄ ⦃ Gns = C.ground-nonstar h ⦄ vU′)))
tag-matched-redex-question {U = U} (＇ X) H∼★ ★∼H vU
    with value-question-complete vU | X Fin.≟ X in X-eq
tag-matched-redex-question (＇ X) H∼★ ★∼H vU
    | vU′ , value-eq | yes refl
    rewrite value-eq | X-eq = vU′ , refl
tag-matched-redex-question (＇ X) H∼★ ★∼H vU
    | vU′ , value-eq | no X≢X = ⊥-elim (X≢X refl)
tag-matched-redex-question {U = U} (‵ ι) H∼★ ★∼H vU
    with value-question-complete vU | ι ≟Base ι in ι-eq
tag-matched-redex-question (‵ ι) H∼★ ★∼H vU
    | vU′ , value-eq | yes refl
    rewrite value-eq | ι-eq = vU′ , refl
tag-matched-redex-question (‵ ι) H∼★ ★∼H vU
    | vU′ , value-eq | no ι≢ι = ⊥-elim (ι≢ι refl)
tag-matched-redex-question {U = U} ★⇒★ H∼★ ★∼H vU
    with value-question-complete vU
tag-matched-redex-question ★⇒★ H∼★ ★∼H vU
    | vU′ , value-eq
    rewrite value-eq = vU′ , refl
tag-matched-redex-question {U = U} ∀★ H∼★ ★∼H vU
    with value-question-complete vU
tag-matched-redex-question ∀★ H∼★ ★∼H vU
    | vU′ , value-eq
    rewrite value-eq = vU′ , refl

tag-mismatched-redex-question : ∀ {Δ} {U : Term Δ}
    {μ ν : C.Env∼ Δ} {H G : Ty Δ}
    (h : Ground H) (g : Ground G)
    (H∼★ : μ C.⊢ H ∼★) (★∼G : ν C.⊢★∼ G)
    (vU : Value U)
  → H ≢ G
  → Σ[ H≢G′ ∈ H ≢ G ] Σ[ vU′ ∈ Value U ]
      E.cast-redex? (U ⟨ groundInjection h H∼★ ⟩)
        (groundProjection g ★∼G (C.idᵍ g)
          (C.ground-nonstar g)) ≡
        just (E.step-result keep blame
          (pure-step (tag-untag-bad ⦃ Gᵍ = h ⦄ ⦃ Hᵍ = g ⦄
            ⦃ G∼★ = H∼★ ⦄ ⦃ ★∼H = ★∼G ⦄
            ⦃ Gns = C.ground-nonstar h ⦄
            ⦃ Hns = C.ground-nonstar g ⦄ vU′ H≢G′)))
tag-mismatched-redex-question {U = U} {H = H} h (＇ X)
    H∼★ ★∼G vU H≢G
    with value-question-complete
      (vU 《 inj ⦃ Gᵍ = h ⦄ ⦃ G∼★ = H∼★ ⦄
        ⦃ Gns = C.ground-nonstar h ⦄ 》)
       | H ≟Ty ＇ X in type-eq
tag-mismatched-redex-question h (＇ X) H∼★ ★∼G vU H≢G
    | (vU′ 《 inj 》) , value-eq | yes H≡G = ⊥-elim (H≢G H≡G)
tag-mismatched-redex-question h (＇ X) H∼★ ★∼G vU H≢G
    | (vU′ 《 inj 》) , value-eq | no H≢G′
    rewrite value-eq | type-eq = H≢G′ , vU′ , refl
tag-mismatched-redex-question {U = U} {H = H} h (‵ ι)
    H∼★ ★∼G vU H≢G
    with value-question-complete
      (vU 《 inj ⦃ Gᵍ = h ⦄ ⦃ G∼★ = H∼★ ⦄
        ⦃ Gns = C.ground-nonstar h ⦄ 》)
       | H ≟Ty ‵ ι in type-eq
tag-mismatched-redex-question h (‵ ι) H∼★ ★∼G vU H≢G
    | (vU′ 《 inj 》) , value-eq | yes H≡G = ⊥-elim (H≢G H≡G)
tag-mismatched-redex-question h (‵ ι) H∼★ ★∼G vU H≢G
    | (vU′ 《 inj 》) , value-eq | no H≢G′
    rewrite value-eq | type-eq = H≢G′ , vU′ , refl
tag-mismatched-redex-question {U = U} {H = H} h ★⇒★
    H∼★ ★∼G vU H≢G
    with value-question-complete
      (vU 《 inj ⦃ Gᵍ = h ⦄ ⦃ G∼★ = H∼★ ⦄
        ⦃ Gns = C.ground-nonstar h ⦄ 》)
       | H ≟Ty (★ ⇒ ★) in type-eq
tag-mismatched-redex-question h ★⇒★ H∼★ ★∼G vU H≢G
    | (vU′ 《 inj 》) , value-eq | yes H≡G = ⊥-elim (H≢G H≡G)
tag-mismatched-redex-question h ★⇒★ H∼★ ★∼G vU H≢G
    | (vU′ 《 inj 》) , value-eq | no H≢G′
    rewrite value-eq | type-eq = H≢G′ , vU′ , refl
tag-mismatched-redex-question {U = U} {H = H} h ∀★
    H∼★ ★∼G vU H≢G
    with value-question-complete
      (vU 《 inj ⦃ Gᵍ = h ⦄ ⦃ G∼★ = H∼★ ⦄
        ⦃ Gns = C.ground-nonstar h ⦄ 》)
       | H ≟Ty (`∀ ★) in type-eq
tag-mismatched-redex-question h ∀★ H∼★ ★∼G vU H≢G
    | (vU′ 《 inj 》) , value-eq | yes H≡G = ⊥-elim (H≢G H≡G)
tag-mismatched-redex-question h ∀★ H∼★ ★∼G vU H≢G
    | (vU′ 《 inj 》) , value-eq | no H≢G′
    rewrite value-eq | type-eq = H≢G′ , vU′ , refl

tag-projection-step-view : ∀ {Δ} {Σ : TyStore Δ}
    {U : Term Δ} {μ ν : C.Env∼ Δ} {H G : Ty Δ}
    (h : Ground H) (g : Ground G)
    (H∼★ : μ C.⊢ H ∼★) (★∼G : ν C.⊢★∼ G)
    (vU : Value U)
  → TagProjectionStepView Σ h g H∼★ ★∼G vU
tag-projection-step-view {Σ = Σ} {U = U} {H = H} {G = G}
    h g H∼★ ★∼G vU with H ≟Ty G
tag-projection-step-view {Σ = Σ} {U = U} {H = H} {G = .H}
    h g H∼★ ★∼G vU | yes refl
    rewrite ground-unique g h
    with tag-matched-redex-question h H∼★ ★∼G vU
tag-projection-step-view {Σ = Σ} {U = U} {H = H} {G = .H}
    h g H∼★ ★∼G vU | yes refl | vU′ , redex-eq =
  tag-matched refl
    (tag-untag ⦃ Gᵍ = h ⦄ ⦃ G∼★ = H∼★ ⦄
      ⦃ ★∼G = ★∼G ⦄ ⦃ Gns = C.ground-nonstar h ⦄ vU′)
    (cast-redex-step-question {Σ = Σ}
      (vU′ 《 inj ⦃ Gᵍ = h ⦄ ⦃ G∼★ = H∼★ ⦄
        ⦃ Gns = C.ground-nonstar h ⦄ 》) redex-eq)
tag-projection-step-view {Σ = Σ} {U = U} {H = H} {G = G}
    h g H∼★ ★∼G vU | no H≢G
    with tag-mismatched-redex-question h g H∼★ ★∼G vU H≢G
tag-projection-step-view {Σ = Σ} {U = U} {H = H} {G = G}
    h g H∼★ ★∼G vU | no H≢G | H≢G′ , vU′ , redex-eq =
  tag-mismatched H≢G′
    (tag-untag-bad ⦃ Gᵍ = h ⦄ ⦃ Hᵍ = g ⦄
      ⦃ G∼★ = H∼★ ⦄ ⦃ ★∼H = ★∼G ⦄
      ⦃ Gns = C.ground-nonstar h ⦄
      ⦃ Hns = C.ground-nonstar g ⦄ vU′ H≢G′)
    (cast-redex-step-question {Σ = Σ}
      (vU′ 《 inj ⦃ Gᵍ = h ⦄ ⦃ G∼★ = H∼★ ⦄
        ⦃ Gns = C.ground-nonstar h ⦄ 》) redex-eq)
