module proof.ImprecisionComposition where

-- File Charter:
--   * Proves transitivity of type imprecision under a fixed imprecision
--     environment.
--   * Handles structural, instantiating, dynamic, bottom universal, and
--     alias cases.
--   * The alias case recurses through `imp-env-weaken` and a shift
--     renaming, which the syntactic termination checker cannot follow;
--     the induction is therefore well-founded on the sum of the two
--     derivation sizes, using the exact size preservation of both
--     transports.

open import Data.Empty using (⊥-elim)
open import Data.Fin using (suc)
open import Data.Nat as Nat using (ℕ; _+_; _<_; _≤_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties
  using (≤-refl; +-suc; +-mono-≤; m≤m+n; m≤n+m; n<1+n;
         m≤n⇒m≤1+n)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (fromWitnessFalse)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; subst; sym)

open import Types
open import Imprecision
open import proof.Imprecision
  using (imprecision-to-fresh; ext-aliases-avoid-zero)
open import proof.ImprecisionConsistency using
  ( ext-to-inst-star-map
  ; ext-to-inst-alias-map
  ; shift-star-map
  ; shift-alias-map
  ; fin-suc-injective
  ; imp-env-weaken
  ; rename-⊑
  ; source-nonvar-from-target
  ; target-occurs-source
  ; universal-right-to-star
  ; sizeI
  ; sizeI-weaken
  ; sizeI-rename
  )


source-nonstar-from-target : ∀ {Δ} {μ : ImpEnv Δ} {A B : Ty Δ}
  → μ ⊢ A ⊑ B
  → NonStar B
  → NonStar A
source-nonstar-from-target ★⊑★ ()
source-nonstar-from-target ι⊑ι nonstar-ι = nonstar-ι
source-nonstar-from-target X⊑X nonstar-X = nonstar-X
source-nonstar-from-target (⇒⊑⇒ p q) nonstar-⇒ = nonstar-⇒
source-nonstar-from-target (∀⊑∀ p) nonstar-∀ = nonstar-∀
source-nonstar-from-target (⇒⊑★ p q) ()
source-nonstar-from-target ι⊑★ ()
source-nonstar-from-target (X⊑★ eq) ()
source-nonstar-from-target (∀⊑ Anv zero∈A p) Bns = nonstar-∀
source-nonstar-from-target ∀★⊑★ ()
source-nonstar-from-target (∀⊑★ Ans p) ()
source-nonstar-from-target bot-elim nonstar-∀ = nonstar-∀
source-nonstar-from-target bot⊑★ ()
source-nonstar-from-target (alias eq p) Bns = nonstar-X

-- Rebuild an alias conclusion after composing its premise, unless the
-- target collapsed onto the alias variable itself, in which case the
-- reflexive leaf applies.

alias-rebuild : ∀ {Δ} {μ : ImpEnv Δ} {X : TyVar Δ}
    {T C : Ty Δ}
  → Dec (C ≡ (＇ X))
  → μ X ≡ X⊑ᵗ T
  → μ ⊢ T ⊑ C
  → μ ⊢ ＇ X ⊑ C
alias-rebuild (yes C≡X) eq T⊑C =
  subst (λ R → _ ⊢ ＇ _ ⊑ R) (sym C≡X) X⊑X
alias-rebuild (no C≢X) eq T⊑C =
  alias eq {notSelf = fromWitnessFalse C≢X} T⊑C

-- Arithmetic for the size measure.

private

  sum-lt : ∀ {pa pb qa qb : ℕ}
    → pa ≤ pb
    → qa ≤ qb
    → pa + qa < Nat.suc pb + Nat.suc qb
  sum-lt {pa} {pb} {qa} {qb} h₁ h₂ =
    Nat.s≤s
      (subst (pa + qa ≤_) (sym (+-suc pb qb))
        (m≤n⇒m≤1+n (+-mono-≤ h₁ h₂)))

  lt-by : ∀ {a pa b qa : ℕ}
    → a ≡ pa
    → b ≡ qa
    → ∀ {pb qb : ℕ}
    → pa ≤ pb
    → qa ≤ qb
    → a + b < Nat.suc pb + Nat.suc qb
  lt-by refl refl = sum-lt

  peel-lt : ∀ {a b b′ : ℕ}
    → b ≡ b′
    → a + b < Nat.suc (a + b′)
  peel-lt refl = n<1+n _

  go : ∀ {Δ} {μ : ImpEnv Δ} {A B C : Ty Δ}
    → (p : μ ⊢ A ⊑ B)
    → (q : μ ⊢ B ⊑ C)
    → Acc _<_ (sizeI p + sizeI q)
    → μ ⊢ A ⊑ C
  go ★⊑★ ★⊑★ wf = ★⊑★
  go ι⊑ι ι⊑ι wf = ι⊑ι
  go ι⊑ι ι⊑★ wf = ι⊑★
  go X⊑X X⊑X wf = X⊑X
  go X⊑X (X⊑★ eq) wf = X⊑★ eq
  go X⊑X (alias eq {notSelf} q) wf =
    alias eq {notSelf = notSelf} q
  go (⇒⊑⇒ p₁ p₂) (⇒⊑⇒ q₁ q₂) (acc rec) =
    ⇒⊑⇒
      (go p₁ q₁
        (rec (sum-lt (m≤m+n (sizeI p₁) (sizeI p₂))
          (m≤m+n (sizeI q₁) (sizeI q₂)))))
      (go p₂ q₂
        (rec (sum-lt (m≤n+m (sizeI p₂) (sizeI p₁))
          (m≤n+m (sizeI q₂) (sizeI q₁)))))
  go (⇒⊑⇒ p₁ p₂) (⇒⊑★ q₁ q₂) (acc rec) =
    ⇒⊑★
      (go p₁ q₁
        (rec (sum-lt (m≤m+n (sizeI p₁) (sizeI p₂))
          (m≤m+n (sizeI q₁) (sizeI q₂)))))
      (go p₂ q₂
        (rec (sum-lt (m≤n+m (sizeI p₂) (sizeI p₁))
          (m≤n+m (sizeI q₂) (sizeI q₁)))))
  go (∀⊑∀ p) (∀⊑∀ q) (acc rec) =
    ∀⊑∀ (go p q (rec (sum-lt ≤-refl ≤-refl)))
  go (∀⊑∀ p) (∀⊑ Bnv zero∈B q) (acc rec) =
    ∀⊑
      (source-nonvar-from-target (ext-aliases-avoid-zero _)
        p Bnv zero∈B)
      (target-occurs-source (ext-aliases-avoid-zero _) p zero∈B)
      (go
        (imp-env-weaken ext-to-inst-star-map
          ext-to-inst-alias-map p)
        q
        (rec
          (lt-by
            (sizeI-weaken ext-to-inst-star-map
              ext-to-inst-alias-map p)
            refl ≤-refl ≤-refl)))
  go (∀⊑∀ p) ∀★⊑★ wf = universal-right-to-star (∀⊑∀ p)
  go (∀⊑∀ p) (∀⊑★ Bns q) (acc rec) =
    ∀⊑★ (source-nonstar-from-target p Bns)
      (go p q (rec (sum-lt ≤-refl ≤-refl)))
  go (∀⊑∀ p) bot-elim wf =
    subst (λ T → _ ⊢ `∀ T ⊑ `∀ ★)
      (sym (imprecision-to-fresh (ext-aliases-avoid-zero _) p))
      bot-elim
  go (∀⊑∀ p) bot⊑★ wf =
    subst (λ T → _ ⊢ `∀ T ⊑ ★)
      (sym (imprecision-to-fresh (ext-aliases-avoid-zero _) p))
      bot⊑★
  go (⇒⊑★ p q) ★⊑★ wf = ⇒⊑★ p q
  go ι⊑★ ★⊑★ wf = ι⊑★
  go (X⊑★ eq) ★⊑★ wf = X⊑★ eq
  go {μ = μ} (∀⊑ Anv zero∈A p) q (acc rec) =
    ∀⊑ Anv zero∈A
      (go p
        (rename-⊑ {μ′ = instᵐ μ} suc fin-suc-injective
          (shift-star-map {ν = μ} {v = X⊑★})
          (shift-alias-map {ν = μ} {v = X⊑★}) q)
        (rec
          (peel-lt
            (sizeI-rename (instᵐ μ) suc fin-suc-injective
              (shift-star-map {ν = μ} {v = X⊑★})
              (shift-alias-map {ν = μ} {v = X⊑★}) q))))
  go ∀★⊑★ ★⊑★ wf = ∀★⊑★
  go (∀⊑★ Ans p) ★⊑★ wf = ∀⊑★ Ans p
  go bot-elim (∀⊑∀ ★⊑★) wf = bot-elim
  go bot-elim ∀★⊑★ wf = bot⊑★
  go bot⊑★ ★⊑★ wf = bot⊑★
  go {C = C} (alias {X = X} eq p) q (acc rec) =
    alias-rebuild (isVar? X C) eq
      (go p q (rec (n<1+n _)))

⊑-trans : ∀ {Δ} {μ : ImpEnv Δ} {A B C : Ty Δ}
  → μ ⊢ A ⊑ B
  → μ ⊢ B ⊑ C
  → μ ⊢ A ⊑ C
⊑-trans p q = go p q (<-wellFounded (sizeI p + sizeI q))
