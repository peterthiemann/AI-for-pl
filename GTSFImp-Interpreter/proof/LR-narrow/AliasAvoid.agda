module proof.LR-narrow.AliasAvoid where

-- File Charter:
--   * Derivation-restricted alias avoidance (Finding H of
--     REPLACEMENT-CLOSURE-DESIGN.md): a center variable avoids the
--     representatives of exactly the alias leaves USED by a
--     derivation.  Unlike environment-level avoidance this survives
--     lifting to arbitrary future worlds, because lifting a
--     derivation creates no new alias leaves.
--   * Transport lemmas: between derivations of one judgment (leaves
--     are a function of the judgment, by uniqueness), along
--     renamings, and from alias-free environments.
--   * The derivation-restricted occurrence transfer
--     (target-occurs-source with avoidance read off the derivation).

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
  renaming (subst to subst≡)

open import Types
import Imprecision as I
import proof.Imprecision as PI
open import proof.ImprecisionConsistency using
  (rename-⊑; RenameAliasMap; NoAliases; ext-no-aliases;
   inst-no-aliases; shift-occurs; ext-injective;
   rename-star-map-ext; rename-star-map-inst;
   rename-alias-map-ext; rename-alias-map-inst)
open import proof.LR-narrow.StarNoOccurrence using (renameᵗ-∉ᵗ)

------------------------------------------------------------------------
-- The predicate
------------------------------------------------------------------------

AliasAvoidᵖ : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ}
  → TyVar Δ → I._⊢_⊑_ μ A B → Set
AliasAvoidᵖ c I.★⊑★ = ⊤
AliasAvoidᵖ c I.ι⊑ι = ⊤
AliasAvoidᵖ c I.X⊑X = ⊤
AliasAvoidᵖ c (I.⇒⊑⇒ p q) = AliasAvoidᵖ c p × AliasAvoidᵖ c q
AliasAvoidᵖ c (I.∀⊑∀ p) = AliasAvoidᵖ (Fin.suc c) p
AliasAvoidᵖ c (I.⇒⊑★ p q) = AliasAvoidᵖ c p × AliasAvoidᵖ c q
AliasAvoidᵖ c I.ι⊑★ = ⊤
AliasAvoidᵖ c (I.X⊑★ eq) = ⊤
AliasAvoidᵖ c (I.∀⊑ nonvar occurs p) = AliasAvoidᵖ (Fin.suc c) p
AliasAvoidᵖ c I.∀★⊑★ = ⊤
AliasAvoidᵖ c (I.∀⊑★ nonstar p) = AliasAvoidᵖ (Fin.suc c) p
AliasAvoidᵖ c I.bot-elim = ⊤
AliasAvoidᵖ c I.bot⊑★ = ⊤
AliasAvoidᵖ c (I.alias {T = T} eq p) =
  (c ∉ᵗ T) × AliasAvoidᵖ c p

------------------------------------------------------------------------
-- Transport between derivations of one judgment
------------------------------------------------------------------------

alias-avoid-unique : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ}
    {c : TyVar Δ}
    (p q : I._⊢_⊑_ μ A B)
  → AliasAvoidᵖ c p
  → AliasAvoidᵖ c q
alias-avoid-unique {c = c} p q avoid =
  subst≡ (AliasAvoidᵖ c) (PI.⊑-unique p q) avoid

------------------------------------------------------------------------
-- Transport along renamings
------------------------------------------------------------------------

alias-avoid-rename : ∀ {Δ Δ′} {μ : I.ImpEnv Δ}
    {μ′ : I.ImpEnv Δ′} {A B : Ty Δ} {c : TyVar Δ}
    (ρ : Δ ⇒ʳ Δ′)
    (injective : ∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
    (h : ∀ X → μ X ≡ I.X⊑★ → μ′ (ρ X) ≡ I.X⊑★)
    (ha : RenameAliasMap ρ μ μ′)
    (p : I._⊢_⊑_ μ A B)
  → AliasAvoidᵖ c p
  → AliasAvoidᵖ (ρ c)
      (rename-⊑ {μ = μ} {μ′ = μ′} ρ injective h ha p)
alias-avoid-rename ρ injective h ha I.★⊑★ avoid = tt
alias-avoid-rename ρ injective h ha I.ι⊑ι avoid = tt
alias-avoid-rename ρ injective h ha I.X⊑X avoid = tt
alias-avoid-rename {μ′ = μ′} ρ injective h ha (I.⇒⊑⇒ p q)
    (avoidᵖ , avoidᵍ) =
  alias-avoid-rename {μ′ = μ′} ρ injective h ha p avoidᵖ ,
  alias-avoid-rename {μ′ = μ′} ρ injective h ha q avoidᵍ
alias-avoid-rename {μ′ = μ′} ρ injective h ha (I.∀⊑∀ p) avoid =
  alias-avoid-rename {μ′ = I.extᵐ μ′} (extᵗ ρ)
    (ext-injective injective)
    (rename-star-map-ext ρ h) (rename-alias-map-ext ρ ha) p avoid
alias-avoid-rename {μ′ = μ′} ρ injective h ha (I.⇒⊑★ p q)
    (avoidᵖ , avoidᵍ) =
  alias-avoid-rename {μ′ = μ′} ρ injective h ha p avoidᵖ ,
  alias-avoid-rename {μ′ = μ′} ρ injective h ha q avoidᵍ
alias-avoid-rename ρ injective h ha I.ι⊑★ avoid = tt
alias-avoid-rename ρ injective h ha (I.X⊑★ eq) avoid = tt
alias-avoid-rename {μ′ = μ′} {c = c} ρ injective h ha
    (I.∀⊑ {A = A₀} {B = B₀} nonvar occurs p) avoid =
  alias-avoid-subst-right (renameᵗ-shift ρ B₀)
    (alias-avoid-rename {μ′ = I.instᵐ μ′} (extᵗ ρ)
      (ext-injective injective)
      (rename-star-map-inst ρ h) (rename-alias-map-inst ρ ha)
      p avoid)
  where
  alias-avoid-subst-right : ∀ {Δ} {μ : I.ImpEnv Δ}
      {A B B′ : Ty Δ} {c : TyVar Δ}
      (eq : B ≡ B′) {p : I._⊢_⊑_ μ A B}
    → AliasAvoidᵖ c p
    → AliasAvoidᵖ c
        (subst≡ (λ T → I._⊢_⊑_ μ A T) eq p)
  alias-avoid-subst-right refl avoid′ = avoid′
alias-avoid-rename ρ injective h ha I.∀★⊑★ avoid = tt
alias-avoid-rename {μ′ = μ′} ρ injective h ha
    (I.∀⊑★ nonstar p) avoid =
  alias-avoid-rename {μ′ = I.extᵐ μ′} (extᵗ ρ)
    (ext-injective injective)
    (rename-star-map-ext ρ h) (rename-alias-map-ext ρ ha) p avoid
alias-avoid-rename ρ injective h ha I.bot-elim avoid = tt
alias-avoid-rename ρ injective h ha I.bot⊑★ avoid = tt
alias-avoid-rename {μ′ = μ′} ρ injective h ha
    (I.alias {T = T} eq p)
    (c∉T , avoid) =
  renameᵗ-∉ᵗ ρ injective c∉T ,
  alias-avoid-rename {μ′ = μ′} ρ injective h ha p avoid

------------------------------------------------------------------------
-- Alias-free environments avoid everything
------------------------------------------------------------------------

no-aliases-avoidᵖ : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ}
    {c : TyVar Δ}
  → NoAliases μ
  → (p : I._⊢_⊑_ μ A B)
  → AliasAvoidᵖ c p
no-aliases-avoidᵖ na I.★⊑★ = tt
no-aliases-avoidᵖ na I.ι⊑ι = tt
no-aliases-avoidᵖ na I.X⊑X = tt
no-aliases-avoidᵖ na (I.⇒⊑⇒ p q) =
  no-aliases-avoidᵖ na p , no-aliases-avoidᵖ na q
no-aliases-avoidᵖ na (I.∀⊑∀ p) =
  no-aliases-avoidᵖ (ext-no-aliases na) p
no-aliases-avoidᵖ na (I.⇒⊑★ p q) =
  no-aliases-avoidᵖ na p , no-aliases-avoidᵖ na q
no-aliases-avoidᵖ na I.ι⊑★ = tt
no-aliases-avoidᵖ na (I.X⊑★ eq) = tt
no-aliases-avoidᵖ na (I.∀⊑ nonvar occurs p) =
  no-aliases-avoidᵖ (inst-no-aliases na) p
no-aliases-avoidᵖ na I.∀★⊑★ = tt
no-aliases-avoidᵖ na (I.∀⊑★ nonstar p) =
  no-aliases-avoidᵖ (ext-no-aliases na) p
no-aliases-avoidᵖ na I.bot-elim = tt
no-aliases-avoidᵖ na I.bot⊑★ = tt
no-aliases-avoidᵖ na (I.alias eq p) = ⊥-elim (na _ eq)

------------------------------------------------------------------------
-- Occurrence transfer restricted to the derivation's leaves
------------------------------------------------------------------------

-- The center occurs on the left of every rule whose right-hand side
-- it meets, provided it avoids the representatives of the alias
-- leaves actually used.

target-occurs-sourceᵖ : ∀ {Δ} {μ : I.ImpEnv Δ}
    {c : TyVar Δ} {A B : Ty Δ}
    (p : I._⊢_⊑_ μ A B)
  → AliasAvoidᵖ c p
  → c ∈ᵗ B
  → c ∈ᵗ A
target-occurs-sourceᵖ I.★⊑★ avoid ()
target-occurs-sourceᵖ I.ι⊑ι avoid ()
target-occurs-sourceᵖ I.X⊑X avoid c∈ = c∈
target-occurs-sourceᵖ (I.⇒⊑⇒ p q) (aᵖ , aᵍ) (∈-fun-left c∈) =
  ∈-fun-left (target-occurs-sourceᵖ p aᵖ c∈)
target-occurs-sourceᵖ {c = c} {A = A ⇒ B} (I.⇒⊑⇒ p q)
    (aᵖ , aᵍ) (∈-fun-right c∉ c∈)
    with occurs? c A
target-occurs-sourceᵖ {A = A ⇒ B} (I.⇒⊑⇒ p q)
    (aᵖ , aᵍ) (∈-fun-right c∉ c∈) | present c∈A =
  ∈-fun-left c∈A
target-occurs-sourceᵖ {A = A ⇒ B} (I.⇒⊑⇒ p q)
    (aᵖ , aᵍ) (∈-fun-right c∉ c∈) | absent c∉A =
  ∈-fun-right c∉A (target-occurs-sourceᵖ q aᵍ c∈)
target-occurs-sourceᵖ (I.∀⊑∀ p) avoid (∈-all c∈) =
  ∈-all (target-occurs-sourceᵖ p avoid c∈)
target-occurs-sourceᵖ (I.⇒⊑★ p q) avoid ()
target-occurs-sourceᵖ I.ι⊑★ avoid ()
target-occurs-sourceᵖ (I.X⊑★ eq) avoid ()
target-occurs-sourceᵖ (I.∀⊑ nonvar occurs p) avoid c∈ =
  ∈-all (target-occurs-sourceᵖ p avoid (shift-occurs c∈))
target-occurs-sourceᵖ I.∀★⊑★ avoid ()
target-occurs-sourceᵖ (I.∀⊑★ nonstar p) avoid ()
target-occurs-sourceᵖ I.bot-elim avoid (∈-all ())
target-occurs-sourceᵖ I.bot⊑★ avoid ()
target-occurs-sourceᵖ (I.alias eq p) (c∉T , avoid) c∈ =
  ⊥-elim (PI.∈∉-⊥ c∉T (target-occurs-sourceᵖ p avoid c∈))
