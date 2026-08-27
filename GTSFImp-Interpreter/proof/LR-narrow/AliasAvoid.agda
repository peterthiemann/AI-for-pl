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
open import Data.Sum using (_⊎_; inj₁; inj₂)
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
open import proof.Imprecision using
  (AliasesAvoid; ext-aliases-avoid-suc; inst-aliases-avoid-suc)
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

-- The catch-all transport: between any two derivations whose
-- endpoints agree propositionally (uniqueness closes the gap).

alias-avoid-any : ∀ {Δ} {μ : I.ImpEnv Δ} {A B A′ B′ : Ty Δ}
    {c : TyVar Δ}
    (p : I._⊢_⊑_ μ A B) (q : I._⊢_⊑_ μ A′ B′)
  → A ≡ A′ → B ≡ B′
  → AliasAvoidᵖ c p
  → AliasAvoidᵖ c q
alias-avoid-any p q refl refl avoid = alias-avoid-unique p q avoid

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

------------------------------------------------------------------------
-- Environment-level avoidance restricts to every derivation
------------------------------------------------------------------------

env-aliases-avoidᵖ : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ}
    {c : TyVar Δ}
  → AliasesAvoid μ c
  → (p : I._⊢_⊑_ μ A B)
  → AliasAvoidᵖ c p
env-aliases-avoidᵖ avoid I.★⊑★ = tt
env-aliases-avoidᵖ avoid I.ι⊑ι = tt
env-aliases-avoidᵖ avoid I.X⊑X = tt
env-aliases-avoidᵖ avoid (I.⇒⊑⇒ p q) =
  env-aliases-avoidᵖ avoid p , env-aliases-avoidᵖ avoid q
env-aliases-avoidᵖ avoid (I.∀⊑∀ p) =
  env-aliases-avoidᵖ (ext-aliases-avoid-suc avoid) p
env-aliases-avoidᵖ avoid (I.⇒⊑★ p q) =
  env-aliases-avoidᵖ avoid p , env-aliases-avoidᵖ avoid q
env-aliases-avoidᵖ avoid I.ι⊑★ = tt
env-aliases-avoidᵖ avoid (I.X⊑★ eq) = tt
env-aliases-avoidᵖ avoid (I.∀⊑ nonvar occurs p) =
  env-aliases-avoidᵖ (inst-aliases-avoid-suc avoid) p
env-aliases-avoidᵖ avoid I.∀★⊑★ = tt
env-aliases-avoidᵖ avoid (I.∀⊑★ nonstar p) =
  env-aliases-avoidᵖ (ext-aliases-avoid-suc avoid) p
env-aliases-avoidᵖ avoid I.bot-elim = tt
env-aliases-avoidᵖ avoid I.bot⊑★ = tt
env-aliases-avoidᵖ avoid (I.alias {X = X} eq p) =
  avoid X eq , env-aliases-avoidᵖ avoid p

------------------------------------------------------------------------
-- Transport along endpoint substitutions
------------------------------------------------------------------------

alias-avoid-subst-left : ∀ {Δ} {μ : I.ImpEnv Δ}
    {A A′ B : Ty Δ} {c : TyVar Δ}
    (eq : A ≡ A′) {p : I._⊢_⊑_ μ A B}
  → AliasAvoidᵖ c p
  → AliasAvoidᵖ c (subst≡ (λ L → I._⊢_⊑_ μ L B) eq p)
alias-avoid-subst-left refl avoid = avoid

alias-avoid-subst-rightᵉ : ∀ {Δ} {μ : I.ImpEnv Δ}
    {A B B′ : Ty Δ} {c : TyVar Δ}
    (eq : B ≡ B′) {p : I._⊢_⊑_ μ A B}
  → AliasAvoidᵖ c p
  → AliasAvoidᵖ c (subst≡ (λ R → I._⊢_⊑_ μ A R) eq p)
alias-avoid-subst-rightᵉ refl avoid = avoid

------------------------------------------------------------------------
-- The ★-right-exempt variant
------------------------------------------------------------------------

-- Substitution instances copy the star discharge's subderivations
-- into a derivation's ⊑★ positions, where no avoidance is
-- available; the weakened predicate exempts alias leaves whose
-- right endpoint is ★.  Every position a replacement can change
-- still satisfies the strong clause, since a ★ endpoint is fixed
-- by every replacement (see Finding I item 2 in
-- REPLACEMENT-CLOSURE-DESIGN.md).

AliasAvoid★ᵖ : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ}
  → TyVar Δ → I._⊢_⊑_ μ A B → Set
AliasAvoid★ᵖ c I.★⊑★ = ⊤
AliasAvoid★ᵖ c I.ι⊑ι = ⊤
AliasAvoid★ᵖ c I.X⊑X = ⊤
AliasAvoid★ᵖ c (I.⇒⊑⇒ p q) = AliasAvoid★ᵖ c p × AliasAvoid★ᵖ c q
AliasAvoid★ᵖ c (I.∀⊑∀ p) = AliasAvoid★ᵖ (Fin.suc c) p
AliasAvoid★ᵖ c (I.⇒⊑★ p q) = AliasAvoid★ᵖ c p × AliasAvoid★ᵖ c q
AliasAvoid★ᵖ c I.ι⊑★ = ⊤
AliasAvoid★ᵖ c (I.X⊑★ eq) = ⊤
AliasAvoid★ᵖ c (I.∀⊑ nonvar occurs p) =
  AliasAvoid★ᵖ (Fin.suc c) p
AliasAvoid★ᵖ c I.∀★⊑★ = ⊤
AliasAvoid★ᵖ c (I.∀⊑★ nonstar p) = AliasAvoid★ᵖ (Fin.suc c) p
AliasAvoid★ᵖ c I.bot-elim = ⊤
AliasAvoid★ᵖ c I.bot⊑★ = ⊤
AliasAvoid★ᵖ c (I.alias {T = T} {B = B} eq p) =
  ((B ≡ ★) ⊎ (c ∉ᵗ T)) × AliasAvoid★ᵖ c p

-- The strong predicate weakens.

alias-avoid-weaken★ : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ}
    {c : TyVar Δ}
    (p : I._⊢_⊑_ μ A B)
  → AliasAvoidᵖ c p
  → AliasAvoid★ᵖ c p
alias-avoid-weaken★ I.★⊑★ avoid = tt
alias-avoid-weaken★ I.ι⊑ι avoid = tt
alias-avoid-weaken★ I.X⊑X avoid = tt
alias-avoid-weaken★ (I.⇒⊑⇒ p q) (avoidᵖ , avoidᵍ) =
  alias-avoid-weaken★ p avoidᵖ , alias-avoid-weaken★ q avoidᵍ
alias-avoid-weaken★ (I.∀⊑∀ p) avoid = alias-avoid-weaken★ p avoid
alias-avoid-weaken★ (I.⇒⊑★ p q) (avoidᵖ , avoidᵍ) =
  alias-avoid-weaken★ p avoidᵖ , alias-avoid-weaken★ q avoidᵍ
alias-avoid-weaken★ I.ι⊑★ avoid = tt
alias-avoid-weaken★ (I.X⊑★ eq) avoid = tt
alias-avoid-weaken★ (I.∀⊑ nonvar occurs p) avoid =
  alias-avoid-weaken★ p avoid
alias-avoid-weaken★ I.∀★⊑★ avoid = tt
alias-avoid-weaken★ (I.∀⊑★ nonstar p) avoid =
  alias-avoid-weaken★ p avoid
alias-avoid-weaken★ I.bot-elim avoid = tt
alias-avoid-weaken★ I.bot⊑★ avoid = tt
alias-avoid-weaken★ (I.alias eq p) (c∉T , avoid) =
  inj₂ c∉T , alias-avoid-weaken★ p avoid

-- Transport between derivations of one judgment, and the
-- endpoint-propositional catch-all.

alias-avoid★-unique : ∀ {Δ} {μ : I.ImpEnv Δ} {A B : Ty Δ}
    {c : TyVar Δ}
    (p q : I._⊢_⊑_ μ A B)
  → AliasAvoid★ᵖ c p
  → AliasAvoid★ᵖ c q
alias-avoid★-unique {c = c} p q avoid =
  subst≡ (AliasAvoid★ᵖ c) (PI.⊑-unique p q) avoid

alias-avoid★-any : ∀ {Δ} {μ : I.ImpEnv Δ} {A B A′ B′ : Ty Δ}
    {c : TyVar Δ}
    (p : I._⊢_⊑_ μ A B) (q : I._⊢_⊑_ μ A′ B′)
  → A ≡ A′ → B ≡ B′
  → AliasAvoid★ᵖ c p
  → AliasAvoid★ᵖ c q
alias-avoid★-any p q refl refl avoid =
  alias-avoid★-unique p q avoid

-- Transport along endpoint substitutions.

alias-avoid★-subst-left : ∀ {Δ} {μ : I.ImpEnv Δ}
    {A A′ B : Ty Δ} {c : TyVar Δ}
    (eq : A ≡ A′) {p : I._⊢_⊑_ μ A B}
  → AliasAvoid★ᵖ c p
  → AliasAvoid★ᵖ c (subst≡ (λ L → I._⊢_⊑_ μ L B) eq p)
alias-avoid★-subst-left refl avoid = avoid

alias-avoid★-subst-rightᵉ : ∀ {Δ} {μ : I.ImpEnv Δ}
    {A B B′ : Ty Δ} {c : TyVar Δ}
    (eq : B ≡ B′) {p : I._⊢_⊑_ μ A B}
  → AliasAvoid★ᵖ c p
  → AliasAvoid★ᵖ c (subst≡ (λ R → I._⊢_⊑_ μ A R) eq p)
alias-avoid★-subst-rightᵉ refl avoid = avoid

-- Transport along renamings.

alias-avoid★-rename : ∀ {Δ Δ′} {μ : I.ImpEnv Δ}
    {μ′ : I.ImpEnv Δ′} {A B : Ty Δ} {c : TyVar Δ}
    (ρ : Δ ⇒ʳ Δ′)
    (injective : ∀ {Y Z} → ρ Y ≡ ρ Z → Y ≡ Z)
    (h : ∀ X → μ X ≡ I.X⊑★ → μ′ (ρ X) ≡ I.X⊑★)
    (ha : RenameAliasMap ρ μ μ′)
    (p : I._⊢_⊑_ μ A B)
  → AliasAvoid★ᵖ c p
  → AliasAvoid★ᵖ (ρ c)
      (rename-⊑ {μ = μ} {μ′ = μ′} ρ injective h ha p)
alias-avoid★-rename ρ injective h ha I.★⊑★ avoid = tt
alias-avoid★-rename ρ injective h ha I.ι⊑ι avoid = tt
alias-avoid★-rename ρ injective h ha I.X⊑X avoid = tt
alias-avoid★-rename {μ′ = μ′} ρ injective h ha (I.⇒⊑⇒ p q)
    (avoidᵖ , avoidᵍ) =
  alias-avoid★-rename {μ′ = μ′} ρ injective h ha p avoidᵖ ,
  alias-avoid★-rename {μ′ = μ′} ρ injective h ha q avoidᵍ
alias-avoid★-rename {μ′ = μ′} ρ injective h ha (I.∀⊑∀ p) avoid =
  alias-avoid★-rename {μ′ = I.extᵐ μ′} (extᵗ ρ)
    (ext-injective injective)
    (rename-star-map-ext ρ h) (rename-alias-map-ext ρ ha) p avoid
alias-avoid★-rename {μ′ = μ′} ρ injective h ha (I.⇒⊑★ p q)
    (avoidᵖ , avoidᵍ) =
  alias-avoid★-rename {μ′ = μ′} ρ injective h ha p avoidᵖ ,
  alias-avoid★-rename {μ′ = μ′} ρ injective h ha q avoidᵍ
alias-avoid★-rename ρ injective h ha I.ι⊑★ avoid = tt
alias-avoid★-rename ρ injective h ha (I.X⊑★ eq) avoid = tt
alias-avoid★-rename {μ′ = μ′} {c = c} ρ injective h ha
    (I.∀⊑ {A = A₀} {B = B₀} nonvar occurs p) avoid =
  alias-avoid★-subst-right (renameᵗ-shift ρ B₀)
    (alias-avoid★-rename {μ′ = I.instᵐ μ′} (extᵗ ρ)
      (ext-injective injective)
      (rename-star-map-inst ρ h) (rename-alias-map-inst ρ ha)
      p avoid)
  where
  alias-avoid★-subst-right : ∀ {Δ₁} {μ₁ : I.ImpEnv Δ₁}
      {A₁ B₁ B₁′ : Ty Δ₁} {c₁ : TyVar Δ₁}
      (eq : B₁ ≡ B₁′) {p₁ : I._⊢_⊑_ μ₁ A₁ B₁}
    → AliasAvoid★ᵖ c₁ p₁
    → AliasAvoid★ᵖ c₁
        (subst≡ (λ T → I._⊢_⊑_ μ₁ A₁ T) eq p₁)
  alias-avoid★-subst-right refl avoid′ = avoid′
alias-avoid★-rename ρ injective h ha I.∀★⊑★ avoid = tt
alias-avoid★-rename {μ′ = μ′} ρ injective h ha
    (I.∀⊑★ nonstar p) avoid =
  alias-avoid★-rename {μ′ = I.extᵐ μ′} (extᵗ ρ)
    (ext-injective injective)
    (rename-star-map-ext ρ h) (rename-alias-map-ext ρ ha) p avoid
alias-avoid★-rename ρ injective h ha I.bot-elim avoid = tt
alias-avoid★-rename ρ injective h ha I.bot⊑★ avoid = tt
alias-avoid★-rename {μ′ = μ′} ρ injective h ha
    (I.alias {T = T} eq p)
    (inj₁ B≡★ , avoid) =
  inj₁ (cong (renameᵗ ρ) B≡★) ,
  alias-avoid★-rename {μ′ = μ′} ρ injective h ha p avoid
alias-avoid★-rename {μ′ = μ′} ρ injective h ha
    (I.alias {T = T} eq p)
    (inj₂ c∉T , avoid) =
  inj₂ (renameᵗ-∉ᵗ ρ injective c∉T) ,
  alias-avoid★-rename {μ′ = μ′} ρ injective h ha p avoid

-- Occurrence transfer: the exempted leaves have ★ on the right,
-- where nothing occurs.

target-occurs-source★ᵖ : ∀ {Δ} {μ : I.ImpEnv Δ}
    {c : TyVar Δ} {A B : Ty Δ}
    (p : I._⊢_⊑_ μ A B)
  → AliasAvoid★ᵖ c p
  → c ∈ᵗ B
  → c ∈ᵗ A
target-occurs-source★ᵖ I.★⊑★ avoid ()
target-occurs-source★ᵖ I.ι⊑ι avoid ()
target-occurs-source★ᵖ I.X⊑X avoid c∈ = c∈
target-occurs-source★ᵖ (I.⇒⊑⇒ p q) (aᵖ , aᵍ)
    (∈-fun-left c∈) =
  ∈-fun-left (target-occurs-source★ᵖ p aᵖ c∈)
target-occurs-source★ᵖ {c = c} {A = A ⇒ B} (I.⇒⊑⇒ p q)
    (aᵖ , aᵍ) (∈-fun-right c∉ c∈)
    with occurs? c A
target-occurs-source★ᵖ {A = A ⇒ B} (I.⇒⊑⇒ p q)
    (aᵖ , aᵍ) (∈-fun-right c∉ c∈) | present c∈A =
  ∈-fun-left c∈A
target-occurs-source★ᵖ {A = A ⇒ B} (I.⇒⊑⇒ p q)
    (aᵖ , aᵍ) (∈-fun-right c∉ c∈) | absent c∉A =
  ∈-fun-right c∉A (target-occurs-source★ᵖ q aᵍ c∈)
target-occurs-source★ᵖ (I.∀⊑∀ p) avoid (∈-all c∈) =
  ∈-all (target-occurs-source★ᵖ p avoid c∈)
target-occurs-source★ᵖ (I.⇒⊑★ p q) avoid ()
target-occurs-source★ᵖ I.ι⊑★ avoid ()
target-occurs-source★ᵖ (I.X⊑★ eq) avoid ()
target-occurs-source★ᵖ (I.∀⊑ nonvar occurs p) avoid c∈ =
  ∈-all (target-occurs-source★ᵖ p avoid (shift-occurs c∈))
target-occurs-source★ᵖ I.∀★⊑★ avoid ()
target-occurs-source★ᵖ (I.∀⊑★ nonstar p) avoid ()
target-occurs-source★ᵖ I.bot-elim avoid (∈-all ())
target-occurs-source★ᵖ I.bot⊑★ avoid ()
target-occurs-source★ᵖ (I.alias eq p) (inj₁ refl , avoid) ()
target-occurs-source★ᵖ (I.alias eq p) (inj₂ c∉T , avoid) c∈ =
  ⊥-elim (PI.∈∉-⊥ c∉T (target-occurs-source★ᵖ p avoid c∈))
