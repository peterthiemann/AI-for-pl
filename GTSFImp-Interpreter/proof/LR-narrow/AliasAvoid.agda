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
open import Data.Nat using (suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Fin as Fin
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst₂)
  renaming (subst to subst≡)

open import Types
import Imprecision as I
import proof.Imprecision as PI
open import proof.ImprecisionConsistency using
  (rename-⊑; RenameAliasMap; NoAliases; ext-no-aliases;
   inst-no-aliases; shift-occurs; ext-injective;
   rename-star-map-ext; rename-star-map-inst;
   rename-alias-map-ext; rename-alias-map-inst;
   fin-suc-injective; subst₂-⊑; SubstAliasMap;
   subst₂-same-map-exts; subst₂-same-map-insts;
   subst₂-star-map-exts; subst₂-star-map-insts;
   subst-alias-map-exts; subst-alias-map-insts;
   shift-⊑; shift-star-map; shift-alias-map)
open import proof.Imprecision using
  (AliasesAvoid; ext-aliases-avoid-suc; inst-aliases-avoid-suc)
open import proof.LR-narrow.StarNoOccurrence using
  (renameᵗ-∉ᵗ; renameᵗ-reflects-∉ᵗ)

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

------------------------------------------------------------------------
-- Below ★ every alias leaf is exempted
------------------------------------------------------------------------

-- The subderivations of a derivation whose right endpoint is ★ all
-- have ★ on the right themselves, so the weakened predicate holds of
-- them outright: every alias leaf takes the exemption branch.

star-avoid★ᵖ : ∀ {Δ} {μ : I.ImpEnv Δ} {A : Ty Δ} {c : TyVar Δ}
    (p : I._⊢_⊑_ μ A ★)
  → AliasAvoid★ᵖ c p
star-avoid★ᵖ I.★⊑★ = tt
star-avoid★ᵖ I.ι⊑★ = tt
star-avoid★ᵖ (I.X⊑★ eq) = tt
star-avoid★ᵖ (I.⇒⊑★ p q) = star-avoid★ᵖ p , star-avoid★ᵖ q
star-avoid★ᵖ I.∀★⊑★ = tt
star-avoid★ᵖ (I.∀⊑★ nonstar p) = star-avoid★ᵖ p
star-avoid★ᵖ (I.∀⊑ nonvar occurs p) = star-avoid★ᵖ p
star-avoid★ᵖ I.bot⊑★ = tt
star-avoid★ᵖ (I.alias eq p) = inj₁ refl , star-avoid★ᵖ p

------------------------------------------------------------------------
-- Avoidance through a two-sided substitution
------------------------------------------------------------------------

-- Transport along `subst₂-⊑`: inherited alias leaves substitute their
-- recorded representative, so the avoidance premise is a substituted
-- non-occurrence; the star-map's copies land below ★ and are covered
-- by `star-avoid★ᵖ`; the same-map's insertions carry their own
-- avoidance.

alias-avoid★-subst₂ : ∀ {Δ} {μ : I.ImpEnv Δ}
    {A A′ B B′ : Ty Δ} {c : TyVar Δ}
    (eqᴸ : A ≡ A′) (eqᴿ : B ≡ B′)
    (p : I._⊢_⊑_ μ A B)
  → AliasAvoid★ᵖ c p
  → AliasAvoid★ᵖ c (subst₂ (λ L R → I._⊢_⊑_ μ L R) eqᴸ eqᴿ p)
alias-avoid★-subst₂ refl refl p avoid = avoid

same-avoid-exts : ∀ {Δ Δ′} {ν : I.ImpEnv Δ′}
    {σᴸ σᴿ : Δ ⇒ˢ Δ′} {c′ : TyVar Δ′}
    (same : ∀ X → ν I.⊢ σᴸ X ⊑ σᴿ X)
  → (∀ X → AliasAvoid★ᵖ c′ (same X))
  → ∀ X → AliasAvoid★ᵖ (Fin.suc c′)
      (subst₂-same-map-exts same X)
same-avoid-exts same sa Fin.zero = tt
same-avoid-exts {ν = ν} same sa (Fin.suc X) =
  alias-avoid★-rename Fin.suc fin-suc-injective
    (shift-star-map {ν = ν} {v = I.X⊑X})
    (shift-alias-map {ν = ν} {v = I.X⊑X})
    (same X) (sa X)

same-avoid-insts : ∀ {Δ Δ′} {ν : I.ImpEnv Δ′}
    {σᴸ σᴿ : Δ ⇒ˢ Δ′} {c′ : TyVar Δ′}
    (same : ∀ X → ν I.⊢ σᴸ X ⊑ σᴿ X)
  → (∀ X → AliasAvoid★ᵖ c′ (same X))
  → ∀ X → AliasAvoid★ᵖ (Fin.suc c′)
      (subst₂-same-map-insts same X)
same-avoid-insts same sa Fin.zero = tt
same-avoid-insts {ν = ν} same sa (Fin.suc X) =
  alias-avoid★-rename Fin.suc fin-suc-injective
    (shift-star-map {ν = ν} {v = I.X⊑★})
    (shift-alias-map {ν = ν} {v = I.X⊑★})
    (same X) (sa X)

subst-avoid-map-extend : ∀ {Δ Δ′} {μ : I.ImpEnv Δ}
    {σ : Δ ⇒ˢ Δ′} {v : I.VarImp (suc Δ)}
    {c : TyVar Δ} {c′ : TyVar Δ′}
  → (∀ {T} → v ≡ I.X⊑ᵗ T → ⊥)
  → (∀ X {T} → μ X ≡ I.X⊑ᵗ T → c ∉ᵗ T → c′ ∉ᵗ substᵗ σ T)
  → ∀ X {T} → I.extendᵐ v μ X ≡ I.X⊑ᵗ T
  → Fin.suc c ∉ᵗ T
  → Fin.suc c′ ∉ᵗ substᵗ (extsᵗ σ) T
subst-avoid-map-extend head-not-alias hav Fin.zero eq c∉T =
  ⊥-elim (head-not-alias eq)
subst-avoid-map-extend hna hav (Fin.suc X) eq c∉T
    with I.lift-alias-inv eq
subst-avoid-map-extend {σ = σ} {c′ = c′} hna hav
    (Fin.suc X) eq c∉T | T₀ , mode , refl =
  subst≡ (Fin.suc c′ ∉ᵗ_) (sym (substᵗ-shift σ T₀))
    (renameᵗ-∉ᵗ Fin.suc fin-suc-injective
      (hav X mode (renameᵗ-reflects-∉ᵗ Fin.suc T₀ c∉T)))

subst₂-avoid★ : ∀ {Δ Δ′} {μ : I.ImpEnv Δ} {ν : I.ImpEnv Δ′}
    {σᴸ σᴿ : Δ ⇒ˢ Δ′} {A B : Ty Δ} {c : TyVar Δ} {c′ : TyVar Δ′}
    (same : ∀ X → ν I.⊢ σᴸ X ⊑ σᴿ X)
    (star : ∀ X → μ X ≡ I.X⊑★ → ν I.⊢ σᴸ X ⊑ ★)
    (ha : SubstAliasMap μ ν σᴸ)
  → (∀ X → AliasAvoid★ᵖ c′ (same X))
  → (∀ X {T} → μ X ≡ I.X⊑ᵗ T → c ∉ᵗ T → c′ ∉ᵗ substᵗ σᴸ T)
  → (p : I._⊢_⊑_ μ A B)
  → AliasAvoid★ᵖ c p
  → AliasAvoid★ᵖ c′ (subst₂-⊑ same star ha p)
subst₂-avoid★ same star ha sa hav I.★⊑★ avoid = tt
subst₂-avoid★ same star ha sa hav I.ι⊑ι avoid = tt
subst₂-avoid★ same star ha sa hav I.X⊑X avoid = sa _
subst₂-avoid★ same star ha sa hav (I.⇒⊑⇒ p q) (ap , aq) =
  subst₂-avoid★ same star ha sa hav p ap ,
  subst₂-avoid★ same star ha sa hav q aq
subst₂-avoid★ {μ = μ} {ν = ν} {σᴸ = σᴸ} {σᴿ = σᴿ}
    same star ha sa hav (I.∀⊑∀ p) avoid =
  subst₂-avoid★ {μ = I.extᵐ μ} {ν = I.extᵐ ν}
    {σᴸ = extsᵗ σᴸ} {σᴿ = extsᵗ σᴿ}
    (subst₂-same-map-exts same) (subst₂-star-map-exts star)
    (subst-alias-map-exts ha)
    (same-avoid-exts same sa)
    (subst-avoid-map-extend (λ ()) hav) p avoid
subst₂-avoid★ same star ha sa hav (I.⇒⊑★ p q) avoid =
  star-avoid★ᵖ (subst₂-⊑ same star ha p) ,
  star-avoid★ᵖ (subst₂-⊑ same star ha q)
subst₂-avoid★ same star ha sa hav I.ι⊑★ avoid = tt
subst₂-avoid★ same star ha sa hav (I.X⊑★ x⊑★) avoid =
  star-avoid★ᵖ (star _ x⊑★)
subst₂-avoid★ {μ = μ} {ν = ν} {σᴸ = σᴸ} {σᴿ = σᴿ}
    same star ha sa hav
    (I.∀⊑ {A = A} {B = B} nonvar occurs p) avoid =
  alias-avoid★-subst-rightᵉ (substᵗ-shift σᴿ B)
    (subst₂-avoid★ {μ = I.instᵐ μ} {ν = I.instᵐ ν}
      {σᴸ = extsᵗ σᴸ} {σᴿ = extsᵗ σᴿ}
      (subst₂-same-map-insts same) (subst₂-star-map-insts star)
      (subst-alias-map-insts ha)
      (same-avoid-insts same sa)
      (subst-avoid-map-extend (λ ()) hav) p avoid)
subst₂-avoid★ same star ha sa hav I.∀★⊑★ avoid = tt
subst₂-avoid★ same star ha sa hav (I.∀⊑★ nonstar p) avoid =
  star-avoid★ᵖ (subst₂-⊑ same star ha (I.∀⊑★ nonstar p))
subst₂-avoid★ same star ha sa hav I.bot-elim avoid = tt
subst₂-avoid★ same star ha sa hav I.bot⊑★ avoid = tt
subst₂-avoid★ {σᴸ = σᴸ} {σᴿ = σᴿ} same star ha sa hav
    (I.alias {X = X} {T = T} {B = B} eq p) (leaf , av-p)
    with ha X eq
subst₂-avoid★ {σᴸ = σᴸ} {σᴿ = σᴿ} same star ha sa hav
    (I.alias {X = X} {T = T} {B = B} eq p) (leaf , av-p)
    | inj₁ collapse =
  alias-avoid★-subst-left (sym collapse)
    (subst₂-avoid★ same star ha sa hav p av-p)
subst₂-avoid★ {σᴸ = σᴸ} {σᴿ = σᴿ} same star ha sa hav
    (I.alias {X = X} {T = T} {B = B} eq p) (leaf , av-p)
    | inj₂ (X′ , to-var , aliased)
    with isVar? X′ (substᵗ σᴿ B)
subst₂-avoid★ {σᴸ = σᴸ} {σᴿ = σᴿ} same star ha sa hav
    (I.alias {X = X} {T = T} {B = B} eq p) (leaf , av-p)
    | inj₂ (X′ , to-var , aliased) | yes B≡X′ =
  alias-avoid★-subst₂ (sym to-var) (sym B≡X′) I.X⊑X tt
subst₂-avoid★ {σᴸ = σᴸ} {σᴿ = σᴿ} {c = c} {c′ = c′}
    same star ha sa hav
    (I.alias {X = X} {T = T} {B = B} eq p) (leaf , av-p)
    | inj₂ (X′ , to-var , aliased) | no B≢X′ =
  alias-avoid★-subst-left (sym to-var)
    (map-leaf leaf ,
     subst₂-avoid★ same star ha sa hav p av-p)
  where
  map-leaf : (B ≡ ★) ⊎ (c ∉ᵗ T)
    → (substᵗ σᴿ B ≡ ★) ⊎ (c′ ∉ᵗ substᵗ σᴸ T)
  map-leaf (inj₁ eqB) = inj₁ (cong (substᵗ σᴿ) eqB)
  map-leaf (inj₂ c∉T) = inj₂ (hav X eq c∉T)
