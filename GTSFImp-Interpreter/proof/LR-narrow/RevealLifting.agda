module proof.LR-narrow.RevealLifting where

-- File Charter:
--   * Renaming laws for the structural reveal and conceal conversions:
--     an injective type renaming commutes with `〖_,_↑_〗` and
--     `makeConceal`, and with `replaceTy`.
--   * Lifting laws along LR futures: a structural reveal or conceal of a
--     value at a slot lifts to the structural reveal or conceal at the
--     lifted slot.
--   * Paired slots as a package, and their transport along futures.

open import Data.Nat using (suc)
import Data.Fin as Fin
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)
  renaming (subst to subst≡)
open import Relation.Nullary using (yes; no)
open import Data.Fin.Properties using (_≟_)

open import Types
open import CastTerms
open import Conversion using
  (Conv↑; Conv↓; unseal; seal; _↦↑_; _↦↓_; `∀↑_; `∀↓_; id↑; id↓;
   rename↑; rename↓; replaceTy; 〖_,_↑_〗; makeConceal)
open import Consistency using (toRenameᵗ; wk↪ᵗ)
import Imprecision as I
open import proof.ImprecisionConsistency using
  (toRenameᵗ-injective; ext-injective; fin-suc-injective;
   shift-star-map; shift-alias-map;
   rename-star-map-ext; rename-star-map-inst;
   rename-alias-map-ext; rename-alias-map-inst)
open import proof.LR-narrow.AliasAvoid using
  (AliasAvoidᵖ; alias-avoid-rename;
   AliasAvoid★ᵖ; alias-avoid★-rename)
open import proof.TypeInTermSubst using (toRename-wk-eq; renameᵗ-wk-eq)
open import proof.LR-narrow.TypeRenamingComposition using
  (Packed↑; Packed↓; pack↑; pack↓; pack-↦↑; pack-↦↓; pack-∀↑; pack-∀↓;
   apply↑; apply↓)
open import LR-narrow.World
open import LR-narrow.Atoms
open import LR-narrow.SlotSequence public

------------------------------------------------------------------------
-- Renaming laws
------------------------------------------------------------------------

Injective : ∀ {Δ Δ′} → (Δ ⇒ʳ Δ′) → Set
Injective ρ = ∀ {X Y} → ρ X ≡ ρ Y → X ≡ Y

renameᵗ-replaceTy : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) → Injective ρ
  → (X : TyVar Δ) (R B : Ty Δ)
  → renameᵗ ρ (replaceTy X R B)
      ≡ replaceTy (ρ X) (renameᵗ ρ R) (renameᵗ ρ B)
renameᵗ-replaceTy ρ injective X R (＇ Y) with X ≟ Y
renameᵗ-replaceTy ρ injective X R (＇ .X) | yes refl with ρ X ≟ ρ X
renameᵗ-replaceTy ρ injective X R (＇ .X) | yes refl | yes refl = refl
renameᵗ-replaceTy ρ injective X R (＇ .X) | yes refl | no neq =
  ⊥-elim (neq refl)
renameᵗ-replaceTy ρ injective X R (＇ Y) | no X≢Y with ρ X ≟ ρ Y
renameᵗ-replaceTy ρ injective X R (＇ Y) | no X≢Y | yes eq =
  ⊥-elim (X≢Y (injective eq))
renameᵗ-replaceTy ρ injective X R (＇ Y) | no X≢Y | no neq = refl
renameᵗ-replaceTy ρ injective X R (‵ ι) = refl
renameᵗ-replaceTy ρ injective X R ★ = refl
renameᵗ-replaceTy ρ injective X R (A ⇒ B) =
  cong₂ _⇒_ (renameᵗ-replaceTy ρ injective X R A)
    (renameᵗ-replaceTy ρ injective X R B)
renameᵗ-replaceTy ρ injective X R (`∀ B) =
  cong `∀
    (trans (renameᵗ-replaceTy (extᵗ ρ) (ext-injective injective)
      (Fin.suc X) (⇑ᵗ R) B)
      (cong (λ T → replaceTy (Fin.suc (ρ X)) T (renameᵗ (extᵗ ρ) B))
        (renameᵗ-shift ρ R)))

mutual
  rename-structural-reveal : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) → Injective ρ
    → (X : TyVar Δ) (R B : Ty Δ)
    → pack↑ (rename↑ ρ 〖 X , R ↑ B 〗)
        ≡ pack↑ 〖 ρ X , renameᵗ ρ R ↑ renameᵗ ρ B 〗
  rename-structural-reveal ρ injective X R (＇ Y) with X ≟ Y
  rename-structural-reveal ρ injective X R (＇ .X) | yes refl
      with ρ X ≟ ρ X
  rename-structural-reveal ρ injective X R (＇ .X) | yes refl | yes refl = refl
  rename-structural-reveal ρ injective X R (＇ .X) | yes refl | no neq =
    ⊥-elim (neq refl)
  rename-structural-reveal ρ injective X R (＇ Y) | no X≢Y with ρ X ≟ ρ Y
  rename-structural-reveal ρ injective X R (＇ Y) | no X≢Y | yes eq =
    ⊥-elim (X≢Y (injective eq))
  rename-structural-reveal ρ injective X R (＇ Y) | no X≢Y | no neq = refl
  rename-structural-reveal ρ injective X R (‵ ι) = refl
  rename-structural-reveal ρ injective X R ★ = refl
  rename-structural-reveal ρ injective X R (A ⇒ B) =
    cong₂ pack-↦↑ (rename-structural-conceal ρ injective X R A)
      (rename-structural-reveal ρ injective X R B)
  rename-structural-reveal ρ injective X R (`∀ B) =
    cong pack-∀↑
      (trans (rename-structural-reveal (extᵗ ρ) (ext-injective injective)
        (Fin.suc X) (⇑ᵗ R) B)
        (cong (λ T → pack↑ 〖 Fin.suc (ρ X) , T ↑ renameᵗ (extᵗ ρ) B 〗)
          (renameᵗ-shift ρ R)))

  rename-structural-conceal : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) → Injective ρ
    → (X : TyVar Δ) (R B : Ty Δ)
    → pack↓ (rename↓ ρ (makeConceal X R B))
        ≡ pack↓ (makeConceal (ρ X) (renameᵗ ρ R) (renameᵗ ρ B))
  rename-structural-conceal ρ injective X R (＇ Y) with X ≟ Y
  rename-structural-conceal ρ injective X R (＇ .X) | yes refl
      with ρ X ≟ ρ X
  rename-structural-conceal ρ injective X R (＇ .X) | yes refl | yes refl = refl
  rename-structural-conceal ρ injective X R (＇ .X) | yes refl | no neq =
    ⊥-elim (neq refl)
  rename-structural-conceal ρ injective X R (＇ Y) | no X≢Y with ρ X ≟ ρ Y
  rename-structural-conceal ρ injective X R (＇ Y) | no X≢Y | yes eq =
    ⊥-elim (X≢Y (injective eq))
  rename-structural-conceal ρ injective X R (＇ Y) | no X≢Y | no neq = refl
  rename-structural-conceal ρ injective X R (‵ ι) = refl
  rename-structural-conceal ρ injective X R ★ = refl
  rename-structural-conceal ρ injective X R (A ⇒ B) =
    cong₂ pack-↦↓ (rename-structural-reveal ρ injective X R A)
      (rename-structural-conceal ρ injective X R B)
  rename-structural-conceal ρ injective X R (`∀ B) =
    cong pack-∀↓
      (trans (rename-structural-conceal (extᵗ ρ) (ext-injective injective)
        (Fin.suc X) (⇑ᵗ R) B)
        (cong (λ T → pack↓ (makeConceal (Fin.suc (ρ X)) T
          (renameᵗ (extᵗ ρ) B)))
          (renameᵗ-shift ρ R)))

------------------------------------------------------------------------
-- One weakening step
------------------------------------------------------------------------

shift-structural-reveal : ∀ {Δ} (V : Term Δ) (X : TyVar Δ) (R B : Ty Δ)
  → ⇑ᵗᵐ (V ↑ 〖 X , R ↑ B 〗)
      ≡ ⇑ᵗᵐ V ↑ 〖 Fin.suc X , ⇑ᵗ R ↑ ⇑ᵗ B 〗
shift-structural-reveal V X R B =
  cong (apply↑ (⇑ᵗᵐ V))
    (trans (rename-structural-reveal (toRenameᵗ wk↪ᵗ)
      (toRenameᵗ-injective wk↪ᵗ) X R B) pack-eq)
  where
  pack-eq : pack↑ 〖 toRenameᵗ wk↪ᵗ X , renameᵗ (toRenameᵗ wk↪ᵗ) R
      ↑ renameᵗ (toRenameᵗ wk↪ᵗ) B 〗
    ≡ pack↑ 〖 Fin.suc X , ⇑ᵗ R ↑ ⇑ᵗ B 〗
  pack-eq rewrite toRename-wk-eq X | renameᵗ-wk-eq R | renameᵗ-wk-eq B =
    refl

shift-structural-conceal : ∀ {Δ} (V : Term Δ) (X : TyVar Δ) (R B : Ty Δ)
  → ⇑ᵗᵐ (V ↓ makeConceal X R B)
      ≡ ⇑ᵗᵐ V ↓ makeConceal (Fin.suc X) (⇑ᵗ R) (⇑ᵗ B)
shift-structural-conceal V X R B =
  cong (apply↓ (⇑ᵗᵐ V))
    (trans (rename-structural-conceal (toRenameᵗ wk↪ᵗ)
      (toRenameᵗ-injective wk↪ᵗ) X R B) pack-eq)
  where
  pack-eq : pack↓ (makeConceal (toRenameᵗ wk↪ᵗ X)
      (renameᵗ (toRenameᵗ wk↪ᵗ) R) (renameᵗ (toRenameᵗ wk↪ᵗ) B))
    ≡ pack↓ (makeConceal (Fin.suc X) (⇑ᵗ R) (⇑ᵗ B))
  pack-eq rewrite toRename-wk-eq X | renameᵗ-wk-eq R | renameᵗ-wk-eq B =
    refl

shift-replace : ∀ {Δ} (X : TyVar Δ) (R B : Ty Δ)
  → ⇑ᵗ (replaceTy X R B) ≡ replaceTy (Fin.suc X) (⇑ᵗ R) (⇑ᵗ B)
shift-replace X R B =
  trans (sym (renameᵗ-wk-eq (replaceTy X R B)))
    (trans (renameᵗ-replaceTy (toRenameᵗ wk↪ᵗ)
      (toRenameᵗ-injective wk↪ᵗ) X R B)
      (cong₃ (toRename-wk-eq X) (renameᵗ-wk-eq R) (renameᵗ-wk-eq B)))
  where
  cong₃ : ∀ {Y Y′ : TyVar (suc _)} {T T′ U U′ : Ty (suc _)}
    → Y ≡ Y′ → T ≡ T′ → U ≡ U′
    → replaceTy Y T U ≡ replaceTy Y′ T′ U′
  cong₃ refl refl refl = refl

------------------------------------------------------------------------
-- Lifting along futures
------------------------------------------------------------------------

liftPreciseTerm-reveal : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (V : Term Δᴾ) (X : TyVar Δᴾ) (R B : Ty Δᴾ)
  → liftPreciseTerm W≼W′ (V ↑ 〖 X , R ↑ B 〗)
      ≡ liftPreciseTerm W≼W′ V
          ↑ 〖 liftPreciseVariable W≼W′ X , liftPreciseTy W≼W′ R
              ↑ liftPreciseTy W≼W′ B 〗
liftPreciseTerm-reveal future-refl V X R B = refl
liftPreciseTerm-reveal (future-paired W≼W′ r) V X R B
    rewrite liftPreciseTerm-reveal W≼W′ V X R B =
  shift-structural-reveal _ _ _ _
liftPreciseTerm-reveal (future-precise W≼W′ r) V X R B
    rewrite liftPreciseTerm-reveal W≼W′ V X R B =
  shift-structural-reveal _ _ _ _
liftPreciseTerm-reveal (future-alias W≼W′) V X R B
    rewrite liftPreciseTerm-reveal W≼W′ V X R B =
  shift-structural-reveal _ _ _ _
liftPreciseTerm-reveal (future-imprecise W≼W′) V X R B =
  liftPreciseTerm-reveal W≼W′ V X R B

liftImpreciseTerm-reveal : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (V : Term Δᴵ) (X : TyVar Δᴵ) (R B : Ty Δᴵ)
  → liftImpreciseTerm W≼W′ (V ↑ 〖 X , R ↑ B 〗)
      ≡ liftImpreciseTerm W≼W′ V
          ↑ 〖 liftImpreciseVariable W≼W′ X , liftImpreciseTy W≼W′ R
              ↑ liftImpreciseTy W≼W′ B 〗
liftImpreciseTerm-reveal future-refl V X R B = refl
liftImpreciseTerm-reveal (future-paired W≼W′ r) V X R B
    rewrite liftImpreciseTerm-reveal W≼W′ V X R B =
  shift-structural-reveal _ _ _ _
liftImpreciseTerm-reveal (future-precise W≼W′ r) V X R B =
  liftImpreciseTerm-reveal W≼W′ V X R B
liftImpreciseTerm-reveal (future-alias W≼W′) V X R B =
  liftImpreciseTerm-reveal W≼W′ V X R B
liftImpreciseTerm-reveal (future-imprecise W≼W′) V X R B
    rewrite liftImpreciseTerm-reveal W≼W′ V X R B =
  shift-structural-reveal _ _ _ _

liftPreciseTerm-conceal : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (V : Term Δᴾ) (X : TyVar Δᴾ) (R B : Ty Δᴾ)
  → liftPreciseTerm W≼W′ (V ↓ makeConceal X R B)
      ≡ liftPreciseTerm W≼W′ V
          ↓ makeConceal (liftPreciseVariable W≼W′ X)
              (liftPreciseTy W≼W′ R) (liftPreciseTy W≼W′ B)
liftPreciseTerm-conceal future-refl V X R B = refl
liftPreciseTerm-conceal (future-paired W≼W′ r) V X R B
    rewrite liftPreciseTerm-conceal W≼W′ V X R B =
  shift-structural-conceal _ _ _ _
liftPreciseTerm-conceal (future-precise W≼W′ r) V X R B
    rewrite liftPreciseTerm-conceal W≼W′ V X R B =
  shift-structural-conceal _ _ _ _
liftPreciseTerm-conceal (future-alias W≼W′) V X R B
    rewrite liftPreciseTerm-conceal W≼W′ V X R B =
  shift-structural-conceal _ _ _ _
liftPreciseTerm-conceal (future-imprecise W≼W′) V X R B =
  liftPreciseTerm-conceal W≼W′ V X R B

liftImpreciseTerm-conceal : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (V : Term Δᴵ) (X : TyVar Δᴵ) (R B : Ty Δᴵ)
  → liftImpreciseTerm W≼W′ (V ↓ makeConceal X R B)
      ≡ liftImpreciseTerm W≼W′ V
          ↓ makeConceal (liftImpreciseVariable W≼W′ X)
              (liftImpreciseTy W≼W′ R) (liftImpreciseTy W≼W′ B)
liftImpreciseTerm-conceal future-refl V X R B = refl
liftImpreciseTerm-conceal (future-paired W≼W′ r) V X R B
    rewrite liftImpreciseTerm-conceal W≼W′ V X R B =
  shift-structural-conceal _ _ _ _
liftImpreciseTerm-conceal (future-precise W≼W′ r) V X R B =
  liftImpreciseTerm-conceal W≼W′ V X R B
liftImpreciseTerm-conceal (future-alias W≼W′) V X R B =
  liftImpreciseTerm-conceal W≼W′ V X R B
liftImpreciseTerm-conceal (future-imprecise W≼W′) V X R B
    rewrite liftImpreciseTerm-conceal W≼W′ V X R B =
  shift-structural-conceal _ _ _ _

-- Replaced types lift to replaced types.

liftPreciseTy-replace : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (X : TyVar Δᴾ) (R B : Ty Δᴾ)
  → liftPreciseTy W≼W′ (replaceTy X R B)
      ≡ replaceTy (liftPreciseVariable W≼W′ X) (liftPreciseTy W≼W′ R)
          (liftPreciseTy W≼W′ B)
liftPreciseTy-replace future-refl X R B = refl
liftPreciseTy-replace (future-paired W≼W′ r) X R B
    rewrite liftPreciseTy-replace W≼W′ X R B =
  shift-replace (liftPreciseVariable W≼W′ X) (liftPreciseTy W≼W′ R)
    (liftPreciseTy W≼W′ B)
liftPreciseTy-replace (future-precise W≼W′ r) X R B
    rewrite liftPreciseTy-replace W≼W′ X R B =
  shift-replace (liftPreciseVariable W≼W′ X) (liftPreciseTy W≼W′ R)
    (liftPreciseTy W≼W′ B)
liftPreciseTy-replace (future-alias W≼W′) X R B
    rewrite liftPreciseTy-replace W≼W′ X R B =
  shift-replace (liftPreciseVariable W≼W′ X) (liftPreciseTy W≼W′ R)
    (liftPreciseTy W≼W′ B)
liftPreciseTy-replace (future-imprecise W≼W′) X R B =
  liftPreciseTy-replace W≼W′ X R B

liftImpreciseTy-replace : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (X : TyVar Δᴵ) (R B : Ty Δᴵ)
  → liftImpreciseTy W≼W′ (replaceTy X R B)
      ≡ replaceTy (liftImpreciseVariable W≼W′ X)
          (liftImpreciseTy W≼W′ R) (liftImpreciseTy W≼W′ B)
liftImpreciseTy-replace future-refl X R B = refl
liftImpreciseTy-replace (future-paired W≼W′ r) X R B
    rewrite liftImpreciseTy-replace W≼W′ X R B =
  shift-replace (liftImpreciseVariable W≼W′ X) (liftImpreciseTy W≼W′ R)
    (liftImpreciseTy W≼W′ B)
liftImpreciseTy-replace (future-precise W≼W′ r) X R B =
  liftImpreciseTy-replace W≼W′ X R B
liftImpreciseTy-replace (future-alias W≼W′) X R B =
  liftImpreciseTy-replace W≼W′ X R B
liftImpreciseTy-replace (future-imprecise W≼W′) X R B
    rewrite liftImpreciseTy-replace W≼W′ X R B =
  shift-replace (liftImpreciseVariable W≼W′ X) (liftImpreciseTy W≼W′ R)
    (liftImpreciseTy W≼W′ B)

------------------------------------------------------------------------
-- Paired slots and their transport along futures
------------------------------------------------------------------------

-- Paired slots are defined publicly in `LR-narrow.SlotSequence`
-- (beside the slot-conversion sequences) and re-exported here.

-- The lift of a paired entry is a paired entry with lifted fields.

record PairedEntryLift {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {Z : TyVar Δᶜ}
    (a : SemanticAtom (core W) Z) {mode′}
    (e′ : SemanticEntry (core W′) (liftCenterVariable W≼W′ Z) mode′)
    : Set where
  constructor paired-entry-lift
  field
    lifted-atom : SemanticAtom (core W′) (liftCenterVariable W≼W′ Z)
    lifted-entry-eq : e′ ≡ paired-entry lifted-atom
    lifted-precise-variable : preciseVariable lifted-atom
      ≡ liftPreciseVariable W≼W′ (preciseVariable a)
    lifted-imprecise-variable : impreciseVariable lifted-atom
      ≡ liftImpreciseVariable W≼W′ (impreciseVariable a)
    lifted-precise-rep : preciseRep lifted-atom
      ≡ liftPreciseTy W≼W′ (preciseRep a)
    lifted-imprecise-rep : impreciseRep lifted-atom
      ≡ liftImpreciseTy W≼W′ (impreciseRep a)

open PairedEntryLift public

paired-entry-lift-view : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {Z : TyVar Δᶜ} {mode mode′}
    (a : SemanticAtom (core W) Z)
    {e′ : SemanticEntry (core W′) (liftCenterVariable W≼W′ Z) mode′}
  → EntryLift W≼W′ (paired-entry {mode = mode} a) e′
  → PairedEntryLift W≼W′ a e′
paired-entry-lift-view W≼W′ a (lift-paired eqX eqXᴵ eqR eqRᴵ) =
  paired-entry-lift _ refl eqX eqXᴵ eqR eqRᴵ

slot-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (s : PairedSlot W) (W≼W′ : Future W W′)
  → PairedEntryLift W≼W′ (atom s)
      (semanticEntry W′ (liftCenterVariable W≼W′ (center s)))
slot-lift {W = W} {W′ = W′} s W≼W′ =
  paired-entry-lift-view W≼W′ (atom s)
    (subst≡
      (λ e → EntryLift W≼W′ e
        (semanticEntry W′ (liftCenterVariable W≼W′ (center s))))
      (entry-eq s) (entry-future W≼W′ (center s)))

slot-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
  → PairedSlot W → (W≼W′ : Future W W′) → PairedSlot W′
slot-future s W≼W′ = paired-slot
  (liftCenterVariable W≼W′ (center s))
  (lifted-atom (slot-lift s W≼W′))
  (lifted-entry-eq (slot-lift s W≼W′))
  (liftCenterMode-paired W≼W′ (center s) (mode-eq s))

------------------------------------------------------------------------
-- Derivation-restricted avoidance lifts along futures
------------------------------------------------------------------------

-- Lifting a derivation to a future world creates no alias leaves, so
-- avoidance of the lifted center transports (Finding H).

alias-avoid-lift-center : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Aᴾ Aᴵ : Ty Δᶜ}
    (W≼W′ : Future W W′) (c : TyVar Δᶜ)
    (p : I._⊢_⊑_ (impEnv (core W)) Aᴾ Aᴵ)
  → AliasAvoidᵖ c p
  → AliasAvoidᵖ (liftCenterVariable W≼W′ c)
      (liftCenterImprecision W≼W′ p)
alias-avoid-lift-center future-refl c p avoid = avoid
alias-avoid-lift-center (future-paired {W′ = W₁} W≼W′ r) c p avoid =
  alias-avoid-rename {μ′ = I.extᵐ (impEnv (core W₁))} Fin.suc
    fin-suc-injective (shift-star-map {v = I.X⊑X})
    (shift-alias-map {v = I.X⊑X})
    (liftCenterImprecision W≼W′ p)
    (alias-avoid-lift-center W≼W′ c p avoid)
alias-avoid-lift-center (future-precise {W′ = W₁} W≼W′ r) c p avoid =
  alias-avoid-rename {μ′ = I.instᵐ (impEnv (core W₁))} Fin.suc
    fin-suc-injective (shift-star-map {v = I.X⊑★})
    (shift-alias-map {v = I.X⊑★})
    (liftCenterImprecision W≼W′ p)
    (alias-avoid-lift-center W≼W′ c p avoid)
alias-avoid-lift-center (future-alias {W′ = W₁} {rep = rep} W≼W′)
    c p avoid =
  alias-avoid-rename
    {μ′ = I.extendᵐ
      (I.X⊑ᵗ (⇑ᵗ (embedPrecise (core W₁) (＇ rep))))
      (impEnv (core W₁))} Fin.suc
    fin-suc-injective
    (shift-star-map
      {v = I.X⊑ᵗ (⇑ᵗ (embedPrecise (core W₁) (＇ rep)))})
    (shift-alias-map
      {v = I.X⊑ᵗ (⇑ᵗ (embedPrecise (core W₁) (＇ rep)))})
    (liftCenterImprecision W≼W′ p)
    (alias-avoid-lift-center W≼W′ c p avoid)
alias-avoid-lift-center (future-imprecise {W′ = W₁} W≼W′) c p avoid =
  alias-avoid-rename {μ′ = I.instᵐ (impEnv (core W₁))} Fin.suc
    fin-suc-injective (shift-star-map {v = I.X⊑★})
    (shift-alias-map {v = I.X⊑★})
    (liftCenterImprecision W≼W′ p)
    (alias-avoid-lift-center W≼W′ c p avoid)

alias-avoid-lift-body : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Aᴾ Aᴵ : Ty (suc Δᶜ)}
    (W≼W′ : Future W W′) (c : TyVar Δᶜ)
    (p : I._⊢_⊑_ (I.extᵐ (impEnv (core W))) Aᴾ Aᴵ)
  → AliasAvoidᵖ (Fin.suc c) p
  → AliasAvoidᵖ (Fin.suc (liftCenterVariable W≼W′ c))
      (liftCenterBodyImprecision W≼W′ p)
alias-avoid-lift-body future-refl c p avoid = avoid
alias-avoid-lift-body (future-paired {W′ = W₁} W≼W′ r) c p avoid =
  alias-avoid-rename {μ′ = I.extᵐ (I.extᵐ (impEnv (core W₁)))}
    (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (rename-star-map-ext Fin.suc (shift-star-map {v = I.X⊑X}))
    (rename-alias-map-ext Fin.suc (shift-alias-map {v = I.X⊑X}))
    (liftCenterBodyImprecision W≼W′ p)
    (alias-avoid-lift-body W≼W′ c p avoid)
alias-avoid-lift-body (future-precise {W′ = W₁} W≼W′ r) c p avoid =
  alias-avoid-rename {μ′ = I.extᵐ (I.instᵐ (impEnv (core W₁)))}
    (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (rename-star-map-ext Fin.suc (shift-star-map {v = I.X⊑★}))
    (rename-alias-map-ext Fin.suc (shift-alias-map {v = I.X⊑★}))
    (liftCenterBodyImprecision W≼W′ p)
    (alias-avoid-lift-body W≼W′ c p avoid)
alias-avoid-lift-body (future-alias {W′ = W₁} {rep = rep} W≼W′)
    c p avoid =
  alias-avoid-rename
    {μ′ = I.extᵐ (I.extendᵐ
      (I.X⊑ᵗ (⇑ᵗ (embedPrecise (core W₁) (＇ rep))))
      (impEnv (core W₁)))}
    (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (rename-star-map-ext Fin.suc (shift-star-map
      {v = I.X⊑ᵗ (⇑ᵗ (embedPrecise (core W₁) (＇ rep)))}))
    (rename-alias-map-ext Fin.suc (shift-alias-map
      {v = I.X⊑ᵗ (⇑ᵗ (embedPrecise (core W₁) (＇ rep)))}))
    (liftCenterBodyImprecision W≼W′ p)
    (alias-avoid-lift-body W≼W′ c p avoid)
alias-avoid-lift-body (future-imprecise {W′ = W₁} W≼W′) c p avoid =
  alias-avoid-rename {μ′ = I.extᵐ (I.instᵐ (impEnv (core W₁)))}
    (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (rename-star-map-ext Fin.suc (shift-star-map {v = I.X⊑★}))
    (rename-alias-map-ext Fin.suc (shift-alias-map {v = I.X⊑★}))
    (liftCenterBodyImprecision W≼W′ p)
    (alias-avoid-lift-body W≼W′ c p avoid)

alias-avoid-lift-dynamic-body : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Aᴾ Aᴵ : Ty (suc Δᶜ)}
    (W≼W′ : Future W W′) (c : TyVar Δᶜ)
    (p : I._⊢_⊑_ (I.instᵐ (impEnv (core W))) Aᴾ Aᴵ)
  → AliasAvoidᵖ (Fin.suc c) p
  → AliasAvoidᵖ (Fin.suc (liftCenterVariable W≼W′ c))
      (liftCenterDynamicBodyImprecision W≼W′ p)
alias-avoid-lift-dynamic-body future-refl c p avoid = avoid
alias-avoid-lift-dynamic-body (future-paired {W′ = W₁} W≼W′ r)
    c p avoid =
  alias-avoid-rename {μ′ = I.instᵐ (I.extᵐ (impEnv (core W₁)))}
    (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (rename-star-map-inst Fin.suc (shift-star-map {v = I.X⊑X}))
    (rename-alias-map-inst Fin.suc (shift-alias-map {v = I.X⊑X}))
    (liftCenterDynamicBodyImprecision W≼W′ p)
    (alias-avoid-lift-dynamic-body W≼W′ c p avoid)
alias-avoid-lift-dynamic-body (future-precise {W′ = W₁} W≼W′ r)
    c p avoid =
  alias-avoid-rename {μ′ = I.instᵐ (I.instᵐ (impEnv (core W₁)))}
    (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (rename-star-map-inst Fin.suc (shift-star-map {v = I.X⊑★}))
    (rename-alias-map-inst Fin.suc (shift-alias-map {v = I.X⊑★}))
    (liftCenterDynamicBodyImprecision W≼W′ p)
    (alias-avoid-lift-dynamic-body W≼W′ c p avoid)
alias-avoid-lift-dynamic-body (future-alias {W′ = W₁} {rep = rep} W≼W′)
    c p avoid =
  alias-avoid-rename
    {μ′ = I.instᵐ (I.extendᵐ
      (I.X⊑ᵗ (⇑ᵗ (embedPrecise (core W₁) (＇ rep))))
      (impEnv (core W₁)))}
    (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (rename-star-map-inst Fin.suc (shift-star-map
      {v = I.X⊑ᵗ (⇑ᵗ (embedPrecise (core W₁) (＇ rep)))}))
    (rename-alias-map-inst Fin.suc (shift-alias-map
      {v = I.X⊑ᵗ (⇑ᵗ (embedPrecise (core W₁) (＇ rep)))}))
    (liftCenterDynamicBodyImprecision W≼W′ p)
    (alias-avoid-lift-dynamic-body W≼W′ c p avoid)
alias-avoid-lift-dynamic-body (future-imprecise {W′ = W₁} W≼W′)
    c p avoid =
  alias-avoid-rename {μ′ = I.instᵐ (I.instᵐ (impEnv (core W₁)))}
    (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (rename-star-map-inst Fin.suc (shift-star-map {v = I.X⊑★}))
    (rename-alias-map-inst Fin.suc (shift-alias-map {v = I.X⊑★}))
    (liftCenterDynamicBodyImprecision W≼W′ p)
    (alias-avoid-lift-dynamic-body W≼W′ c p avoid)

-- The ★-right-exempt avoidance lifts the same way: lifting creates
-- no alias leaves and every renaming step preserves both branches
-- of the exemption.

alias-avoid★-lift-center : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Aᴾ Aᴵ : Ty Δᶜ}
    (W≼W′ : Future W W′) (c : TyVar Δᶜ)
    (p : I._⊢_⊑_ (impEnv (core W)) Aᴾ Aᴵ)
  → AliasAvoid★ᵖ c p
  → AliasAvoid★ᵖ (liftCenterVariable W≼W′ c)
      (liftCenterImprecision W≼W′ p)
alias-avoid★-lift-center future-refl c p avoid = avoid
alias-avoid★-lift-center (future-paired {W′ = W₁} W≼W′ r) c p avoid =
  alias-avoid★-rename {μ′ = I.extᵐ (impEnv (core W₁))} Fin.suc
    fin-suc-injective (shift-star-map {v = I.X⊑X})
    (shift-alias-map {v = I.X⊑X})
    (liftCenterImprecision W≼W′ p)
    (alias-avoid★-lift-center W≼W′ c p avoid)
alias-avoid★-lift-center (future-precise {W′ = W₁} W≼W′ r) c p avoid =
  alias-avoid★-rename {μ′ = I.instᵐ (impEnv (core W₁))} Fin.suc
    fin-suc-injective (shift-star-map {v = I.X⊑★})
    (shift-alias-map {v = I.X⊑★})
    (liftCenterImprecision W≼W′ p)
    (alias-avoid★-lift-center W≼W′ c p avoid)
alias-avoid★-lift-center (future-alias {W′ = W₁} {rep = rep} W≼W′)
    c p avoid =
  alias-avoid★-rename
    {μ′ = I.extendᵐ
      (I.X⊑ᵗ (⇑ᵗ (embedPrecise (core W₁) (＇ rep))))
      (impEnv (core W₁))} Fin.suc
    fin-suc-injective
    (shift-star-map
      {v = I.X⊑ᵗ (⇑ᵗ (embedPrecise (core W₁) (＇ rep)))})
    (shift-alias-map
      {v = I.X⊑ᵗ (⇑ᵗ (embedPrecise (core W₁) (＇ rep)))})
    (liftCenterImprecision W≼W′ p)
    (alias-avoid★-lift-center W≼W′ c p avoid)
alias-avoid★-lift-center (future-imprecise {W′ = W₁} W≼W′) c p avoid =
  alias-avoid★-rename {μ′ = I.instᵐ (impEnv (core W₁))} Fin.suc
    fin-suc-injective (shift-star-map {v = I.X⊑★})
    (shift-alias-map {v = I.X⊑★})
    (liftCenterImprecision W≼W′ p)
    (alias-avoid★-lift-center W≼W′ c p avoid)

alias-avoid★-lift-body : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Aᴾ Aᴵ : Ty (suc Δᶜ)}
    (W≼W′ : Future W W′) (c : TyVar Δᶜ)
    (p : I._⊢_⊑_ (I.extᵐ (impEnv (core W))) Aᴾ Aᴵ)
  → AliasAvoid★ᵖ (Fin.suc c) p
  → AliasAvoid★ᵖ (Fin.suc (liftCenterVariable W≼W′ c))
      (liftCenterBodyImprecision W≼W′ p)
alias-avoid★-lift-body future-refl c p avoid = avoid
alias-avoid★-lift-body (future-paired {W′ = W₁} W≼W′ r) c p avoid =
  alias-avoid★-rename {μ′ = I.extᵐ (I.extᵐ (impEnv (core W₁)))}
    (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (rename-star-map-ext Fin.suc (shift-star-map {v = I.X⊑X}))
    (rename-alias-map-ext Fin.suc (shift-alias-map {v = I.X⊑X}))
    (liftCenterBodyImprecision W≼W′ p)
    (alias-avoid★-lift-body W≼W′ c p avoid)
alias-avoid★-lift-body (future-precise {W′ = W₁} W≼W′ r) c p avoid =
  alias-avoid★-rename {μ′ = I.extᵐ (I.instᵐ (impEnv (core W₁)))}
    (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (rename-star-map-ext Fin.suc (shift-star-map {v = I.X⊑★}))
    (rename-alias-map-ext Fin.suc (shift-alias-map {v = I.X⊑★}))
    (liftCenterBodyImprecision W≼W′ p)
    (alias-avoid★-lift-body W≼W′ c p avoid)
alias-avoid★-lift-body (future-alias {W′ = W₁} {rep = rep} W≼W′)
    c p avoid =
  alias-avoid★-rename
    {μ′ = I.extᵐ (I.extendᵐ
      (I.X⊑ᵗ (⇑ᵗ (embedPrecise (core W₁) (＇ rep))))
      (impEnv (core W₁)))}
    (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (rename-star-map-ext Fin.suc (shift-star-map
      {v = I.X⊑ᵗ (⇑ᵗ (embedPrecise (core W₁) (＇ rep)))}))
    (rename-alias-map-ext Fin.suc (shift-alias-map
      {v = I.X⊑ᵗ (⇑ᵗ (embedPrecise (core W₁) (＇ rep)))}))
    (liftCenterBodyImprecision W≼W′ p)
    (alias-avoid★-lift-body W≼W′ c p avoid)
alias-avoid★-lift-body (future-imprecise {W′ = W₁} W≼W′) c p avoid =
  alias-avoid★-rename {μ′ = I.extᵐ (I.instᵐ (impEnv (core W₁)))}
    (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (rename-star-map-ext Fin.suc (shift-star-map {v = I.X⊑★}))
    (rename-alias-map-ext Fin.suc (shift-alias-map {v = I.X⊑★}))
    (liftCenterBodyImprecision W≼W′ p)
    (alias-avoid★-lift-body W≼W′ c p avoid)

alias-avoid★-lift-dynamic-body : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {Aᴾ Aᴵ : Ty (suc Δᶜ)}
    (W≼W′ : Future W W′) (c : TyVar Δᶜ)
    (p : I._⊢_⊑_ (I.instᵐ (impEnv (core W))) Aᴾ Aᴵ)
  → AliasAvoid★ᵖ (Fin.suc c) p
  → AliasAvoid★ᵖ (Fin.suc (liftCenterVariable W≼W′ c))
      (liftCenterDynamicBodyImprecision W≼W′ p)
alias-avoid★-lift-dynamic-body future-refl c p avoid = avoid
alias-avoid★-lift-dynamic-body (future-paired {W′ = W₁} W≼W′ r)
    c p avoid =
  alias-avoid★-rename {μ′ = I.instᵐ (I.extᵐ (impEnv (core W₁)))}
    (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (rename-star-map-inst Fin.suc (shift-star-map {v = I.X⊑X}))
    (rename-alias-map-inst Fin.suc (shift-alias-map {v = I.X⊑X}))
    (liftCenterDynamicBodyImprecision W≼W′ p)
    (alias-avoid★-lift-dynamic-body W≼W′ c p avoid)
alias-avoid★-lift-dynamic-body (future-precise {W′ = W₁} W≼W′ r)
    c p avoid =
  alias-avoid★-rename {μ′ = I.instᵐ (I.instᵐ (impEnv (core W₁)))}
    (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (rename-star-map-inst Fin.suc (shift-star-map {v = I.X⊑★}))
    (rename-alias-map-inst Fin.suc (shift-alias-map {v = I.X⊑★}))
    (liftCenterDynamicBodyImprecision W≼W′ p)
    (alias-avoid★-lift-dynamic-body W≼W′ c p avoid)
alias-avoid★-lift-dynamic-body
    (future-alias {W′ = W₁} {rep = rep} W≼W′)
    c p avoid =
  alias-avoid★-rename
    {μ′ = I.instᵐ (I.extendᵐ
      (I.X⊑ᵗ (⇑ᵗ (embedPrecise (core W₁) (＇ rep))))
      (impEnv (core W₁)))}
    (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (rename-star-map-inst Fin.suc (shift-star-map
      {v = I.X⊑ᵗ (⇑ᵗ (embedPrecise (core W₁) (＇ rep)))}))
    (rename-alias-map-inst Fin.suc (shift-alias-map
      {v = I.X⊑ᵗ (⇑ᵗ (embedPrecise (core W₁) (＇ rep)))}))
    (liftCenterDynamicBodyImprecision W≼W′ p)
    (alias-avoid★-lift-dynamic-body W≼W′ c p avoid)
alias-avoid★-lift-dynamic-body (future-imprecise {W′ = W₁} W≼W′)
    c p avoid =
  alias-avoid★-rename {μ′ = I.instᵐ (I.instᵐ (impEnv (core W₁)))}
    (extᵗ Fin.suc) (ext-injective fin-suc-injective)
    (rename-star-map-inst Fin.suc (shift-star-map {v = I.X⊑★}))
    (rename-alias-map-inst Fin.suc (shift-alias-map {v = I.X⊑★}))
    (liftCenterDynamicBodyImprecision W≼W′ p)
    (alias-avoid★-lift-dynamic-body W≼W′ c p avoid)
