module LR-narrow.SlotSequence where

-- File Charter:
--   * Dynamic slots: center variables at mode `X⊑★` whose semantic
--     entry is an unoccupied dynamic atom, with the entry fact stored
--     as a mode-indexed view so that no transport along the mode
--     equality is ever needed.  (Moved here from the proof layer so
--     that the logical relation may quantify over them.)
--   * Slot-conversion sequences: type-indexed lists of reveal and
--     conceal wrappers on the precise side — at dynamic slots, and at
--     arbitrary avoid variables — together with their action on
--     terms.  These index the replacement-closed universal clause
--     families (see REPLACEMENT-CLOSURE-DESIGN.md).

open import Data.Nat using (suc)
import Data.Fin as Fin
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong) renaming (subst to subst≡)

open import Types
open import CastTerms
open import Conversion using (replaceTy; 〖_,_↑_〗; makeConceal)
import Imprecision as I
open import Consistency using (toRenameᵗ)
open import proof.ImprecisionConsistency using (ty-all-injective)
open import proof.LR-narrow.AliasAvoid using
  (AliasAvoidᵖ; AliasAvoid★ᵖ)
open import LR-narrow.World

------------------------------------------------------------------------
-- Dynamic slots
------------------------------------------------------------------------

data IsDynamicEntry {Δᴾ Δᴵ Δᶜ} {W : CoreWorld Δᴾ Δᴵ Δᶜ}
    {Z : TyVar Δᶜ} (a : DynamicSemanticAtom W Z) :
    ∀ {mode} → SemanticEntry W Z mode → Set where
  is-dynamic : IsDynamicEntry a (dynamic-entry a)

record DynamicSlot {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) : Set where
  constructor dynamic-slot
  field
    dcenter : TyVar Δᶜ
    datom : DynamicSemanticAtom (core W) dcenter
    dentry-is : IsDynamicEntry datom (semanticEntry W dcenter)

open DynamicSlot public

is-dynamic-mode : ∀ {Δᴾ Δᴵ Δᶜ} {W : CoreWorld Δᴾ Δᴵ Δᶜ}
    {Z : TyVar Δᶜ} {a : DynamicSemanticAtom W Z} {mode}
    {e : SemanticEntry W Z mode}
  → IsDynamicEntry a e
  → mode ≡ I.X⊑★
is-dynamic-mode is-dynamic = refl

dmode-eq : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    (d : DynamicSlot W)
  → impEnv (core W) (dcenter d) ≡ I.X⊑★
dmode-eq d = is-dynamic-mode (dentry-is d)

dslotXᴾ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
  → DynamicSlot W → TyVar Δᴾ
dslotXᴾ d = dynamicPreciseVariable (datom d)

dslotRᴾ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
  → DynamicSlot W → Ty Δᴾ
dslotRᴾ d = dynamicRep (datom d)

------------------------------------------------------------------------
-- Paired slots
------------------------------------------------------------------------

record PairedSlot {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) : Set where
  constructor paired-slot
  field
    center : TyVar Δᶜ
    atom : SemanticAtom (core W) center
    entry-eq : semanticEntry W center ≡ paired-entry atom
    mode-eq : impEnv (core W) center ≡ I.X⊑X

open PairedSlot public

slotXᴾ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} → PairedSlot W → TyVar Δᴾ
slotXᴾ s = preciseVariable (atom s)

slotXᴵ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} → PairedSlot W → TyVar Δᴵ
slotXᴵ s = impreciseVariable (atom s)

slotRᴾ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} → PairedSlot W → Ty Δᴾ
slotRᴾ s = preciseRep (atom s)

slotRᴵ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} → PairedSlot W → Ty Δᴵ
slotRᴵ s = impreciseRep (atom s)

------------------------------------------------------------------------
-- Alias slots
------------------------------------------------------------------------

-- A mode-indexed view keeps the chosen alias atom definitionally tied to
-- the world's semantic entry, just as `IsDynamicEntry` does for dynamic
-- slots.  This is the precise-only, type-transparent slot used by the
-- universal producer cascades.

data IsAliasSlotEntry {Δᴾ Δᴵ Δᶜ} {W : CoreWorld Δᴾ Δᴵ Δᶜ}
    {Z : TyVar Δᶜ} {T : Ty Δᶜ} (a : AliasSemanticAtom W Z T) :
    ∀ {mode} → SemanticEntry W Z mode → Set where
  is-alias-slot : IsAliasSlotEntry a (alias-entry a)

record AliasSlot {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) : Set where
  constructor alias-slot
  field
    acenter : TyVar Δᶜ
    arepresentative : Ty Δᶜ
    aatom : AliasSemanticAtom (core W) acenter arepresentative
    aentry-is : IsAliasSlotEntry aatom (semanticEntry W acenter)

open AliasSlot public

is-alias-slot-mode : ∀ {Δᴾ Δᴵ Δᶜ} {W : CoreWorld Δᴾ Δᴵ Δᶜ}
    {Z : TyVar Δᶜ} {T : Ty Δᶜ} {a : AliasSemanticAtom W Z T}
    {mode} {e : SemanticEntry W Z mode}
  → IsAliasSlotEntry a e
  → mode ≡ I.X⊑ᵗ T
is-alias-slot-mode is-alias-slot = refl

amode-eq : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    (a : AliasSlot W)
  → impEnv (core W) (acenter a) ≡ I.X⊑ᵗ (arepresentative a)
amode-eq a = is-alias-slot-mode (aentry-is a)

aslotXᴾ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
  → AliasSlot W → TyVar Δᴾ
aslotXᴾ a = aliasPreciseVariable (aatom a)

aslotRᴾ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
  → AliasSlot W → Ty Δᴾ
aslotRᴾ a = aliasRep (aatom a)

fresh-alias-slot : ∀ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (rep : Ty Δᴾ)
  → AliasSlot (aliasBindWorld W rep)
fresh-alias-slot W rep =
  alias-slot Fin.zero (⇑ᵗ (embedPrecise (core W) rep))
    (fresh-alias-semantic-atom (core W) rep) is-alias-slot

------------------------------------------------------------------------
-- Universal slot-conversion wrappers
------------------------------------------------------------------------

-- One precise-side slot conversion at a universal type, indexed by
-- the bodies of the universal types it consumes and produces (the
-- conversion's type argument is always the universal type itself).
-- Indexing by bodies keeps every step universal by construction: a
-- conceal at a dynamic slot whose type argument were not universal
-- could land on a variable type (body the slot variable, universal
-- representative) and leave the family's domain.

-- The clause data of a body pair: the centre imprecision a `∀⊑`
-- clause records for the universal type `` `∀ B `` against `C`.  A
-- wrapper carries the data of the bodies it produces, because a
-- conceal wrapper's target derivation cannot be recovered from its
-- types (un-replacing an imprecision derivation is false; see
-- Finding G in REPLACEMENT-CLOSURE-DESIGN.md), and carrying it
-- uniformly also spares the reveal wrappers from rebuilding theirs.

embedPreciseBody : ∀ {Δᴾ Δᴵ Δᶜ} (W : CoreWorld Δᴾ Δᴵ Δᶜ)
  → Ty (suc Δᴾ) → Ty (suc Δᶜ)
embedPreciseBody W B =
  renameᵗ (extᵗ (toRenameᵗ (preciseEmbedding W))) B

record BodyImprecision {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (B : Ty (suc Δᴾ)) (C : Ty Δᴵ) : Set where
  constructor body-imprecision
  field
    bodyNonvar : NonVar (embedPreciseBody (core W) B)
    bodyOccurs : Fin.zero ∈ᵗ embedPreciseBody (core W) B
    bodyP : I.instᵐ (impEnv (core W)) I.⊢
      embedPreciseBody (core W) B
        ⊑ ⇑ᵗ (embedImprecise (core W) C)

open BodyImprecision public

-- A slot wrapper is a value exactly when its type argument is a
-- function or a universal.  Carrying that shape rather than the
-- value witness keeps the wrappers stable under renaming: a sealing
-- conceal at a variable type would not survive a change of slot.

data UniShape {Δ : TyCtx} : Ty Δ → Set where
  shape-fun : ∀ {A B} → UniShape (A ⇒ B)
  shape-all : ∀ {A} → UniShape (`∀ A)

shape-rename : ∀ {Δ Δ′} (ρ : Δ ⇒ʳ Δ′) {B : Ty Δ}
  → UniShape B → UniShape (renameᵗ ρ B)
shape-rename ρ shape-fun = shape-fun
shape-rename ρ shape-all = shape-all

shape-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) {B : Ty Δᴵ}
  → UniShape B → UniShape (liftImpreciseTy W≼W′ B)
shape-lift future-refl sh = sh
shape-lift (future-paired W≼W′ related) sh =
  shape-rename Fin.suc (shape-lift W≼W′ sh)
shape-lift (future-precise W≼W′ related) sh = shape-lift W≼W′ sh
shape-lift (future-alias W≼W′) sh = shape-lift W≼W′ sh
shape-lift (future-imprecise W≼W′) sh =
  shape-rename Fin.suc (shape-lift W≼W′ sh)

reveal-value-of : ∀ {Δ} {X : TyVar Δ} {R B : Ty Δ}
  → UniShape B → RevealValue 〖 X , R ↑ B 〗
reveal-value-of shape-fun = fun
reveal-value-of shape-all = all

conceal-value-of : ∀ {Δ} {X : TyVar Δ} {R B : Ty Δ}
  → UniShape B → ConcealValue (makeConceal X R B)
conceal-value-of shape-fun = fun
conceal-value-of shape-all = all

-- The clause data of a body pair travels to future worlds, and is
-- transported along equalities of the bodies.

body-imprecision-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {B : Ty (suc Δᴾ)} {C : Ty Δᴵ}
    (W≼W′ : Future W W′)
  → BodyImprecision W B C
  → BodyImprecision W′
      (liftPreciseBody W≼W′ B) (liftImpreciseTy W≼W′ C)
body-imprecision-future {W = W} {W′ = W′} {B = B} {C = C} W≼W′ i =
  body-imprecision
    (subst≡ NonVar (sym bodyᴾ-eq)
      (liftCenterBody-nonvar W≼W′ (bodyNonvar i)))
    (subst≡ (Fin.zero ∈ᵗ_) (sym bodyᴾ-eq)
      (liftCenterBody-occurs W≼W′ (bodyOccurs i)))
    (subst≡
      (λ L → I.instᵐ (impEnv (core W′)) I.⊢ L
        ⊑ ⇑ᵗ (embedImprecise (core W′) (liftImpreciseTy W≼W′ C)))
      (sym bodyᴾ-eq)
      (subst≡
        (λ R → I.instᵐ (impEnv (core W′)) I.⊢
          liftCenterBody W≼W′ (embedPreciseBody (core W) B) ⊑ R)
        (trans (liftCenterBody-shift W≼W′
          (embedImprecise (core W) C))
          (cong ⇑ᵗ (sym (embedImprecise-lift W≼W′ C))))
        (liftCenterDynamicBodyImprecision W≼W′ (bodyP i))))
  where
  bodyᴾ-eq : embedPreciseBody (core W′) (liftPreciseBody W≼W′ B)
      ≡ liftCenterBody W≼W′ (embedPreciseBody (core W) B)
  bodyᴾ-eq = ty-all-injective
    (trans
      (cong (embedPrecise (core W′))
        (sym (liftPreciseTy-universal W≼W′ B)))
      (trans (embedPrecise-lift W≼W′ (`∀ B))
        (liftCenterTy-universal W≼W′ (embedPreciseBody (core W) B))))

-- Building the clause data from a derivation presented with
-- embedding equations, as the `∀⊑` clause supplies it.

body-imprecision-of : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B : Ty (suc Δᴾ)} {C : Ty Δᴵ}
    {Ac : Ty (suc Δᶜ)} {Bc : Ty Δᶜ}
    (nonvar : NonVar Ac) (occurs : Fin.zero ∈ᵗ Ac)
    (p : I.instᵐ (impEnv (core W)) I.⊢ Ac ⊑ ⇑ᵗ Bc)
  → embedPrecise (core W) (`∀ B) ≡ `∀ Ac
  → embedImprecise (core W) C ≡ Bc
  → BodyImprecision W B C
body-imprecision-of {W = W} {B = B} {C = C} {Ac = Ac}
    nonvar occurs p eqᴾ eqᴵ =
  body-imprecision
    (subst≡ NonVar (sym bodyᴾ) nonvar)
    (subst≡ (Fin.zero ∈ᵗ_) (sym bodyᴾ) occurs)
    (subst≡
      (λ L → I.instᵐ (impEnv (core W)) I.⊢ L
        ⊑ ⇑ᵗ (embedImprecise (core W) C))
      (sym bodyᴾ)
      (subst≡
        (λ R → I.instᵐ (impEnv (core W)) I.⊢ _ ⊑ ⇑ᵗ R)
        (sym eqᴵ) p))
  where
  bodyᴾ : embedPreciseBody (core W) B ≡ Ac
  bodyᴾ = ty-all-injective eqᴾ

body-imprecision-subst : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B B′ : Ty (suc Δᴾ)} {C : Ty Δᴵ}
  → B ≡ B′
  → BodyImprecision W B C
  → BodyImprecision W B′ C
body-imprecision-subst refl i = i

body-imprecision-subst-imp : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B : Ty (suc Δᴾ)} {C C′ : Ty Δᴵ}
  → C ≡ C′
  → BodyImprecision W B C
  → BodyImprecision W B C′
body-imprecision-subst-imp refl i = i

data UniWrap {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) :
    Ty (suc Δᴾ) → Ty Δᴵ → Ty (suc Δᴾ) → Ty Δᴵ → Set where
  reveal-paired : (s : PairedSlot W) (B : Ty (suc Δᴾ)) (C : Ty Δᴵ)
    → UniShape C
    → BodyImprecision W
        (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B)
        (replaceTy (slotXᴵ s) (slotRᴵ s) C)
    → ((j : BodyImprecision W B C)
        → AliasAvoidᵖ (Fin.suc (center s)) (bodyP j))
    → UniWrap W B C
        (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B)
        (replaceTy (slotXᴵ s) (slotRᴵ s) C)
  conceal-paired : (s : PairedSlot W) (B : Ty (suc Δᴾ)) (C : Ty Δᴵ)
    → UniShape C
    → BodyImprecision W B C
    → ((j : BodyImprecision W B C)
        → AliasAvoidᵖ (Fin.suc (center s)) (bodyP j))
    → UniWrap W
        (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B)
        (replaceTy (slotXᴵ s) (slotRᴵ s) C)
        B C
  reveal-dyn : (d : DynamicSlot W) (B : Ty (suc Δᴾ)) (C : Ty Δᴵ)
    → BodyImprecision W
        (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B) C
    → UniWrap W B C
        (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B) C
  conceal-dyn : (d : DynamicSlot W) (B : Ty (suc Δᴾ)) (C : Ty Δᴵ)
    → BodyImprecision W B C
    → UniWrap W
        (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B) C
        B C
  reveal-alias-slot : (a : AliasSlot W) (B : Ty (suc Δᴾ)) (C : Ty Δᴵ)
    → BodyImprecision W
        (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B) C
    → UniWrap W B C
        (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B) C
  conceal-alias-slot : (a : AliasSlot W) (B : Ty (suc Δᴾ)) (C : Ty Δᴵ)
    → BodyImprecision W B C
    → UniWrap W
        (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B) C
        B C
  reveal-inert : (s : PairedSlot W) (B : Ty (suc Δᴾ)) (C : Ty Δᴵ)
    → slotXᴾ s ∉ᵗ `∀ B
    → BodyImprecision W B C
    → UniWrap W B C B C
  conceal-inert : (s : PairedSlot W) (B : Ty (suc Δᴾ)) (C : Ty Δᴵ)
    → slotXᴾ s ∉ᵗ `∀ B
    → BodyImprecision W B C
    → UniWrap W B C B C
  reveal-imprecise : (s : PairedSlot W) (B : Ty (suc Δᴾ))
      (C : Ty Δᴵ)
    → UniShape C
    → Fin.suc (center s) ∉ᵗ embedPreciseBody (core W) B
    → BodyImprecision W B (replaceTy (slotXᴵ s) (slotRᴵ s) C)
    → ((j : BodyImprecision W B C)
        → AliasAvoid★ᵖ (Fin.suc (center s)) (bodyP j))
    → UniWrap W B C B (replaceTy (slotXᴵ s) (slotRᴵ s) C)
  conceal-imprecise : (s : PairedSlot W) (B : Ty (suc Δᴾ))
      (C : Ty Δᴵ)
    → UniShape C
    → Fin.suc (center s) ∉ᵗ embedPreciseBody (core W) B
    → BodyImprecision W B C
    → ((j : BodyImprecision W B C)
        → AliasAvoid★ᵖ (Fin.suc (center s)) (bodyP j))
    → UniWrap W B (replaceTy (slotXᴵ s) (slotRᴵ s) C) B C

-- Sequences, innermost wrapper first.

infixr 5 _∷_

data UniWraps {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) :
    Ty (suc Δᴾ) → Ty Δᴵ → Ty (suc Δᴾ) → Ty Δᴵ → Set where
  [] : ∀ {B C} → UniWraps W B C B C
  _∷_ : ∀ {B C B′ C′ B″ C″}
    → UniWrap W B C B′ C′ → UniWraps W B′ C′ B″ C″
    → UniWraps W B C B″ C″

-- The action on the precise endpoint.  The inert wrappers produce
-- terms whose world types are `replaceTy X R (`∀ B)`; the stored
-- non-occurrence witness identifies them with `` `∀ B `` through
-- `replaceTy-absent` where the distinction matters.

wrapTermᴾ₁ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B C B′ C′}
  → UniWrap W B C B′ C′ → Term Δᴾ → Term Δᴾ
wrapTermᴾ₁ (reveal-paired s B C v i av) V =
  V ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B 〗
wrapTermᴾ₁ (conceal-paired s B C v i av) V =
  V ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ B)
wrapTermᴾ₁ (reveal-dyn d B C i) V =
  V ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ `∀ B 〗
wrapTermᴾ₁ (conceal-dyn d B C i) V =
  V ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) (`∀ B)
wrapTermᴾ₁ (reveal-alias-slot a B C i) V =
  V ↑ 〖 aslotXᴾ a , aslotRᴾ a ↑ `∀ B 〗
wrapTermᴾ₁ (conceal-alias-slot a B C i) V =
  V ↓ makeConceal (aslotXᴾ a) (aslotRᴾ a) (`∀ B)
wrapTermᴾ₁ (reveal-inert s B C avoid i) V =
  V ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B 〗
wrapTermᴾ₁ (conceal-inert s B C avoid i) V =
  V ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ B)
wrapTermᴾ₁ (reveal-imprecise s B C sh ∉ᵇ i av) V = V
wrapTermᴾ₁ (conceal-imprecise s B C sh ∉ᵇ i av) V = V

-- The action on the imprecise endpoint: the paired wrappers convert
-- both endpoints, the imprecise-only wrappers convert this endpoint
-- alone, and the dynamic and inert slots have no imprecise occupant,
-- respectively leave the imprecise type alone.

wrapTermᴵ₁ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B C B′ C′}
  → UniWrap W B C B′ C′ → Term Δᴵ → Term Δᴵ
wrapTermᴵ₁ (reveal-paired s B C v i av) V =
  V ↑ 〖 slotXᴵ s , slotRᴵ s ↑ C 〗
wrapTermᴵ₁ (conceal-paired s B C v i av) V =
  V ↓ makeConceal (slotXᴵ s) (slotRᴵ s) C
wrapTermᴵ₁ (reveal-dyn d B C i) V = V
wrapTermᴵ₁ (conceal-dyn d B C i) V = V
wrapTermᴵ₁ (reveal-alias-slot a B C i) V = V
wrapTermᴵ₁ (conceal-alias-slot a B C i) V = V
wrapTermᴵ₁ (reveal-inert s B C avoid i) V = V
wrapTermᴵ₁ (conceal-inert s B C avoid i) V = V
wrapTermᴵ₁ (reveal-imprecise s B C sh ∉ᵇ i av) V =
  V ↑ 〖 slotXᴵ s , slotRᴵ s ↑ C 〗
wrapTermᴵ₁ (conceal-imprecise s B C sh ∉ᵇ i av) V =
  V ↓ makeConceal (slotXᴵ s) (slotRᴵ s) C

wrapTermᴾ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} {B C B′ C′}
  → UniWraps W B C B′ C′ → Term Δᴾ → Term Δᴾ
wrapTermᴾ [] V = V
wrapTermᴾ (w ∷ σ) V = wrapTermᴾ σ (wrapTermᴾ₁ w V)

wrapTermᴵ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} {B C B′ C′}
  → UniWraps W B C B′ C′ → Term Δᴵ → Term Δᴵ
wrapTermᴵ [] V = V
wrapTermᴵ (w ∷ σ) V = wrapTermᴵ σ (wrapTermᴵ₁ w V)

-- Transporting a sequence along equalities of its source types does
-- not change its action on terms.

wrapTermᴾ-subst : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B B′ C B″ C″}
    (eq : B′ ≡ B) (σ : UniWraps W B′ C B″ C″) (V : Term Δᴾ)
  → wrapTermᴾ (subst≡ (λ X → UniWraps W X C B″ C″) eq σ) V
      ≡ wrapTermᴾ σ V
wrapTermᴾ-subst refl σ V = refl

wrapTermᴵ-subst : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B B′ C B″ C″}
    (eq : B′ ≡ B) (σ : UniWraps W B′ C B″ C″) (V : Term Δᴵ)
  → wrapTermᴵ (subst≡ (λ X → UniWraps W X C B″ C″) eq σ) V
      ≡ wrapTermᴵ σ V
wrapTermᴵ-subst refl σ V = refl

wrapTermᴾ-subst-imp : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B C C′ B″ C″}
    (eq : C′ ≡ C) (σ : UniWraps W B C′ B″ C″) (V : Term Δᴾ)
  → wrapTermᴾ (subst≡ (λ Y → UniWraps W B Y B″ C″) eq σ) V
      ≡ wrapTermᴾ σ V
wrapTermᴾ-subst-imp refl σ V = refl

wrapTermᴵ-subst-imp : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B C C′ B″ C″}
    (eq : C′ ≡ C) (σ : UniWraps W B C′ B″ C″) (V : Term Δᴵ)
  → wrapTermᴵ (subst≡ (λ Y → UniWraps W B Y B″ C″) eq σ) V
      ≡ wrapTermᴵ σ V
wrapTermᴵ-subst-imp refl σ V = refl

------------------------------------------------------------------------
-- Two-sided universal slot-conversion wrappers
------------------------------------------------------------------------

-- The `∀⊑∀` analogue of the wrappers above: both endpoint types are
-- universal, so the paired wrappers convert both sides, while the
-- dynamic and inert wrappers convert only the precise side.  The
-- carried clause data is the plain two-sided body imprecision.

embedImpreciseBody : ∀ {Δᴾ Δᴵ Δᶜ} (W : CoreWorld Δᴾ Δᴵ Δᶜ)
  → Ty (suc Δᴵ) → Ty (suc Δᶜ)
embedImpreciseBody W C =
  renameᵗ (extᵗ (toRenameᵗ (impreciseEmbedding W))) C

record BodyImprecisionᵇ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ)
    (B : Ty (suc Δᴾ)) (C : Ty (suc Δᴵ)) : Set where
  constructor body-imprecisionᵇ
  field
    bodyPᵇ : I.extᵐ (impEnv (core W)) I.⊢
      embedPreciseBody (core W) B ⊑ embedImpreciseBody (core W) C

open BodyImprecisionᵇ public

data UniWrapᵇ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) :
    Ty (suc Δᴾ) → Ty (suc Δᴵ) → Ty (suc Δᴾ) → Ty (suc Δᴵ)
    → Set where
  reveal-pairedᵇ : (s : PairedSlot W)
      (B : Ty (suc Δᴾ)) (C : Ty (suc Δᴵ))
    → BodyImprecisionᵇ W
        (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B)
        (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) C)
    → ((j : BodyImprecisionᵇ W B C)
        → AliasAvoidᵖ (Fin.suc (center s)) (bodyPᵇ j))
    → UniWrapᵇ W B C
        (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B)
        (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) C)
  conceal-pairedᵇ : (s : PairedSlot W)
      (B : Ty (suc Δᴾ)) (C : Ty (suc Δᴵ))
    → BodyImprecisionᵇ W B C
    → ((j : BodyImprecisionᵇ W B C)
        → AliasAvoidᵖ (Fin.suc (center s)) (bodyPᵇ j))
    → UniWrapᵇ W
        (replaceTy (Fin.suc (slotXᴾ s)) (⇑ᵗ (slotRᴾ s)) B)
        (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) C)
        B C
  reveal-dynᵇ : (d : DynamicSlot W)
      (B : Ty (suc Δᴾ)) (C : Ty (suc Δᴵ))
    → BodyImprecisionᵇ W
        (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B) C
    → UniWrapᵇ W B C
        (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B) C
  conceal-dynᵇ : (d : DynamicSlot W)
      (B : Ty (suc Δᴾ)) (C : Ty (suc Δᴵ))
    → BodyImprecisionᵇ W B C
    → UniWrapᵇ W
        (replaceTy (Fin.suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B) C
        B C
  reveal-aliasᵇ : (a : AliasSlot W)
      (B : Ty (suc Δᴾ)) (C : Ty (suc Δᴵ))
    → BodyImprecisionᵇ W
        (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B) C
    → UniWrapᵇ W B C
        (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B) C
  conceal-aliasᵇ : (a : AliasSlot W)
      (B : Ty (suc Δᴾ)) (C : Ty (suc Δᴵ))
    → BodyImprecisionᵇ W B C
    → UniWrapᵇ W
        (replaceTy (Fin.suc (aslotXᴾ a)) (⇑ᵗ (aslotRᴾ a)) B) C
        B C
  reveal-inertᵇ : (s : PairedSlot W)
      (B : Ty (suc Δᴾ)) (C : Ty (suc Δᴵ))
    → slotXᴾ s ∉ᵗ `∀ B
    → BodyImprecisionᵇ W B C
    → UniWrapᵇ W B C B C
  conceal-inertᵇ : (s : PairedSlot W)
      (B : Ty (suc Δᴾ)) (C : Ty (suc Δᴵ))
    → slotXᴾ s ∉ᵗ `∀ B
    → BodyImprecisionᵇ W B C
    → UniWrapᵇ W B C B C
  reveal-impreciseᵇ : (s : PairedSlot W)
      (B : Ty (suc Δᴾ)) (C : Ty (suc Δᴵ))
    → Fin.suc (center s) ∉ᵗ embedPreciseBody (core W) B
    → BodyImprecisionᵇ W B
        (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) C)
    → ((j : BodyImprecisionᵇ W B C)
        → AliasAvoid★ᵖ (Fin.suc (center s)) (bodyPᵇ j))
    → UniWrapᵇ W B C B
        (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) C)
  conceal-impreciseᵇ : (s : PairedSlot W)
      (B : Ty (suc Δᴾ)) (C : Ty (suc Δᴵ))
    → Fin.suc (center s) ∉ᵗ embedPreciseBody (core W) B
    → BodyImprecisionᵇ W B C
    → ((j : BodyImprecisionᵇ W B C)
        → AliasAvoid★ᵖ (Fin.suc (center s)) (bodyPᵇ j))
    → UniWrapᵇ W B
        (replaceTy (Fin.suc (slotXᴵ s)) (⇑ᵗ (slotRᴵ s)) C)
        B C

data UniWrapsᵇ {Δᴾ Δᴵ Δᶜ} (W : World Δᴾ Δᴵ Δᶜ) :
    Ty (suc Δᴾ) → Ty (suc Δᴵ) → Ty (suc Δᴾ) → Ty (suc Δᴵ)
    → Set where
  [] : ∀ {B C} → UniWrapsᵇ W B C B C
  _∷_ : ∀ {B C B′ C′ B″ C″}
    → UniWrapᵇ W B C B′ C′ → UniWrapsᵇ W B′ C′ B″ C″
    → UniWrapsᵇ W B C B″ C″

wrapTermᴾᵇ₁ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B C B′ C′}
  → UniWrapᵇ W B C B′ C′ → Term Δᴾ → Term Δᴾ
wrapTermᴾᵇ₁ (reveal-pairedᵇ s B C i av) V =
  V ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B 〗
wrapTermᴾᵇ₁ (conceal-pairedᵇ s B C i av) V =
  V ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ B)
wrapTermᴾᵇ₁ (reveal-dynᵇ d B C i) V =
  V ↑ 〖 dslotXᴾ d , dslotRᴾ d ↑ `∀ B 〗
wrapTermᴾᵇ₁ (conceal-dynᵇ d B C i) V =
  V ↓ makeConceal (dslotXᴾ d) (dslotRᴾ d) (`∀ B)
wrapTermᴾᵇ₁ (reveal-aliasᵇ a B C i) V =
  V ↑ 〖 aslotXᴾ a , aslotRᴾ a ↑ `∀ B 〗
wrapTermᴾᵇ₁ (conceal-aliasᵇ a B C i) V =
  V ↓ makeConceal (aslotXᴾ a) (aslotRᴾ a) (`∀ B)
wrapTermᴾᵇ₁ (reveal-inertᵇ s B C avoid i) V =
  V ↑ 〖 slotXᴾ s , slotRᴾ s ↑ `∀ B 〗
wrapTermᴾᵇ₁ (conceal-inertᵇ s B C avoid i) V =
  V ↓ makeConceal (slotXᴾ s) (slotRᴾ s) (`∀ B)
wrapTermᴾᵇ₁ (reveal-impreciseᵇ s B C no-occur i av) V = V
wrapTermᴾᵇ₁ (conceal-impreciseᵇ s B C no-occur i av) V = V

wrapTermᴵᵇ₁ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B C B′ C′}
  → UniWrapᵇ W B C B′ C′ → Term Δᴵ → Term Δᴵ
wrapTermᴵᵇ₁ (reveal-pairedᵇ s B C i av) V =
  V ↑ 〖 slotXᴵ s , slotRᴵ s ↑ `∀ C 〗
wrapTermᴵᵇ₁ (conceal-pairedᵇ s B C i av) V =
  V ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (`∀ C)
wrapTermᴵᵇ₁ (reveal-dynᵇ d B C i) V = V
wrapTermᴵᵇ₁ (conceal-dynᵇ d B C i) V = V
wrapTermᴵᵇ₁ (reveal-aliasᵇ a B C i) V = V
wrapTermᴵᵇ₁ (conceal-aliasᵇ a B C i) V = V
wrapTermᴵᵇ₁ (reveal-inertᵇ s B C avoid i) V = V
wrapTermᴵᵇ₁ (conceal-inertᵇ s B C avoid i) V = V
wrapTermᴵᵇ₁ (reveal-impreciseᵇ s B C no-occur i av) V =
  V ↑ 〖 slotXᴵ s , slotRᴵ s ↑ `∀ C 〗
wrapTermᴵᵇ₁ (conceal-impreciseᵇ s B C no-occur i av) V =
  V ↓ makeConceal (slotXᴵ s) (slotRᴵ s) (`∀ C)

wrapTermᴾᵇ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} {B C B′ C′}
  → UniWrapsᵇ W B C B′ C′ → Term Δᴾ → Term Δᴾ
wrapTermᴾᵇ [] V = V
wrapTermᴾᵇ (w ∷ σ) V = wrapTermᴾᵇ σ (wrapTermᴾᵇ₁ w V)

wrapTermᴵᵇ : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ} {B C B′ C′}
  → UniWrapsᵇ W B C B′ C′ → Term Δᴵ → Term Δᴵ
wrapTermᴵᵇ [] V = V
wrapTermᴵᵇ (w ∷ σ) V = wrapTermᴵᵇ σ (wrapTermᴵᵇ₁ w V)

wrapTermᴾᵇ-subst : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B B′ C B″ C″}
    (eq : B′ ≡ B) (σ : UniWrapsᵇ W B′ C B″ C″) (V : Term Δᴾ)
  → wrapTermᴾᵇ (subst≡ (λ X → UniWrapsᵇ W X C B″ C″) eq σ) V
      ≡ wrapTermᴾᵇ σ V
wrapTermᴾᵇ-subst refl σ V = refl

wrapTermᴵᵇ-subst : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B B′ C B″ C″}
    (eq : B′ ≡ B) (σ : UniWrapsᵇ W B′ C B″ C″) (V : Term Δᴵ)
  → wrapTermᴵᵇ (subst≡ (λ X → UniWrapsᵇ W X C B″ C″) eq σ) V
      ≡ wrapTermᴵᵇ σ V
wrapTermᴵᵇ-subst refl σ V = refl

wrapTermᴾᵇ-subst-imp : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B C C′ B″ C″}
    (eq : C′ ≡ C) (σ : UniWrapsᵇ W B C′ B″ C″) (V : Term Δᴾ)
  → wrapTermᴾᵇ (subst≡ (λ Y → UniWrapsᵇ W B Y B″ C″) eq σ) V
      ≡ wrapTermᴾᵇ σ V
wrapTermᴾᵇ-subst-imp refl σ V = refl

wrapTermᴵᵇ-subst-imp : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B C C′ B″ C″}
    (eq : C′ ≡ C) (σ : UniWrapsᵇ W B C′ B″ C″) (V : Term Δᴵ)
  → wrapTermᴵᵇ (subst≡ (λ Y → UniWrapsᵇ W B Y B″ C″) eq σ) V
      ≡ wrapTermᴵᵇ σ V
wrapTermᴵᵇ-subst-imp refl σ V = refl

-- The two-sided clause data travels to future worlds and is
-- transported along body equalities, and is built from a derivation
-- presented with embedding equations.

embedImpreciseBody-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (C : Ty (suc Δᴵ))
  → embedImpreciseBody (core W′) (liftImpreciseBody W≼W′ C)
      ≡ liftCenterBody W≼W′ (embedImpreciseBody (core W) C)
embedImpreciseBody-lift {W = W} {W′ = W′} W≼W′ C =
  ty-all-injective
    (trans
      (cong (embedImprecise (core W′))
        (sym (liftImpreciseTy-universal W≼W′ C)))
      (trans (embedImprecise-lift W≼W′ (`∀ C))
        (liftCenterTy-universal W≼W′
          (embedImpreciseBody (core W) C))))

embedPreciseBody-lift : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    (W≼W′ : Future W W′) (B : Ty (suc Δᴾ))
  → embedPreciseBody (core W′) (liftPreciseBody W≼W′ B)
      ≡ liftCenterBody W≼W′ (embedPreciseBody (core W) B)
embedPreciseBody-lift {W = W} {W′ = W′} W≼W′ B =
  ty-all-injective
    (trans
      (cong (embedPrecise (core W′))
        (sym (liftPreciseTy-universal W≼W′ B)))
      (trans (embedPrecise-lift W≼W′ (`∀ B))
        (liftCenterTy-universal W≼W′
          (embedPreciseBody (core W) B))))

body-imprecisionᵇ-future : ∀ {Δᴾ Δᴵ Δᶜ Δᴾ′ Δᴵ′ Δᶜ′}
    {W : World Δᴾ Δᴵ Δᶜ} {W′ : World Δᴾ′ Δᴵ′ Δᶜ′}
    {B : Ty (suc Δᴾ)} {C : Ty (suc Δᴵ)}
    (W≼W′ : Future W W′)
  → BodyImprecisionᵇ W B C
  → BodyImprecisionᵇ W′
      (liftPreciseBody W≼W′ B) (liftImpreciseBody W≼W′ C)
body-imprecisionᵇ-future {W = W} {W′ = W′} {B = B} {C = C} W≼W′ i =
  body-imprecisionᵇ
    (subst≡
      (λ L → I.extᵐ (impEnv (core W′)) I.⊢ L
        ⊑ embedImpreciseBody (core W′) (liftImpreciseBody W≼W′ C))
      (sym (embedPreciseBody-lift W≼W′ B))
      (subst≡
        (λ R → I.extᵐ (impEnv (core W′)) I.⊢
          liftCenterBody W≼W′ (embedPreciseBody (core W) B) ⊑ R)
        (sym (embedImpreciseBody-lift W≼W′ C))
        (liftCenterBodyImprecision W≼W′ (bodyPᵇ i))))

body-imprecisionᵇ-subst : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B B′ : Ty (suc Δᴾ)} {C : Ty (suc Δᴵ)}
  → B ≡ B′
  → BodyImprecisionᵇ W B C
  → BodyImprecisionᵇ W B′ C
body-imprecisionᵇ-subst refl i = i

body-imprecisionᵇ-subst-imp : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B : Ty (suc Δᴾ)} {C C′ : Ty (suc Δᴵ)}
  → C ≡ C′
  → BodyImprecisionᵇ W B C
  → BodyImprecisionᵇ W B C′
body-imprecisionᵇ-subst-imp refl i = i

body-imprecisionᵇ-of : ∀ {Δᴾ Δᴵ Δᶜ} {W : World Δᴾ Δᴵ Δᶜ}
    {B : Ty (suc Δᴾ)} {C : Ty (suc Δᴵ)}
    {Aᴾc Aᴵc : Ty (suc Δᶜ)}
    (p : I.extᵐ (impEnv (core W)) I.⊢ Aᴾc ⊑ Aᴵc)
  → embedPrecise (core W) (`∀ B) ≡ `∀ Aᴾc
  → embedImprecise (core W) (`∀ C) ≡ `∀ Aᴵc
  → BodyImprecisionᵇ W B C
body-imprecisionᵇ-of {W = W} {B = B} {C = C} p eqᴾ eqᴵ =
  body-imprecisionᵇ
    (subst≡
      (λ L → I.extᵐ (impEnv (core W)) I.⊢ L
        ⊑ embedImpreciseBody (core W) C)
      (sym (ty-all-injective eqᴾ))
      (subst≡
        (λ R → I.extᵐ (impEnv (core W)) I.⊢ _ ⊑ R)
        (sym (ty-all-injective eqᴵ)) p))
