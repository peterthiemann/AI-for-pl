module proof.LR-narrow.ScopeRebase where

-- File Charter:
--   * Restricts semantic types to new physical roots without changing terms.
--   * Grafting recovers the old scopes, stores, and allocation histories.
--   * Transfers observations and arrow behavior in both directions; no
--     evaluation-equivariance or compatibility assumptions are introduced.
--   * Visible-name selection is separate from physical re-rooting.

open import Data.List using ([])
open import Data.Nat using (_<_; _∸_)
open import Data.Product using (_×_; _,_; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans)
  renaming (subst to subst≡; subst₂ to subst₂≡)

open import Types
open import TyStore
open import CastTerms
open import Conversion
import Eval as E
open import Interpreter
open import LR-narrow.Computation using (BlamesFrom)
open import proof.LR-narrow.Application using
  (return-store-reindex; blame-store-reindex)
open import proof.LR-narrow.PhysicalScope
open import proof.LR-narrow.ScopedBehavior

module Rebase {Δᴵ₀ Δᴾ₀ Δᴵ Δᴾ} {Σᴵ₀ : TyStore Δᴵ₀} {Σᴾ₀ : TyStore Δᴾ₀}
    (S : PhysicalScope Σᴵ₀ Δᴵ) (T : PhysicalScope Σᴾ₀ Δᴾ) where

  module Old = Model Σᴵ₀ Σᴾ₀
  module New = Model (scopeStore S) (scopeStore T)

  rebase : Old.ScopedType → New.ScopedType
  rebase A = record
    { impreciseTy = scopeTy S (Old.impreciseTy A)
    ; preciseTy = scopeTy T (Old.preciseTy A)
    ; related = λ P Q k → Old.related A (graft S P) (graft T Q) k
    ; imprecise-value = Old.imprecise-value A
    ; precise-value = Old.precise-value A
    ; imprecise-typed = λ { {S = P} {U = U} r →
        subst₂≡ (λ Σ B → ⟨ _ , Σ , [] ⟩ ⊢ U ⦂ B)
          (graft-store S P) (graft-type S P (Old.impreciseTy A))
          (Old.imprecise-typed A r) }
    ; precise-typed = λ { {T = Q} {V = V} r →
        subst₂≡ (λ Σ B → ⟨ _ , Σ , [] ⟩ ⊢ V ⦂ B)
          (graft-store T Q) (graft-type T Q (Old.preciseTy A))
          (Old.precise-typed A r) }
    ; downward = Old.downward A
    ; future-closed = λ { {U = U} {V = V} p q r →
        subst₂≡ (Old.related A _ _ _)
          (graft-lift S p U) (graft-lift T q V)
          (Old.future-closed A (graft-future S p) (graft-future T q) r) }
    }

  observed-to : ∀ {Δᴵ′ Δᴾ′} (A : Old.ScopedType)
      {P : PhysicalScope (scopeStore S) Δᴵ′}
      {Q : PhysicalScope (scopeStore T) Δᴾ′} {k M N}
    → Old.ObservedComputations A (graft S P) (graft T Q) k M N
    → New.ObservedComputations (rebase A) P Q k M N
  observed-to A {P} {Q} {k} {M} {N} c = record
    { forward-return = forward
    ; backward-return = backward
    ; forward-blame = blames
    }
    where
    forward : ∀ {n} {out : E.EvalResult M}
      → n < k → interpretFrom (scopeStore P) n M ≡ returned out
      → (∃[ m ] ∃[ out′ ] (interpretFrom (scopeStore Q) m N ≡ returned out′)
          × New.related (rebase A) (advance P (E.changes out))
              (advance Q (E.changes out′)) (k ∸ n) (E.term out) (E.term out′))
        ⊎ (∃[ m ] BlamesFrom (scopeStore Q) m N)
    forward {n} n<k ret with Old.ObservedComputations.forward-return c n<k
      (return-store-reindex {gas = n} (graft-store S P) ret)
    forward {n} {out} n<k ret | inj₁ (m , out′ , ret′ , r) = inj₁
      (m , out′ , return-store-reindex {gas = m} (sym (graft-store T Q)) ret′ ,
        subst₂≡ (λ P′ Q′ → Old.related A P′ Q′ (k ∸ n)
            (E.term out) (E.term out′))
          (graft-advance S P (E.changes out))
          (graft-advance T Q (E.changes out′)) r)
    forward n<k ret | inj₂ (m , blameN) =
      inj₂ (m , blame-store-reindex {gas = m} (sym (graft-store T Q)) blameN)

    backward : ∀ {n} {out : E.EvalResult N}
      → n < k → interpretFrom (scopeStore Q) n N ≡ returned out
      → ∃[ m ] ∃[ out′ ] (interpretFrom (scopeStore P) m M ≡ returned out′)
          × New.related (rebase A) (advance P (E.changes out′))
              (advance Q (E.changes out)) (k ∸ n) (E.term out′) (E.term out)
    backward {n} n<k ret with Old.ObservedComputations.backward-return c n<k
      (return-store-reindex {gas = n} (graft-store T Q) ret)
    backward {n} {out} n<k ret | m , out′ , ret′ , r =
      m , out′ , return-store-reindex {gas = m} (sym (graft-store S P)) ret′ ,
      subst₂≡ (λ P′ Q′ → Old.related A P′ Q′ (k ∸ n)
          (E.term out′) (E.term out))
        (graft-advance S P (E.changes out′))
        (graft-advance T Q (E.changes out)) r

    blames : ∀ {n} → n < k → BlamesFrom (scopeStore P) n M
      → ∃[ m ] BlamesFrom (scopeStore Q) m N
    blames {n} n<k blameM with Old.ObservedComputations.forward-blame c n<k
      (blame-store-reindex {gas = n} (graft-store S P) blameM)
    blames n<k blameM | m , blameN =
      m , blame-store-reindex {gas = m} (sym (graft-store T Q)) blameN

  observed-from : ∀ {Δᴵ′ Δᴾ′} (A : Old.ScopedType)
      {P : PhysicalScope (scopeStore S) Δᴵ′}
      {Q : PhysicalScope (scopeStore T) Δᴾ′} {k M N}
    → New.ObservedComputations (rebase A) P Q k M N
    → Old.ObservedComputations A (graft S P) (graft T Q) k M N
  observed-from A {P} {Q} {k} {M} {N} c = record
    { forward-return = forward
    ; backward-return = backward
    ; forward-blame = blames
    }
    where
    forward : ∀ {n} {out : E.EvalResult M}
      → n < k → interpretFrom (scopeStore (graft S P)) n M ≡ returned out
      → (∃[ m ] ∃[ out′ ]
          (interpretFrom (scopeStore (graft T Q)) m N ≡ returned out′)
          × Old.related A (advance (graft S P) (E.changes out))
              (advance (graft T Q) (E.changes out′))
              (k ∸ n) (E.term out) (E.term out′))
        ⊎ (∃[ m ] BlamesFrom (scopeStore (graft T Q)) m N)
    forward {n} n<k ret with New.ObservedComputations.forward-return c n<k
      (return-store-reindex {gas = n} (sym (graft-store S P)) ret)
    forward {n} {out} n<k ret | inj₁ (m , out′ , ret′ , r) = inj₁
      (m , out′ , return-store-reindex {gas = m} (graft-store T Q) ret′ ,
        subst₂≡ (λ P′ Q′ → Old.related A P′ Q′ (k ∸ n)
            (E.term out) (E.term out′))
          (sym (graft-advance S P (E.changes out)))
          (sym (graft-advance T Q (E.changes out′))) r)
    forward n<k ret | inj₂ (m , blameN) =
      inj₂ (m , blame-store-reindex {gas = m} (graft-store T Q) blameN)

    backward : ∀ {n} {out : E.EvalResult N}
      → n < k → interpretFrom (scopeStore (graft T Q)) n N ≡ returned out
      → ∃[ m ] ∃[ out′ ]
          (interpretFrom (scopeStore (graft S P)) m M ≡ returned out′)
          × Old.related A (advance (graft S P) (E.changes out′))
              (advance (graft T Q) (E.changes out))
              (k ∸ n) (E.term out′) (E.term out)
    backward {n} n<k ret with New.ObservedComputations.backward-return c n<k
      (return-store-reindex {gas = n} (sym (graft-store T Q)) ret)
    backward {n} {out} n<k ret | m , out′ , ret′ , r =
      m , out′ , return-store-reindex {gas = m} (graft-store S P) ret′ ,
      subst₂≡ (λ P′ Q′ → Old.related A P′ Q′ (k ∸ n)
          (E.term out′) (E.term out))
        (sym (graft-advance S P (E.changes out′)))
        (sym (graft-advance T Q (E.changes out))) r

    blames : ∀ {n} → n < k → BlamesFrom (scopeStore (graft S P)) n M
      → ∃[ m ] BlamesFrom (scopeStore (graft T Q)) m N
    blames {n} n<k blameM with New.ObservedComputations.forward-blame c n<k
      (blame-store-reindex {gas = n} (sym (graft-store S P)) blameM)
    blames n<k blameM | m , blameN =
      m , blame-store-reindex {gas = m} (graft-store T Q) blameN

  computations-to : ∀ {Δᴵ′ Δᴾ′} (A : Old.ScopedType)
      {P : PhysicalScope (scopeStore S) Δᴵ′}
      {Q : PhysicalScope (scopeStore T) Δᴾ′} {k M N}
    → Old.ScopedComputations A (graft S P) (graft T Q) k M N
    → New.ScopedComputations (rebase A) P Q k M N
  computations-to A {k = k} {M} {N} c p q =
    subst₂≡ (New.ObservedComputations (rebase A) _ _ k)
      (graft-lift S p M) (graft-lift T q N)
      (observed-to A (c (graft-future S p) (graft-future T q)))

  computations-from : ∀ {Δᴵ′ Δᴾ′} (A : Old.ScopedType)
      {P : PhysicalScope (scopeStore S) Δᴵ′}
      {Q : PhysicalScope (scopeStore T) Δᴾ′} {k M N}
    → New.ScopedComputations (rebase A) P Q k M N
    → Old.ScopedComputations A (graft S P) (graft T Q) k M N
  computations-from A {P} {Q} c p q
      with factor-future S P p | factor-future T Q q
  computations-from A {P} {Q} {k} {M} {N} c p q
      | P′ , p′ , refl | Q′ , q′ , refl =
    subst₂≡ (Old.ObservedComputations A (graft S P′) (graft T Q′) k)
      (sym (graft-lift S p′ M)) (sym (graft-lift T q′ N))
      (observed-from A (c p′ q′))

  -- These are equivalences of the constructed relations, not just closure
  -- of their invariants. In particular, arrow tests are neither added nor
  -- removed by re-rooting: factor-future recovers every old future.

  arrow-to : ∀ {Δᴵ′ Δᴾ′} (A B : Old.ScopedType)
      {P : PhysicalScope (scopeStore S) Δᴵ′}
      {Q : PhysicalScope (scopeStore T) Δᴾ′} {k F G}
    → New.related (rebase (Old.arrow A B)) P Q k F G
    → New.related (New.arrow (rebase A) (rebase B)) P Q k F G
  arrow-to A B {P} {Q} {k} {F} {G} r = New.arrow-values
    (Old.ArrowValues.functionᴵ-value r) (Old.ArrowValues.functionᴾ-value r)
    (subst≡ (λ C → ⟨ _ , scopeStore P , [] ⟩ ⊢ F ⦂ C)
      (cong (scopeTy P) (scope-arrow S (Old.impreciseTy A) (Old.impreciseTy B)))
      (New.imprecise-typed (rebase (Old.arrow A B)) r))
    (subst≡ (λ C → ⟨ _ , scopeStore Q , [] ⟩ ⊢ G ⦂ C)
      (cong (scopeTy Q) (scope-arrow T (Old.preciseTy A) (Old.preciseTy B)))
      (New.precise-typed (rebase (Old.arrow A B)) r))
    (λ { {j = j} {U = U} {V = V} p q j<k args →
      subst₂≡ (New.ObservedComputations (rebase B) _ _ j)
        (cong (_· U) (graft-lift S p F))
        (cong (_· V) (graft-lift T q G))
        (observed-to B (Old.ArrowValues.call r
          (graft-future S p) (graft-future T q) j<k args)) })

  arrow-from : ∀ {Δᴵ′ Δᴾ′} (A B : Old.ScopedType)
      {P : PhysicalScope (scopeStore S) Δᴵ′}
      {Q : PhysicalScope (scopeStore T) Δᴾ′} {k F G}
    → New.related (New.arrow (rebase A) (rebase B)) P Q k F G
    → New.related (rebase (Old.arrow A B)) P Q k F G
  arrow-from A B {P} {Q} {k} {F} {G} r = Old.arrow-values
    (New.ArrowValues.functionᴵ-value r) (New.ArrowValues.functionᴾ-value r)
    (subst₂≡ (λ Σ C → ⟨ _ , Σ , [] ⟩ ⊢ F ⦂ C) (sym (graft-store S P))
      (trans
        (cong (scopeTy P)
          (sym (scope-arrow S (Old.impreciseTy A) (Old.impreciseTy B))))
        (sym (graft-type S P (Old.impreciseTy A ⇒ Old.impreciseTy B))))
      (New.ArrowValues.functionᴵ-typed r))
    (subst₂≡ (λ Σ C → ⟨ _ , Σ , [] ⟩ ⊢ G ⦂ C) (sym (graft-store T Q))
      (trans
        (cong (scopeTy Q)
          (sym (scope-arrow T (Old.preciseTy A) (Old.preciseTy B))))
        (sym (graft-type T Q (Old.preciseTy A ⇒ Old.preciseTy B))))
      (New.ArrowValues.functionᴾ-typed r)) call
    where
    call : ∀ {Δᴵ″ Δᴾ″} {P′ : PhysicalScope Σᴵ₀ Δᴵ″}
        {Q′ : PhysicalScope Σᴾ₀ Δᴾ″} {j U V}
      → (p : ScopeFuture (graft S P) P′) → (q : ScopeFuture (graft T Q) Q′)
      → j < k → Old.related A P′ Q′ j U V
      → Old.ObservedComputations B P′ Q′ j (liftTerm p F · U) (liftTerm q G · V)
    call p q j<k args with factor-future S P p | factor-future T Q q
    call {j = j} {U} {V} p q j<k args | P″ , p′ , refl | Q″ , q′ , refl =
      subst₂≡ (Old.ObservedComputations B (graft S P″) (graft T Q″) j)
        (cong (_· U) (sym (graft-lift S p′ F)))
        (cong (_· V) (sym (graft-lift T q′ G)))
        (observed-from B (New.ArrowValues.call r p′ q′ j<k args))

  natural-relation : ∀ {Δᴵ′ Δᴾ′}
      (P : PhysicalScope (scopeStore S) Δᴵ′)
      (Q : PhysicalScope (scopeStore T) Δᴾ′) k U V
    → New.related (rebase Old.natural) P Q k U V
        ≡ New.related New.natural P Q k U V
  natural-relation P Q k U V = refl

  nominal-relation : ∀ {Δᴵ′ Δᴾ′} (A : Old.ScopedType) X Y
      (entryX : Σᴵ₀ ∋ X ⦂ Old.impreciseTy A)
      (entryY : Σᴾ₀ ∋ Y ⦂ Old.preciseTy A)
      (P : PhysicalScope (scopeStore S) Δᴵ′)
      (Q : PhysicalScope (scopeStore T) Δᴾ′) k U V
    → New.related (rebase (Old.nominal A X Y entryX entryY)) P Q k U V
        ≡ New.related (New.nominal (rebase A) (scopeVar S X) (scopeVar T Y)
            (scope-entry S entryX) (scope-entry T entryY)) P Q k U V
  nominal-relation A X Y entryX entryY P Q k U V
      rewrite graft-variable S P X | graft-variable T Q Y
        | graft-type S P (Old.impreciseTy A)
        | graft-type T Q (Old.preciseTy A) = refl
