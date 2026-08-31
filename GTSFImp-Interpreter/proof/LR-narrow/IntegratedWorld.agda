module proof.LR-narrow.IntegratedWorld where

-- File Charter:
--   * Experimental world-indexed dynamic-name layer for an integrated
--     A+B+C′ model. This file does not change the live LR or CTI.
--   * Worlds are small finite syntax indexed by actual independently growing
--     physical scopes. They track explicit matched nominal capabilities and
--     target-only precise capabilities.
--   * Payload typing/evidence is intentionally left to the model relation
--     that consumes this world layer; matching is by capability membership,
--     not by representation equality.

open import Data.Empty using (⊥)
open import Data.Nat using (suc)
import Data.Fin as Fin
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym) renaming (subst to subst≡)

open import Types
open import TyStore
import Reduction as R
open import proof.LR-narrow.PhysicalScope

module Worlds {ΔI0 ΔP0} (ΣI0 : TyStore ΔI0) (ΣP0 : TyStore ΔP0) where

  mutual
    data World : ∀ {ΔI ΔP}
      → PhysicalScope ΣI0 ΔI → PhysicalScope ΣP0 ΔP → Set where
      empty : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP}
        → World S T
      extend-privateI : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP}
        → (W : World S T) → (A : Ty ΔI) → World (allocate S A) T
      extend-privateP : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP}
        → (W : World S T) → (A : Ty ΔP) → World S (allocate T A)
      extend-paired : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP}
        → (W : World S T) → (A : Ty ΔI) → (B : Ty ΔP)
        → World (allocate S A) (allocate T B)
      extend-only : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP}
        → (W : World S T) → (B : Ty ΔP) → World S (allocate T B)

    data Matched : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
        {T : PhysicalScope ΣP0 ΔP}
      → World S T → TyVar ΔI → TyVar ΔP → Set where
      old-privateI : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP} {W : World S T} {A X Y}
        → Matched W X Y → Matched (extend-privateI W A) (Fin.suc X) Y
      old-privateP : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP} {W : World S T} {A X Y}
        → Matched W X Y → Matched (extend-privateP W A) X (Fin.suc Y)
      new-paired : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP} {W : World S T} {A B}
        → Matched (extend-paired W A B) Fin.zero Fin.zero
      old-paired : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP} {W : World S T} {A B X Y}
        → Matched W X Y
        → Matched (extend-paired W A B) (Fin.suc X) (Fin.suc Y)
      old-only-match : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP} {W : World S T} {B X Y}
        → Matched W X Y → Matched (extend-only W B) X (Fin.suc Y)

    data PreciseOnly : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
        {T : PhysicalScope ΣP0 ΔP}
      → World S T → TyVar ΔP → Set where
      old-only-privateP : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP} {W : World S T} {A Y}
        → PreciseOnly W Y → PreciseOnly (extend-privateP W A) (Fin.suc Y)
      old-only-privateI : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP} {W : World S T} {A Y}
        → PreciseOnly W Y → PreciseOnly (extend-privateI W A) Y
      old-only-paired : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP} {W : World S T} {A B Y}
        → PreciseOnly W Y → PreciseOnly (extend-paired W A B) (Fin.suc Y)
      new-precise-only : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP} {W : World S T} {B}
        → PreciseOnly (extend-only W B) Fin.zero
      old-precise-only : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
          {T : PhysicalScope ΣP0 ΔP} {W : World S T} {B Y}
        → PreciseOnly W Y → PreciseOnly (extend-only W B) (Fin.suc Y)

  matched-left-inj : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
      {T : PhysicalScope ΣP0 ΔP} {W : World S T} {X Y Y′}
    → Matched W X Y → Matched W X Y′ → Y ≡ Y′
  matched-left-inj (old-privateI p) (old-privateI q) =
    matched-left-inj p q
  matched-left-inj (old-privateP p) (old-privateP q) =
    cong Fin.suc (matched-left-inj p q)
  matched-left-inj new-paired new-paired = refl
  matched-left-inj (old-paired p) (old-paired q) =
    cong Fin.suc (matched-left-inj p q)
  matched-left-inj (old-only-match p) (old-only-match q) =
    cong Fin.suc (matched-left-inj p q)

  matched-right-inj : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
      {T : PhysicalScope ΣP0 ΔP} {W : World S T} {X X′ Y}
    → Matched W X Y → Matched W X′ Y → X ≡ X′
  matched-right-inj (old-privateI p) (old-privateI q) =
    cong Fin.suc (matched-right-inj p q)
  matched-right-inj (old-privateP p) (old-privateP q) =
    matched-right-inj p q
  matched-right-inj new-paired new-paired = refl
  matched-right-inj (old-paired p) (old-paired q) =
    cong Fin.suc (matched-right-inj p q)
  matched-right-inj (old-only-match p) (old-only-match q) =
    matched-right-inj p q

  only-not-matched-at : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
      {T : PhysicalScope ΣP0 ΔP} {W : World S T} {X Y}
    → PreciseOnly W Y → Matched W X Y → ⊥
  only-not-matched-at (old-only-privateP o) (old-privateP p) =
    only-not-matched-at o p
  only-not-matched-at (old-only-privateI o) (old-privateI p) =
    only-not-matched-at o p
  only-not-matched-at (old-only-paired o) (old-paired p) =
    only-not-matched-at o p
  only-not-matched-at (old-precise-only o) (old-only-match p) =
    only-not-matched-at o p

  record Future {ΔI ΔP ΔI′ ΔP′}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {S′ : PhysicalScope ΣI0 ΔI′} {T′ : PhysicalScope ΣP0 ΔP′}
      (p : ScopeFuture S S′) (q : ScopeFuture T T′)
      (W : World S T) (W′ : World S′ T′) : Set where
    field
      matched-future : ∀ {X Y}
        → Matched W X Y → Matched W′ (liftVar p X) (liftVar q Y)
      only-future : ∀ {Y}
        → PreciseOnly W Y → PreciseOnly W′ (liftVar q Y)

  open Future public

  future-refl : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
      {T : PhysicalScope ΣP0 ΔP} {W : World S T}
    → Future stay stay W W
  future-refl = record
    { matched-future = λ p → p
    ; only-future = λ p → p
    }

  future-trans : ∀ {ΔI ΔP ΔI′ ΔP′ ΔI″ ΔP″}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
      {S′ : PhysicalScope ΣI0 ΔI′} {T′ : PhysicalScope ΣP0 ΔP′}
      {S″ : PhysicalScope ΣI0 ΔI″} {T″ : PhysicalScope ΣP0 ΔP″}
      {p : ScopeFuture S S′} {q : ScopeFuture T T′}
      {p′ : ScopeFuture S′ S″} {q′ : ScopeFuture T′ T″}
      {W : World S T} {W′ : World S′ T′} {W″ : World S″ T″}
    → Future p q W W′ → Future p′ q′ W′ W″
    → Future (scope-trans p p′) (scope-trans q q′) W W″
  future-trans {p = p} {q = q} {p′ = p′} {q′ = q′}
      {W″ = W″} f g = record
    { matched-future = λ {X} {Y} m →
        subst≡ (λ X′ → Matched W″ X′ (liftVar (scope-trans q q′) Y))
          (sym (lift-var-comp p p′ X))
          (subst≡ (λ Y′ → Matched W″ (liftVar p′ (liftVar p X)) Y′)
            (sym (lift-var-comp q q′ Y))
            (matched-future g (matched-future f m)))
    ; only-future = λ {Y} o →
        subst≡ (λ Y′ → PreciseOnly W″ Y′)
          (sym (lift-var-comp q q′ Y))
          (only-future g (only-future f o))
    }

  extend-privateI-future : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
      {T : PhysicalScope ΣP0 ΔP} {A : Ty ΔI} (W : World S T)
    → Future (grow stay) stay W (extend-privateI W A)
  extend-privateI-future W = record
    { matched-future = old-privateI
    ; only-future = old-only-privateI
    }

  extend-privateP-future : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
      {T : PhysicalScope ΣP0 ΔP} {A : Ty ΔP} (W : World S T)
    → Future stay (grow stay) W (extend-privateP W A)
  extend-privateP-future W = record
    { matched-future = old-privateP
    ; only-future = old-only-privateP
    }

  extend-paired-future : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
      {T : PhysicalScope ΣP0 ΔP} {A : Ty ΔI} {B : Ty ΔP}
    → (W : World S T) → Future (grow stay) (grow stay) W
        (extend-paired W A B)
  extend-paired-future W = record
    { matched-future = old-paired
    ; only-future = old-only-paired
    }

  extend-only-future : ∀ {ΔI ΔP} {S : PhysicalScope ΣI0 ΔI}
      {T : PhysicalScope ΣP0 ΔP} (W : World S T) (B : Ty ΔP)
    → Future stay (grow stay) W (extend-only W B)
  extend-only-future W B = record
    { matched-future = old-only-match
    ; only-future = old-precise-only
    }

  advance-source : ∀ {ΔI ΔI′ ΔP} {S : PhysicalScope ΣI0 ΔI}
      {T : PhysicalScope ΣP0 ΔP}
    → (W : World S T) → (χs : R.StoreChanges ΔI ΔI′)
    → World (advance S χs) T
  advance-source W R.[] = W
  advance-source W (R.keep R.∷ χs) = advance-source W χs
  advance-source W (R.bind A R.∷ χs) =
    advance-source (extend-privateI W A) χs

  advance-source-future : ∀ {ΔI ΔI′ ΔP} {S : PhysicalScope ΣI0 ΔI}
      {T : PhysicalScope ΣP0 ΔP}
    → (W : World S T) → (χs : R.StoreChanges ΔI ΔI′)
    → Future (advance-future S χs) stay W (advance-source W χs)
  advance-source-future W R.[] = future-refl
  advance-source-future W (R.keep R.∷ χs) = advance-source-future W χs
  advance-source-future W (R.bind A R.∷ χs) =
    future-trans (extend-privateI-future W)
                 (advance-source-future (extend-privateI W A) χs)

  advance-target : ∀ {ΔI ΔP ΔP′} {S : PhysicalScope ΣI0 ΔI}
      {T : PhysicalScope ΣP0 ΔP}
    → (W : World S T) → (χs : R.StoreChanges ΔP ΔP′)
    → World S (advance T χs)
  advance-target W R.[] = W
  advance-target W (R.keep R.∷ χs) = advance-target W χs
  advance-target W (R.bind A R.∷ χs) =
    advance-target (extend-privateP W A) χs

  advance-target-future : ∀ {ΔI ΔP ΔP′} {S : PhysicalScope ΣI0 ΔI}
      {T : PhysicalScope ΣP0 ΔP}
    → (W : World S T) → (χs : R.StoreChanges ΔP ΔP′)
    → Future stay (advance-future T χs) W (advance-target W χs)
  advance-target-future W R.[] = future-refl
  advance-target-future W (R.keep R.∷ χs) = advance-target-future W χs
  advance-target-future W (R.bind A R.∷ χs) =
    future-trans (extend-privateP-future W)
                 (advance-target-future (extend-privateP W A) χs)

  advance-world : ∀ {ΔI ΔI′ ΔP ΔP′}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
    → (W : World S T) → (χI : R.StoreChanges ΔI ΔI′)
    → (χP : R.StoreChanges ΔP ΔP′)
    → World (advance S χI) (advance T χP)
  advance-world W χI χP = advance-target (advance-source W χI) χP

  advance-world-future : ∀ {ΔI ΔI′ ΔP ΔP′}
      {S : PhysicalScope ΣI0 ΔI} {T : PhysicalScope ΣP0 ΔP}
    → (W : World S T) → (χI : R.StoreChanges ΔI ΔI′)
    → (χP : R.StoreChanges ΔP ΔP′)
    → Future (advance-future S χI) (advance-future T χP) W
        (advance-world W χI χP)
  advance-world-future W χI χP = record
    { matched-future = λ m →
        matched-future (advance-target-future (advance-source W χI) χP)
          (matched-future (advance-source-future W χI) m)
    ; only-future = λ o →
        only-future (advance-target-future (advance-source W χI) χP)
          (only-future (advance-source-future W χI) o)
    }
