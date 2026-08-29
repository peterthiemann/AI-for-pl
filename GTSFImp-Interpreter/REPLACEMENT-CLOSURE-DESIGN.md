# Replacement-closed universal clauses — design note

Status: design (2026-08-24), not yet implemented.  This is the
resolution design for Finding E (see FUNDAMENTAL-PROPERTY-PLAN.md):
the termination obstruction in the dynamic-slot universal reveal, and
the canonical-forms obstruction in the one-sided universal reveal.

## Idea

A value related at a universal imprecision (`∀⊑∀` or `∀⊑`) stores not
just the instantiation chain for its own body type, but a *family* of
chains: one for every finite sequence of slot-conversion wrappers
applied to the (precise) value.  Revealing or concealing such a value
at a dynamic slot — the operation that today has no well-founded
reconstruction — becomes a *projection* from the stored family, plus
syntactic endpoint fixups.

The regress of Finding E is grounded because the families of the
*result* values of a chain head are stored in their own clauses,
which exist by the global induction of the fundamental lemma (on
typing derivations and the step index), not by any local recursion.

## Validated structural facts (checked against the code)

1. `UniversalsRelated` and `RightUniversalsRelated` are phantom in
   their derivation index `p`: the heads mention only
   `(W, Bᴾ, Bᴵ, k, Vᴵ, Vᴾ)`.  Family entries therefore need no
   per-descendant derivations.
2. In `RightUniversalsRelated` heads, the imprecise term is the bare
   lifted value — the imprecise side never steps.  Hence the family
   construction for `∀⊑` is *generic* (see below).
3. The producers of `∀⊑∀`-clauses each know their imprecise value's
   application step syntactically: the Λ-intro
   (`universals-related-from-body`, both sides `Λ`), the universal
   cast (`proof/LR-narrow/Cast.agda` ~4900, cast-β), and the
   reveal/conceal assemblies (β-reveal-∀ / β-conceal-∀).  The only
   producers of `∀⊑`-clauses are the Λ-intro
   (`right-universals-related-from-body`) and the assemblies.
4. `DynamicSemanticAtom` is public (`LR-narrow/Atoms.agda`), so the
   sequence datatype below is definable on the LR side; only the
   `DynamicSlot` view (10 lines, currently proof-side) needs to move
   or be duplicated publicly.

## The sequence datatype

IMPLEMENTED (2026-08-24): `LR-narrow/SlotSequence.agda`, which also
now publicly hosts `DynamicSlot` (moved from
`proof/LR-narrow/RevealStatements.agda`, which re-exports it).

The sequences are indexed by the *bodies* of the universal types they
act on; the wrapper's type argument is always the universal type:

    data UniWrap (W) : Ty (suc Δᴾ) → Ty (suc Δᴾ) → Set where
      reveal-dyn  : (d : DynamicSlot W) (B : Ty (suc Δᴾ))
        → UniWrap W B
            (replaceTy (suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B)
      conceal-dyn : (d : DynamicSlot W) (B : Ty (suc Δᴾ))
        → UniWrap W
            (replaceTy (suc (dslotXᴾ d)) (⇑ᵗ (dslotRᴾ d)) B) B
      reveal-inert  : (X R B) → X ∉ᵗ `∀ B → UniWrap W B B
      conceal-inert : (X R B) → X ∉ᵗ `∀ B → UniWrap W B B

    UniWraps W B C  -- composable sequences (innermost first), with
    wrapTerm : UniWraps W B C → Term Δᴾ → Term Δᴾ
    _++ˢ_    : composition, for the tail projection

Body-indexing is a correction found while typechecking the skeleton:
sequences indexed by whole types do NOT stay universal-headed — a
`conceal-dyn` whose type argument is a *variable* body with a
universal representative conceals a universal type into a variable
type, leaving the family's domain.  Fixing the wrapper's type
argument to `` `∀ B `` makes every step body-to-body by construction.

The two dynamic kinds serve `blocked-dyn-reveal-universal` and
`blocked-dyn-conceal-universal`; the two inert kinds (arbitrary
variable with a non-occurrence witness — subsuming the paired-slot
case) serve `blocked-precise-reveal`/`-conceal`.

## Revisions found while planning the implementation (2026-08-24)

Revision 1 (Kripke families).  The family must quantify over futures
at storage time: a value lifted to a future world must be wrappable
at the future world's *new* dynamic slots, which a per-world family
cannot cover, and repairing it inside the future-closure lemma would
make `Closure` depend on the reveal machinery (a module cycle).  The
stored component is therefore

    ∀ {W′} (W≼W′ : Future W W′) {Bᴾ′}
      (σ : UniWraps W′ (liftPreciseBody W≼W′ Bᴾ) Bᴾ′)
    → RightUniversalsRelated W′
        (liftCenterDynamicBodyImprecision W≼W′ p)
        Bᴾ′ (liftImpreciseTy W≼W′ Bᴵ) k
        (liftImpreciseTerm W≼W′ Vᴵ)
        (wrapTerm σ (liftPreciseTerm W≼W′ Vᴾ))

Future closure then composes futures, and the `(future-refl, [])`
projection is definitionally the old chain.

Revision 2 (Finding F — the `∀⊑∀` entries are unstateable).  A family
entry for a `∀⊑∀`-related pair with a precise-only (dynamic or inert)
wrapper has heads relating an *unwrapped imprecise application* to a
*wrapped precise application*.  Their joint evaluation starts with a
precise-only β of the wrapper at the real instantiation type `Sᴾ`,
allocating a precise name bound to `Sᴾ` with no imprecise partner
allocation (the imprecise application steps by whatever the abstract
imprecise value dictates, and pairing its step with the wrapper β
produces instead an inner precise application at the paired fresh
name, whose own bind is an alias of a paired name).  Neither
intermediate world is classifiable: dynamic atoms require `⊑ ★`
representative imprecision, paired atoms require the imprecise
allocation, and there is no atom kind for a precise-only allocation
at non-`★` imprecision.  Resolving this needs a world-model
extension (one-sided precise atoms at arbitrary representative
imprecision `embP Rᴾ ⊑ T`, generalizing dynamic atoms from `T = ★`),
plus, for the one-sided obligations at `∀⊑∀`, the imprecise
canonical forms already noted.  Step 4's `∀⊑∀` part is therefore
deferred; the family lands in the `∀⊑` clause only, and the four
obligations narrow to `∀⊑∀` sources.

Revision 3 (kit-based producer integration).  The family construction
needs the dynamic and one-sided computations statements, which are
obligation-parameterized, while the producers
(`proof/LR-narrow/Universal.agda`) and the compatibility layer are
not.  Rather than re-parameterizing that layer, the producers take a
*family kit* — a record of family builders whose type is
obligation-free — as an argument, mirroring the record pattern
already used by `proof/LR-narrow/FundamentalAssembly.agda`; the kit
value is constructed in the obligation-parameterized layer from the
generic `family-extend` lemmas and supplied at assembly time.

## The clause change

In `LR-narrow/LogicalRelation.agda`, the chain component of the
`∀⊑∀` clause becomes (and `∀⊑` mutatis mutandis, with `Bᴵ` unbound):

    Σ[ Bᴾ ] Σ[ Bᴵ ]
      (embedPrecise (core W) (`∀ Bᴾ) ≡ `∀ Aᴾ)
      × (embedImprecise (core W) (`∀ Bᴵ) ≡ `∀ Aᴵ)
      × (∀ {Bᴾ'} (σ : UniWraps W Bᴾ Bᴾ')
          → UniversalsRelated W p Bᴾ' Bᴵ (suc k)
              Vᴵ (wrapTerm σ Vᴾ))

The old chain is the `[]`-entry, so existing consumers
(`UniversalInstantiation`, the paired dispatch, `Closure`) project
`[]` — a mechanical rewrite of destructuring sites.  Entries are at
the same index (the wrappers are precise-only, index-preserving),
which the same-index dynamic-seal design (Finding D) already
accommodates; the LR's termination pragma argument is unchanged (the
family adds a quantifier, not a recursion).

## Why the regress is grounded

The generic one-step lemma (`family-extend`, per wrapper kind):

    chain of V at Bᴾ  →  chain of (wrapTerm [w] V) at (action w Bᴾ)

is proved exactly like the existing reveal/conceal inners: expand the
precise β (`related-precise-bind-step-expand`, index-preserving),
instantiate V's given chain head at the fresh dynamic name `＇0`, then
apply the computations-level wrappers (`dyn-revealed-computations`
etc.) at the body and fresh types.  The critical difference from
today: the value-level universal cases *inside* those computations
wrappers — the plug-values steps at ∀-shaped subtypes, including the
whole fresh type when it is ∀-shaped — are projections from the
families stored in the clauses of the *returned values*, not
recursive reconstructions.  Those families exist because every
LR-related value carries one by definition.  So `family-extend`
terminates on the type-size fuel of the computations wrappers alone,
and the family of a value is built by induction on the sequence.

Storing the family is what breaks Finding E's regress: deriving
families on the fly from bare chains would recurse through result
values with no measure (the instantiation types are λ-bound), which
is exactly the refuted situation.

## Producer obligations

* `∀⊑` (right-universal): `family-extend` is generic (imprecise side
  inert), so a single lemma
  `family-of-chain : chain → ∀ σ → entry σ` (induction on σ) serves
  every producer; the Λ-intro and the assemblies keep their current
  `[]`-chain constructions and append `family-of-chain`.
* `∀⊑∀`: the head of a wrapped pair still steps the *imprecise*
  application, so the family cannot be built generically from the
  chain (an arbitrary related value's application step is unknown —
  the canonical-forms obstruction).  Instead each producer builds the
  family by the same σ-induction, using its concrete imprecise step
  (Λ-β for the intro, cast-β for the universal cast, β-reveal-∀ /
  β-conceal-∀ for the assemblies); the σ-step instantiates the
  σ-prefix entry at the fresh paired names `(＇0, ＇0, X⊑X)`,
  mirroring `conceal-universal-inner`.  Three producer sites, each a
  generalization of an existing inner from `[]` to `σ`.

## Implementation log — step 2 landed (2026-08-24)

The clause change and every consumer rewrite are done and green
(commit "Store the replacement-closed family in the right-universal
clause"):

* `RightUniversalFamily` added to `LR-narrow/LogicalRelation.agda`
  (Kripke-indexed, per Revision 1) and installed as the chain
  component of the `∀⊑` clause;
* `LR-narrow/UniversalFamily.agda` defines the kit as a **record**
  (`RightUniversalFamilyKit` with field `to-family`);
* `proof/LR-narrow/Closure.agda` gained
  `right-universals-related-transport`,
  `right-universal-family-reindex` and
  `right-universal-family-future` (future composition), and the three
  `∀⊑` future-closure sites use them;
* `proof/LR-narrow/UniversalInstantiation.agda` projects the family
  at `(future-refl, [])`, which reduces definitionally to the old
  chain — as designed;
* the kit is threaded as an argument through the producer chain
  (`proof/LR-narrow/Universal.agda`, `proof/LR-narrow/Fundamental.agda`
  and their public wrappers); those exports are leaves, so the
  propagation stops there;
* `RevealObligations` gained a single new field
  `right-universal-family-kit`, used by the four `∀⊑` assemblies in
  `RevealStructural.agda` to turn their `heads` chains into families.

### Elaboration idioms discovered (needed for every family site)

1. **Eager implicit insertion.**  A family is a Π-type whose leading
   arguments are implicit, so an application `f a b` in a position
   expecting a family has its implicits inserted as metas and fails
   with `UnequalHiding`.  Every family-valued expression must be
   η-expanded: `λ W≼W′ σ → f a b W≼W′ σ`.
2. **Checking mode is required.**  The η-expanded lambda only gets
   its implicit lambdas inserted if the expected type is known, so
   family components must sit in checked positions — not in
   signature-less `let`/`where` bindings — and any step index the
   expected type depends on must be pinned (`{k = suc j}`).
3. **Non-injective type families.**  `RightUniversalsRelated`
   pattern-matches on the index, so unifying two of its applications
   never solves metas.  Every helper whose conclusion is one of them
   must receive `{W}`, `{p}`, `{Bᴾ}`, `{Bᴵ}`, `{k}` explicitly.

### Step 3 recipe (next session)

Discharging `blocked-dyn-reveal-universal` (and its three siblings)
is *not* a one-liner projection, because the obligation receives the
target derivation `q` rather than constructing it, and
`replace-⊑` — the lemma the paired dispatch uses to build the target
— requires paired mode `X⊑X`, which a dynamic slot does not have.
The workable route is to **match on both `p` and `q`** instead of
invoking `⊑-unique`:

* refute every shape whose precise endpoint is not a `∀`-type by
  `()` on `sourceᴾ` / `targetᴾ` (`embedPrecise (`∀ B₁)` is
  definitionally `∀`-headed, so the equations are absurd);
* `p = I.∀⊑ …`: the source carries a family; the wrapped value's
  family is `λ W≼W′ σ → fam W≼W′ (reveal-dyn d† _ ∷ σ)` with `d†`
  the lifted dynamic slot (`dyn-slot-future`), the term equality
  from `dyn-slot-precise-*-lift`, and the body-type equality from
  `liftPreciseBody-replace`.  Note `q` must still be analysed: with
  the same imprecise endpoint `Aᴵ` but a different precise endpoint,
  `q` may be `∀⊑`, `∀⊑∀`, `∀⊑★`, `∀★⊑★` or `bot⊑★`, so this case
  splits further; only the `∀⊑`/`∀⊑` combination is a projection,
  and the others need their own (mostly refutation) arguments;
* `p = I.∀⊑∀ …`: blocked by Finding F (no family is stateable);
* `p = I.∀⊑★ …` / `I.∀★⊑★`: the value is a dynamic payload pair, so
  the reveal must go through `RightDynamicPayloadRelated` — a
  separate argument, not a family projection;
* `p = I.bot-elim` / `I.bot⊑★`: refute via the bottom-value lemmas
  (they must be imported into `DynamicReveal`).

The same analysis applies to `blocked-dyn-conceal-universal` and,
with paired slots and a non-occurrence witness in place of the
dynamic slot, to `blocked-precise-reveal`/`-conceal`.

Once those land, the kit itself is provable (chain → family by
induction on σ, each step using the now-total computations wrappers),
and `RevealObligations` collapses to the Finding-F residue.

## Implementation log — step 3 landed (2026-08-24)

Step 3 is complete and green (commit "Discharge the universal wrapper
cases down to paired sources").  The step-3 recipe above was
simplified in three ways before implementation:

1. **No target analysis.**  The chain is phantom in its derivation
   index (`right-universals-phantom` transports with *no* endpoint
   equations), and the target derivation is forced by constructing a
   replaced alternative and transporting with
   `value-imprecision-reindex`.  The alternative is built by a new
   left-only replacement lemma
   (`replace-left-⊑` in `proof/LR-narrow/ReplaceImprecision.agda`):
   replacement of a variable on the left needs no mode premise, only
   that the variable avoids the right-hand side — which holds for
   dynamic slots because their center is skipped by the imprecise
   embedding (`dyn-embed-∉`).  Applied at the top derivation it
   reduces to constructor form, so the replaced clause computes.
2. **Value-level central helpers.**  Each of the four statements'
   `∀`-case delegates to one value-level helper
   (`precise-universal-value`/`-conceal-value` in `PreciseReveal`,
   `dyn-universal-value`/`-conceal-value` in `DynamicReveal`)
   dispatching on the source derivation: non-`∀` sources are refuted
   by the embedding equation, the bottom sources by
   `no-precise-bottom-value`, the star-universal sources recurse into
   the dynamic payload at the smaller index (the payload derivation
   is one of the same shapes, so the recursion is structural on the
   step index), the right-universal source projects the stored
   family, and only the paired universal source invokes the
   obligation.
3. **Ground un-replacement by refutation.**  The dynamic conceal at
   `∀⊑★` must transfer the payload shape's ground derivation from the
   replaced type back to the source type.  The key: the source's star
   premise pins the bound variable to the paired mode, so any
   `∀⊑`-shaped ground derivation — whose bound variable occurs, and
   occurrence reflects through replacement
   (`replaceTy-∈-reflect`) — contradicts `star-no-occurrence`.  What
   survives is `∀⊑∀` against the universal ground, rebuilt directly
   from the source premise (`conceal-shape-∀★`), and the bottom
   derivation, which survives replacement unchanged; the other
   grounds are refuted (`conceal-shape-⇒`/`-ι`,
   `⊑-var-right-nonvar`).

The obligations are now **value-level and `∀⊑∀`-only**: the four
blocked fields take `ValueImprecision W (I.∀⊑∀ p₀) k` (or produce
it, for the conceal direction), and the reveal development has no
other gaps besides the kit.

### Remaining (step 4 tail)

* Internalize the kit: `family-extend` (four wrapper kinds, each
  mirroring an existing assembly inner) built inside the statements
  construction from the now-total dynamic and one-sided computations
  statements, then `RevealObligations` shrinks to the four
  `∀⊑∀`-fields.  The construction is well-founded: the wrappers'
  computations recursions are type-fueled and their `∀`-cases are now
  projections, and the family is built by induction on the sequence.
* The `∀⊑∀` residue itself is Finding F (world-model extension) plus
  imprecise canonical forms — recorded in the plan.

## The `∀⊑∀` residue — path analysis (2026-08-24)

The four remaining obligations reduce to one construction: the chain
head for a pair whose precise side alone is wrapped, relating
`(Vᴵ ⦂∀ Bᴵ[Sᴵ], (Vᴾ ↑ ∀↑c) ⦂∀ B′[Sᴾ])`.  Tracing the joint
evaluation with the discharged machinery in view:

1. Pairing the imprecise application's β with the precise wrapper β
   lands in the ordinary paired bind world — the original Finding-F
   trace was overly pessimistic about this step.
2. Gap (i): the imprecise step witness for an abstract value — the
   canonical-forms gate.  Resolution: extend the families to the
   `∀⊑∀` clause, built per producer (each of the Λ-intro, the
   universal cast, and the reveal/conceal assemblies knows its
   imprecise value's step); alternatively a one-shot interpreter
   canonical-forms lemma (every imprecise universal value's
   application first-steps with a bind at the instantiation type).
3. Gap (ii), the true core: after the paired β the precise side holds
   the inner application at the fresh name.  Consuming it through the
   source chain head at the paired fresh names fails (application
   versus body on the imprecise side; contraction produces
   α-mismatched stores), and stepping it forces a precise-only bind
   whose representative is a paired name — Finding F exactly.  The
   model asymmetry is confirmed in the code: `TargetSemanticAtom`
   (imprecise-only allocations) carries no constraint at all, and
   *paired* aliases are already classifiable; only the one-sided
   precise alias is unrepresentable.

Ruled-out shortcuts, with reasons: phantom imprecise store entries
break positional naming; a name-versus-content simulation on the
precise side is false in a sealing calculus; making the precise
embedding a substitution (collapsing aliases) destroys the
injectivity inversions used throughout.

Two honest resolutions, both calculus-level:

* (a) Alias-transparent imprecision (recommended): `VarImp` becomes
  `VarImp Δ` with a third mode `X⊑ᵗ T` and one new leaf rule
  (`μ X ≡ X⊑ᵗ T → μ ⊢ T ⊑ B → μ ⊢ ＇X ⊑ B`).  The precise-only
  alias bind gets an atom at mode `X⊑ᵗ (embP R)`, the precise bind
  expansion gains an alias variant needing no `⊑ ★` derivation, and
  the `∀⊑∀` head closes through the producer's body relation.
  Uniqueness survives by mode disjointness; the narrowing
  isomorphism is unaffected (compile-time environments are
  alias-free).  Fallout is broad but mechanical: every mode analysis
  gains a case, plus the per-producer `∀⊑∀` families.
* (b) Substituting reveal β: change `β-reveal-∀`/`β-conceal-∀` to
  substitute the conversion instead of allocating the indirection.
  Eliminates the alias at the source, and with the `∀`-cases now
  projections no size regress returns — but when the slot variable
  occurs in the instantiation type the substituted conversion is not
  slot-generated, so the whole slot-wrapper machinery would need
  generalizing, on top of operational-semantics and type-safety
  surgery.  More elegant, worse fallout, and it changes the calculus.

Sequencing: internalize the kit first (orthogonal); then (a),
starting from the `VarImp Δ` core change, then the producer
families, then delete `RevealObligations`.

## Alias-transparent imprecision as fused transitivity (2026-08-24)

Refinement of resolution (a), prompted by the observation that some
versions of imprecision carry transitivity.

The connection is exact.  The alias variable is definitionally equal
to its representative's embedding `T` (store unfolding), so the alias
leaf

    μ X ≡ X⊑ᵗ T  →  μ ⊢ T ⊑ B  →  μ ⊢ ＇X ⊑ B

is the composite of an unfolding axiom `＇X ⊑ T` with an arbitrary
`T ⊑ B`: one transitivity step with a fixed left leg.  With a
transitivity rule and that single axiom the alias rule is derivable;
fusing the composite into one syntax-directed leaf is the standard
move in the other direction, and the right one here, because a
transitivity rule destroys derivation uniqueness (`⊑-unique`), on
which the whole reveal development leans, whereas the fused leaf
keeps derivations unique by mode disjointness.  Since the left leg is
definitional unfolding rather than a proper imprecision step, what
the alias needs is only "transport along store equality" — much
weaker than full `⊑`-transitivity, which is itself delicate in this
judgment (mode-environment composition, the `∀⊑` side conditions;
GTSFImp has `⊑-unique` and no `⊑-trans`, while the developments that
do have composition — GTSF's quotiented term imprecision, the
EndpointMLB factorization — pay for it with quotients or
factorization machinery).

The world model already fuses such composites at leaves; the alias
atom completes the pattern uniformly:

* paired atom: name ≐ `Rᴾ` left, name ≐ `Rᴵ` right,
  `embP Rᴾ ⊑ embI Rᴵ` stored aside; leaf `＇Z ⊑ ＇Z`;
* dynamic atom: name ≐ `R` left, nothing right; the leaf `＇Z ⊑ ★`
  is the fused composite "unfold to `embP R`, then `R ⊑ ★`", with the
  star premise stored once in the atom (`dynamicRep-related`);
* alias atom: the same with `T ⊑ B` for arbitrary `B` — the existing
  `X⊑★` mode is the `B = ★` special case (unification is possible
  but adding a third mode is less invasive than reshaping every
  `X⊑★` match).

Consequences: the leaf's metatheory should be developed as
"closure under unfolding" (occurrence up to unfolding;
`replace-left-⊑` at an alias substitutes exactly the premise), and
the first theorem to formalize is conservativity: substituting
unfoldings away maps extended derivations to current ones, and
compile-time environments are alias-free, so the paper-level
judgment is untouched.

### Correction: transitivity is admissible, so do not fuse

The fusing above was justified by the claim that a transitivity rule
would destroy derivation uniqueness.  That premise is wrong for this
judgment: GTSFImp imprecision is transitive *as a theorem* —
`⊑-trans` in `GTSFImp/ImprecisionComposition.agda` (upstream PR #186,
merged 2026-08-25), a plain structural function with no side
conditions, no postulates and no pragmas, over a fixed `μ`.  Being
admissible it adds no derivations, so it coexists with `⊑-unique`
(indeed uniqueness makes `⊑-trans` canonical: any two ways of
composing agree, which is what the reveal development needs when it
composes derivations across world stages).

Consequently the fused rule is unnecessary.  The extension reduces to
the **minimal unfolding axiom**, with no derivation premise at all:

    μ X ≡ X⊑ᵗ T  →  μ ⊢ ＇X ⊑ T

and the general alias statement `μ ⊢ ＇X ⊑ B` is then a *theorem*,
`⊑-trans` of that leaf with `T ⊑ B`.  This is strictly better:

* every structural case analysis (`star-no-occurrence`,
  `replace-⊑`, `replace-left-⊑`, `⊑-unique`, the vacuity lemmas,
  renaming and substitution) gains a **leaf** case rather than a
  recursive one;
* the leaf's conclusion is fixed by the mode, so it can overlap only
  with the *unguarded* `X⊑X` leaf, and only for a cyclic alias
  (`μ X ≡ X⊑ᵗ (＇ X)`); `X⊑★` is mode-disjoint.  The uniqueness
  repair therefore narrows to that one case — guard `X⊑X` with
  `μ X ≡ X⊑X`, or keep alias environments acyclic, which the world
  model's allocation order already gives;
* the semantic atom stores no derivation at all (contrast
  `dynamicRep-related`): the mode carries `T`, and anything else is
  computed with `⊑-trans` on demand.

Transitivity does **not**, however, remove the need for the leaf.
The missing fact is `＇X ⊑ ＇c` (alias against the paired centre it
aliases), and composition cannot reach it: the only rules with a
variable on the left are `X⊑X` and `X⊑★`, so a middle `M` with
`＇X ⊑ M` must be `＇X` or `★`; and `★ ⊑ ＇c` is underivable because
`★` is maximal (only `★⊑★` has `★` on the left).  So the leaf is
genuinely new information — transitivity refines *how much* is added,
not *whether*.

Note also that `X⊑★` cannot simply be re-expressed as
`X⊑ᵗ T` plus `T ⊑ ★`: `instᵐ` uses `X⊑★` for the `∀`-elimination's
bound variable, which has no representative.  The three modes —
paired, unconstrained, alias — stay genuinely distinct.

### Effect on the narrowing/widening isomorphism

`NarrowWiden` gives polarized presentations with derivation
isomorphisms `Widening μ A B ≅ μ ⊢ A ⊑ B ≅ Narrowing μ B A`.

* The isomorphism survives by construction.  The alias leaf always
  unfolds the *precise* endpoint, and the polarized presentations
  keep that endpoint in a fixed role — the widening's source and the
  narrowing's target — including through the contravariant domain
  flips (`w-⇒` embeds a narrowing whose target is again the precise
  side).  So each presentation gains exactly one mirrored
  constructor —

      w-alias : μ X ≡ X⊑ᵗ T → Widening μ (＇ X) T
      n-alias : μ X ≡ X⊑ᵗ T → Narrowing μ T (＇ X)

  (premise-free, per the transitivity correction below; the general
  polarized forms follow from transitivity, which transfers to the
  polarized systems through the existing isomorphism)

  — and the derivation isomorphism extends one case per direction,
  commuting with the unfolding erasure, so the isomorphism theorem
  itself remains conservative over the alias-free fragment.  The
  narrowing reading is the semantically self-evident one: a type
  narrows to a runtime name exactly by narrowing to what the name is
  bound to — the operational name-versus-content intuition that
  generated the alias problem in the first place.
* The real pressure is on uniqueness and determinism, not the
  isomorphism.  The identity-variable leaves (`X⊑X`, `w-idˣ`,
  `n-idˣ`) are currently unguarded, so a cyclic alias environment
  (μ X ≡ X⊑ᵗ (＇ X)) would give two derivations of `＇X ⊑ ＇X`
  (the identity leaf, and the alias leaf around it), breaking
  `⊑-unique` and the determinism of the polarized systems (a known
  pressure point — GTPLC records a narrowing/widening determinism
  counterexample).  Two repairs: (i) guard the identity-variable
  leaves with `μ X ≡ X⊑X`, making all variable leaves mode-disjoint
  and uniqueness syntactic again — mechanical fallout at every
  `X⊑X` use; or (ii) restrict to well-founded alias environments
  (allocation-ordered, which the world model already guarantees via
  `dynamicFresh`) and prove uniqueness under that invariant.  The
  logical relation only ever produces (ii)'s environments, but (i)
  is the cleaner metatheory.
* The one LR-side consumer of the isomorphism
  (`narrowing→imprecision` in `LogicalRelation`) is applied to
  compile-time derivations, which are alias-free — unaffected.

## Implementation log — kit removed from the reveal development
(2026-08-25)

Internalizing the kit turned on a structural question: the kit was
being used *inside* the statements it would have to depend on, so
proving it in place was circular.  The circularity is removed by
building the assemblies' families by **precomposition** instead:

* `UniWrap`/`UniWraps` now act on **both** endpoints (four indices:
  source and target precise body, source and target imprecise type),
  with `wrapTermᴾ` and `wrapTermᴵ`.  This was forced: the assemblies'
  target values are wrapped on the imprecise side too, so a
  precise-only sequence cannot express them.  The six constructors
  are reveal/conceal at a paired slot (both endpoints), at a dynamic
  slot (precise only) and at an inert paired slot (precise only, with
  the non-occurrence witness).  `PairedSlot` and its accessors moved
  to `LR-narrow/SlotSequence.agda` beside `DynamicSlot`, re-exported
  from `RevealLifting`/`SlotLifting` so downstream imports are
  unchanged.
* `reveal-paired-family` and `conceal-paired-family`
  (`RevealStructural.agda`) build the wrapped value's family by
  precomposing the source value's stored family with the paired
  wrapper, transporting along the lift/replace commutations
  (`liftPreciseBody-replace`, `replace-imprecise-lift`) and the term
  commutations (`lifted-reveal-precise`/`-imprecise`,
  `lifted-conceal-precise`/`-imprecise`).  Phantomness of the chain
  in its derivation index (`right-universals-phantom`) does the rest.
* The two *absent* assemblies need no new machinery at all: their
  targets are wrapped on the precise side only, which is exactly what
  `precise-universal-value`/`precise-universal-conceal-value`
  already produce, so their whole `at-every-index` collapses to one
  call plus a `⊑-unique`-style reindex.

Consequently **`RevealObligations` no longer mentions the kit**: the
record is now exactly the four value-level `∀⊑∀` fields, all of them
Finding-F.  The reveal development is free of the kit.

### What is left of the kit

`RightUniversalFamilyKit` survives only as an explicit argument of
the *producers* (`proof/LR-narrow/Universal.agda` and
`proof/LR-narrow/Fundamental.agda`), where the `Λ` introduction must
supply a family for a value it built itself.  Discharging it needs
the six one-step extensions in chain form:

    endpoints + chain for (Vᴵ, Vᴾ) at (B, C)
      → chain for (wrapTermᴵ₁ w Vᴵ, wrapTermᴾ₁ w Vᴾ) at (B′, C′)

plus induction on the sequence, in a new module after
`RevealStructural` that draws `Below` from the completed
`statements-all` (no circularity remains, since the statements no
longer mention the kit).

The raw material already exists and typechecks: the paired
extensions are precisely the `heads` of `reveal-right-universal` /
`conceal-right-universal` (with `reveal-right-universal-head`/
`-inner` and their conceal duals), and the dynamic and inert
extensions are the `[]`-projections of `dyn-universal-value` and
`precise-universal-value`.  Those functions are currently unused by
the assemblies — they were kept deliberately for this purpose.  The
one restatement needed is to take endpoints-plus-chain rather than a
full value relation, since a bare chain carries no endpoints.

## Implementation log — the six extensions (2026-08-26)

All six one-step chain extensions are **proved and green**
(`proof/LR-narrow/UniversalFamilyKit.agda`):
`reveal-paired-chain`, `conceal-paired-chain`, `reveal-inert-chain`,
`conceal-inert-chain`, `reveal-dyn-chain`, `conceal-dyn-chain`.

Supporting work that landed with them:

* the universal wrapper *heads* were restated on a bare instantiation
  chain — a small record `RightUniversalData` (the `∀⊑` clause tuple
  with the family replaced by a chain, plus the endpoint typings), so
  they no longer presuppose the family they are used to build.  The
  `with`-preambles that re-derived the chain's body types from the
  clause disappeared, since the record already fixes them;
* two entirely new head/inner pairs for the dynamic slot,
  `reveal-dyn-universal-head`/`-inner` and
  `conceal-dyn-universal-head`/`-inner`, adapted from the absent
  (one-sided) variants but with the body wrapper at the lifted
  dynamic slot (`dyn-revealed-computations` /
  `dyn-concealed-computations`) and the body derivation replaced by
  `replace-left-⊑`;
* the inert wrappers were weakened to carry the *precise*
  non-occurrence `slotXᴾ s ∉ᵗ `∀ B` rather than the centre fact
  `center s ∉ᵗ Bc`.  This was forced: the producer of inert entries
  (`precise-universal-value`) only has the precise fact, and the
  centre fact does not follow from it.  The absent heads needed the
  precise fact anyway, so they got simpler;
* the endpoint helpers (`revealed-endpoints`, `concealed-endpoints`,
  `dyn-reveal-endpoints`, `dyn-conceal-endpoints`,
  `precise-reveal-endpoints`, `precise-conceal-endpoints`) now take
  `TypedEndpoints` instead of a full `ValueImprecision`, since that
  is all they ever used.

## Finding G — conceal wrappers must carry their target derivation

Assembling the extensions into `to-family` (iterate along the
sequence, then project) hits a genuine obstruction, not bookkeeping.

Each extension step must hand the next step a derivation at the
wrapped types, because the heads build the *body* imprecision
derivation from it (`liftCenterDynamicBodyImprecision p₀`, then
`t₀`).  For a **reveal** wrapper that derivation is constructible —
`replace-⊑` at a paired slot, `replace-left-⊑` at a dynamic slot,
and the identity for an inert one.  For a **conceal** wrapper it
would have to be *un*-replaced, and un-replacement is false:

    take B = ＇(suc X) with X the slot variable and R = ‵ι, so
    replaceTy (suc X) (⇑ᵗ R) B = ‵ι.  Then
    `∀ ‵ι ⊑ ★` is derivable (∀⊑★), but `∀ ＇(suc X) ⊑ ★` is not:
    ∀⊑★ would need `extᵐ μ ⊢ ＇(suc X) ⊑ ★`, i.e. mode `X⊑★` at a
    variable whose mode is the paired `X⊑X`.

So the conceal constructors of `UniWrap` must carry the imprecision
derivation of their *target* body, alongside its `NonVar` and
occurrence witnesses — data that every consumer of a conceal entry
already has (it is the derivation of the clause it is producing), but
that cannot be recovered from the wrapper's types alone.  That is the
next step: widen the three conceal constructors, thread the extra
fields through the three conceal consumers (`conceal-right-universal`,
`precise-universal-conceal-value`, `dyn-universal-conceal-value`),
and then the iteration and `to-family` are pure bookkeeping.

## Implementation log — the kit is discharged (2026-08-26)

`universal-family-kit : RightUniversalFamilyKit` is **proved**
(`proof/LR-narrow/UniversalFamilyKit.agda`), and
`right-universal-value-compatible` there is the `Λ` introduction with
the kit supplied, so the producers no longer carry it as a
hypothesis.  No postulates, no new pragmas.

Finding G was resolved by widening the wrappers, which are our own
definition (`LR-narrow/SlotSequence.agda`), not part of the GTSFImp
calculus.  Rather than only patching the conceal cases, every wrapper
now carries a `BodyImprecision` for the bodies it *produces* — the
clause data (`NonVar`, the zero occurrence, and the centre
imprecision) that a `∀⊑` clause records.  Every consumer already has
it, since it is the data of the clause it is building, and carrying
it uniformly also spared the reveal wrappers from rebuilding their
target derivations with `replace-⊑` / `replace-left-⊑`.

Three refinements made the assembly go through:

* **Canonical embeddings.**  `BodyImprecision` fixes its centre types
  as `embedPreciseBody W B` and `embedImprecise W C` instead of
  carrying them existentially with equations.  With the existentials,
  two data for the *same* bodies had propositionally-but-not-
  definitionally equal centre types, which broke the one-sided
  endpoint helpers (they require the two derivations to share an
  imprecise endpoint).  Canonical form makes those equations `refl`.
  `body-imprecision-of` rebuilds the record from a clause's own
  equations, and `body-imprecision-future` transports it to a future
  world.
* **Shapes, not value witnesses.**  The paired wrappers need the
  imprecise conversion to be a value.  Carrying the `RevealValue` /
  `ConcealValue` witness fails, because it is not stable under
  renaming: a `ConcealValue` at a variable type is a `seal`, which
  becomes an identity once the slot changes.  The wrappers carry a
  `UniShape` (function or universal) instead, from which both
  witnesses follow and which lifts along futures trivially.
* **Inert steps keep the incoming data.**  For the inert wrappers the
  bodies are unchanged, so the step reuses the incoming
  `BodyImprecision` and transports the chain along
  `replaceTy-absent`; using the carried one would have demanded that
  two derivations of the same statement be definitionally equal.

The iteration is then `extend-wraps`, a fold of `extend-wrap` along
the sequence, and `to-family` lifts the data to the demanded future
(`data-future`), folds, and projects the chain — transported to the
family's own derivation by `right-universals-phantom`, which is
sound precisely because the chain is phantom in its derivation.

**State of the development.**  `RevealObligations` is now exactly the
four `∀⊑∀` fields, all of them Finding F; every other universal
statement is proved, and the replacement-closure programme is
complete.

## Alias-transparent imprecision — validated core, staged plan
(2026-08-26)

The extension was implemented in the core and typechecked there, then
reverted so the shared calculus stays green: completing it is a
multi-session refactor of GTSFImp, and the tree cannot sit red in the
meantime.  What the attempt established:

### The rule must be the fused one after all

The earlier "do not fuse" correction was itself wrong on one point.
The minimal unfolding axiom `μ X ≡ X⊑ᵗ T → μ ⊢ ＇X ⊑ T` is **not
closed under transitivity**: `⊑-trans (unfold eq) q` would have to
produce `＇X ⊑ C`, which the axiom only yields when the mode records
`C` rather than `T`.  So keeping the upstream `⊑-trans` true *forces*
the fused rule

    alias : μ X ≡ X⊑ᵗ T  →  μ ⊢ T ⊑ B  →  μ ⊢ ＇X ⊑ B

which is closed by `⊑-trans (alias eq p) q = alias eq (⊑-trans p q)`.
Transitivity's role is thus the opposite of what the correction said:
it does not let us shrink the rule, it pins the rule's shape.  With
modes being constructors of `VarImp`, the three variable leaves are
mode-disjoint, so `⊑-unique` survives with **no** acyclicity side
condition and the unguarded `X⊑X` leaf can stay as it is.

### The core change (typechecked)

`VarImp` becomes context-indexed, with a weakening, and `extendᵐ`
weakens the modes it shifts:

    data VarImp (Δ : TyCtx) : Set where
      X⊑X : VarImp Δ ; X⊑★ : VarImp Δ ; X⊑ᵗ : Ty Δ → VarImp Δ
    ⇑ᵛ : VarImp Δ → VarImp (suc Δ)
    extendᵐ v μ (suc X) = ⇑ᵛ (μ X)      -- was: μ X

Because `extᵐ μ (suc Z)` no longer reduces to `μ Z`, every mode
equation crossing a binder needs transport.  Four one-line lemmas
suffice and were proved: `ext-mode-paired`, `ext-mode-star` (by
`cong ⇑ᵛ`) and their inverses `ext-mode-paired-inv`,
`ext-mode-star-inv` (by casing on the mode; the alias mode never
lifts to a paired or dynamic one).

### Remaining work, and the obstacle class that makes it non-mechanical

* ~87 exhaustive matches on `_⊢_⊑_` (48 in GTSFImp, 39 in the
  interpreter) each need an `alias` case, most of them recursive.
* ~111 `VarImp` signatures need the context index — in world-lifting
  operations the mode belongs to the *extended* context
  (`VarImp (suc Δ)`).
* The genuinely non-mechanical part: existing metatheory whose
  hypotheses mention only the dynamic mode.  `⊑-env-mono`
  (`proof/DGG/WorldDecay.agda`) maps a derivation along
  `∀ Z → μ Z ≡ X⊑★ → μᵈ Z ≡ X⊑★`, which says nothing about aliases
  and so becomes *false* at the new leaf; it needs the extra premise
  `∀ Z T → μ Z ≡ X⊑ᵗ T → μᵈ Z ≡ X⊑ᵗ T`, and each of its four users
  must supply it.  Expect a handful of similar strengthenings —
  every lemma that abstracts over an environment change is a
  candidate.

Suggested staging: (1) core plus the four transport lemmas; (2) the
`VarImp` index across world constructions; (3) the `alias` cases in
GTSFImp, strengthening environment-change hypotheses as they surface,
to a green `GTSFImp/All.agda`; (4) the same in the interpreter, ending
with the LR clause and the alias atom; (5) the alias bind expansion
and the `∀⊑∀` head, discharging the four obligations.  Steps 1–2 are
done and reproducible from this note; the branch was reverted only to
keep the tree green.

## Consumer rewrites (the payoff)

* `DynamicReveal`'s universal case (both directions): project the
  `reveal-dyn`/`conceal-dyn` entry, fix up endpoints — discharging
  `blocked-dyn-reveal-universal`/`-conceal-universal`.  The dynamic
  statement then recurses on type fuel only, with ∀ non-recursive.
* `PreciseReveal`'s universal case: project the inert entries —
  discharging `blocked-precise-reveal`/`-conceal`.  This also
  dissolves the canonical-forms gate: the imprecise application step
  that the consumer cannot perform was performed by the producer.
* The obligation record `RevealObligations` becomes empty and can be
  deleted; the module parameters `ob` disappear.

## Closure lemmas

* Downward: pointwise (chains are downward-closed already).
* Future: lift a sequence along `W ≼ W′` (slots lift by
  `dyn-slot-future`/`EntryLift`; non-occurrence by `liftCenter-∉ᵗ`-
  style lemmas on the precise side) and commute `wrapTerm` with
  `liftPreciseTerm` (single-wrapper versions `lifted-reveal-precise`
  / `lifted-conceal-precise` exist).
* Reindex (`⊑-unique` fixups): unchanged pattern.

## Open risks

1. Volume: LR clause change + sequence module + closure lemmas +
   three producer upgrades + four obligation discharges.  Comparable
   to the Finding-D fallout, likely two to three sessions.
2. The inert-wrapper entries transport along `replaceTy-absent`;
   the with-abstraction pitfalls seen in the dispatch (context
   rewriting) will recur and need the established view/transport
   idioms.
3. The `∀⊑∀` producers' σ-induction at the cast site composes the
   cast-β with the wrapper βs; the expansion lemmas exist
   (`related-paired-bind-step-expand`) but the redex bookkeeping is
   the largest single proof.
4. The family quantifier puts `SlotWraps` (hence the dynamic-atom
   records) inside the LR clause; `Set₁` bookkeeping should be
   unaffected but must be confirmed early with a skeleton typecheck.

## Suggested implementation order

1. `LR-narrow/SlotSequence.agda`: datatype, `wrapTerm`, composition
   — DONE (this commit); lifting along futures remains.
2. Clause change + mechanical `[]`-projections at existing
   destructuring sites; get the tree green with families produced
   only where trivially possible (`family-of-chain` for `∀⊑` may
   land here if the generic proof goes through early).
3. `∀⊑` producers + `DynamicReveal`/`PreciseReveal` right-universal
   projections.
4. `∀⊑∀` producers (intro, cast, assemblies), then the paired
   projections, then delete the obligation record.

## Finding H — aliases falsify the two-sided reveal statements
(2026-08-26, alias branch)

Step 5 planning uncovered a gap the staged plan does not cover.
Once `Future` gains the alias-bind step (which it must — see the
allocation audit below), the two-sided sized statements
(`RevealAtSized`/`ConcealAtSized`) become **false as stated**, and
the failure is reachable through their own Kripke re-entry.

### Why the alias bind must be a `Future` step

`PairedReturns` lets the prover choose any world whose stores match
the trace's cumulative changes, but the choice is still along
`Future`.  The obligations' computations perform, on the precise
side, the wrapper β (`bind Rᴾ`) followed by the inner application's
β (`bind ＇0`), against a single imprecise β (`bind Rᴵ`).  Whichever
two allocations are paired, the third is precise-only with a
non-`★` representative — `future-precise` requires `embP Aᴾ ⊑ ★`,
which fails for both `＇0` (paired mode) and `Rᴾ` (arbitrary).  Only
an alias-mode bind classifies it.  Note the operational alias is
always `bind ＇0`: its representative is exactly the variable of the
immediately preceding bind (`β-reveal-∀`'s reduct applies the inner
value at `＇0`).

### The falsifying configuration

`replace-⊑` (hence the two-sided reveal) rewrites the slot center
`c` in every type of the derivation, but the alias *mode* `X⊑ᵗ T`
lives in the environment, which replacement does not touch.  An
`alias` leaf whose recorded representative `T` mentions `c` cannot
be rebuilt after replacement: the premise must be at `T` exactly,
and `T` is not replaced.  Alias avoidance (`AliasesAvoid μ c`) is
the exact precondition — and it is **not transportable** along alias
futures: a later alias may record `T = ＇c` (the operational alias
does exactly this when its predecessor bind pairs the slot).

The reachability: `reveal-function-head` re-enters `concealAt`/
`revealAt` at `slot-future s W≼W′` for a **consumer-chosen** `W′`
(the Kripke position of the produced `FunctionsRelated`), so no
top-level side condition on the initial world can exclude alias
worlds from the statements' domain.

### Resolution: derivation-restricted avoidance

The saving observation: the derivations at every re-entry are
**lifts of subderivations of the original** (`liftCenterImprecision`
creates no new `alias` leaves; `replace-⊑` preserves leaves;
`⊑-unique` makes leaf-sets a function of the judgment).  So the
right precondition is not world-level but derivation-level:

    AliasAvoidᵖ : TyVar Δ → μ ⊢ A ⊑ B → Set
    -- at an alias leaf (eq : μ X ≡ X⊑ᵗ T): c ∉ᵗ T, recursively;
    -- structural cases: products, with c shifted under the binders
    -- of ∀⊑∀ / ∀⊑ / ∀⊑★; other leaves: ⊤.

with transport lemmas along lifting (`rename-⊑` commutes with the
leaf structure), replacement, subderivations, and `⊑-unique`
(reindexing between derivations of one judgment preserves it).  The
two-sided sized statements and `replace-⊑` take `AliasAvoidᵖ
(center s) p` (`replace-⊑`'s current `AliasesAvoid μ c` premise
weakens to the leaf-restricted form); the one-sided and dynamic
statements need `AliasAvoidᵖ` only where they recurse into the
two-sided ones.  Producers discharge it at compile-time-derivation
roots (alias-free: `NoAliases` environments give it vacuously) and
the reveal recursion transports it.

### Consequences for the staged plan

The step-5 dependency order is forced from the bottom:

1. `AliasAvoidᵖ` and its transport lemmas; thread it through
   `replace-⊑` and the sized statements (the `RevealStructural`
   sweep).  Replace the `World.noAlias` refutations in the reveal
   machinery with the real alias cases, which under `AliasAvoidᵖ`
   collapse cleanly: avoidance plus `target-occurs-source` gives
   `c ∉ B` at every alias leaf, so both replacements are identities
   (`replaceTy-absent`) and identity-reveal steps close the case.
2. Drop `World.noAlias`; add `aliasBindCore`/`aliasBindWorld` (a
   precise-only bind at mode `X⊑ᵗ (⇑ᵗ (embP Aᴾ))` with a fresh
   alias atom) and the `future-alias` step; sweep the ~200 `Future`
   matchers (each mirrors `future-precise`).
3. The `∀⊑∀` clause change: store the wrap-closed Kripke family
   (`UniWraps`-quantified, exactly as the `∀⊑` clause) — consumers
   project `[]`; the four blocked obligations become cons
   projections (`λ W≼W′ σ → fam W≼W′ (w ∷ σ)` plus endpoint fixups).
4. The `∀⊑∀` producers build families by σ-induction with their
   concrete imprecise steps: the universal cast (`Cast.agda`) and
   the two-sided assemblies (`RevealStructural.agda`); the entry
   for a wrapped pair pairs the wrapper β's `bind Rᴾ` with the
   imprecise β's `bind Rᴵ` as the paired bind, classifies the inner
   application's `bind ＇0` as the alias bind (`future-alias`), and
   instantiates the prefix entry at `(＇0, Rᴵ)` with the
   representative imprecision given by the `alias` rule.  This is
   the redex bookkeeping the plan already flags as the largest
   single proof.
5. Delete `RevealObligations` and the `ob` parameters.

Steps 1–2 are large but now fully specified; steps 3–4 carry the
residual proof risk.  What is landed so far on the alias branch:
the alias atom and LR clause (step 4 of the outer staging), and the
real alias closure under futures (`alias-holds-lift`/`-future`,
`liftCenterMode-alias`, and the three future-lifting lemmas'
alias cases in `proof/LR-narrow/Closure.agda`) — the last
`noAlias` uses outside the reveal machinery.

## Finding I — the family's cast producer needs type-transparent
## precise binds (2026-08-27)

Steps 1–5 of Finding H landed: the four blocked obligations are
family projections, `RevealObligations` is gone, and the residual
is the deferred `universal-familyᵇ : UniversalFamilyKitᵇ` field.
Working that residual uncovered three results, one of which
falsifies this note's earlier claim that the cast producer's
σ-induction is "symmetric, no gap" (step 4 of Finding H's plan and
the `∀⊑∀` path analysis above).  Record of the analysis:

### I.1  The chain-based kit is unprovable — do not revive it

`to-familyᵇ : UniversalData → UniversalFamily` (chain in, family
out) has no proof: a chain of heads only couples the two apps at a
common world, and extending a chain across ONE wrapper is exactly
the blocked one-sided statement.  Per-wrapper factorizations fail
at every level (chain, continuation, value), and cons-projections
are vacuous for bootstrapping.  The kit record's current statement
must not survive; the deferred surface has to be reshaped to a
producer-specific premise (the source value's FAMILY plus the
concrete cast, or the Λ body relation).

### I.2  The head's paired bound was an over-specification (fixed)

Every `⦂∀` application β binds the applied type (`β-Λ`,
`β-reveal-∀`, `β-conceal-∀`, `β-gen`; the `∀ᶜ` cast-β is pure), so
under a wrapper stack the precise side binds `Rᴾ` at its FIRST peel
and re-binds `＇0` at every later one, while the imprecise side
binds only at paired wrappers (inert/dyn wrappers do not touch the
imprecise term — `wrapTermᴵᵇ₁` is the identity there).  The old
head demanded `PostBindValueRelation` at
`pairedBindWorld W′ Rᴾ Rᴵ r`, i.e. the FIRST fresh center slot must
be the paired one.  A Λ-producer can honor that (the bare imprecise
Λ-β supplies the `Rᴵ` bind to pair with), but a cast producer under
a σ with no paired wrapper cannot: its precise side must bind `Rᴾ`
first with no imprecise partner, and slot modes are fixed at
allocation, so no later reconciliation can retrofit the paired
mode.  Since no consumer ever inspected the bound (they only thread
the factoring), the head now carries `FutureValueRelation s`
(commit "Relax the universal head to the future value relation").
The right-universal head keeps its `preciseBindWorld` bound — its
imprecise endpoint is never applied, so the one-sided bound is
always realizable.

### I.3  The remaining gap: the first peel of a paired-free σ

With the relaxed head, the cast producer's schedule for a head at
`(W′, Rᴾ, Rᴵ, r, s)` under σ is:

* pair the i-th precise bind with the i-th imprecise bind while
  both queues are nonempty (contents: `Rᴾ`/`Rᴵ` first, `＇0`/`＇0`
  after; the `＇0 ⊑ ＇0` premises come from the top paired slot
  through alias hops);
* classify each surplus precise `＇0`-bind as an alias bind —
  `related-alias-bind-step-expand` (landed) with the fresh alias
  atom at rep `＇0`;
* at the center, expand the pure cast-βs and appeal to the SOURCE
  value's family (available in the `∀ᶜ` clause) at the composite
  future with `σ = []` and the instantiation
  `(＇0-deep , lift Rᴵ , r*)`, framing the result casts with
  `cast-computations-related`, where `r*` walks the alias chain by
  iterated `I.alias`.

For σ with at least one paired wrapper this closes.  For σ whose
wrappers are ALL precise-only (inert/dyn — reachable: the four
projections cons exactly such wrappers), the FIRST precise bind has
content `Rᴾ` (not a variable) and no imprecise partner, and the
chain-bottom premise needs `＇slot₁ ⊑ lift Rᴵ`.  The only mode that
can supply it is `X⊑ᵗ (embP Rᴾ)` — a SELF-ALIAS: the `alias` rule
then discharges `＇slot₁ ⊑ embI Rᴵ` from `r` itself.  This is not a
trick; it is the semantic content of the blocked statements: the
instantiation seal created by a one-sided wrapper β must be
type-transparent to the center, or the source relation cannot be
instantiated at it.  There is no schedule that avoids it (verified
against every alternative: transferring σ to the source value fails
on types — inert conversions mention the wrapped body, and casts
do not preserve variable occurrence; black-box tail reuse fails on
sealing; pre-allocating the paired world breaks store matching).

### I.4  The program this forces (in dependency order)

1. **Generalize the alias atom's representative to a type.**
   `AliasSemanticAtom`: `aliasRepName : TyVar Δᴾ` becomes
   `aliasRep : Ty Δᴾ` (store binds `aliasRep`, `aliasRep-eq` embeds
   it, the seal names it).  The mode `X⊑ᵗ T`, the `alias` rule, and
   the whole `AliasAvoidᵖ` layer are already general in `T`.
   Mechanical consumers: the weaken/shift clones in `Atoms.agda`,
   `aliasBindCore/World` (now `aliasBindWorld W (R : Ty Δᴾ)`, the
   variable case recovering today's behavior), `alias-holds-chain`,
   Closure ~1306, and the `ground-imprecise-targets-agree`
   recursion (its fuel is derivation size, not chain length — the
   general rep only adds non-variable base cases, for which the
   NonVar ground lemmas already exist).

2. **The non-mechanical consumer: `reveal-alias`/`conceal-alias`.**
   Today they use `alias-holds-rep` (T is a variable) and
   `alias-premise-B-shape` (so B is a variable or ★) to make both
   conversions identities.  With a general `T` the LEFT type is
   still the alias variable (identity conversion, mode-disjointness
   as today), but `B` is arbitrary, so the slot conversion acts
   structurally on the IMPRECISE endpoint only.  Unfolding the
   alias atom, the needed statement is an imprecise-side-only
   reveal of the payload pair `(Vᴵ, payload)` at the premise
   `p′ : T ⊑ B` where the center avoids `T` — the exact MIRROR of
   `PreciseRevealAt` (center ∉ LHS instead of ∉ RHS).  This is a
   new statement family (`TargetRevealAt`/`TargetConcealAt`-style)
   joining the sized induction, with its own `∀⊑∀` case — which
   needs an imprecise-only wrapper kind added to `UniWrapᵇ`
   (`wrapTermᴾᵇ₁` identity), whose peels in producer cascades are
   imprecise-only binds (world class: `future-imprecise` with a
   target-style entry).

3. **One-sided alias frames.**  The cascade's re-wrapping after an
   alias peel produces precise-side conversion frames at the FRESH
   ALIAS slot (`〖0, ⇑Rᴾ↑B〗` at slot₁).  The existing frame
   transformers cover paired slots (`revealed-computations`) and
   dynamic slots; alias slots need their own one-sided family.  At
   the derivation level it is `replace-left-⊑` (the replacement
   machinery already landed for Finding H); the computation-level
   statement mirrors `PreciseRevealAt` with the alias slot's
   transparency (`I.alias`) instead of `X⊑★`.

4. **The cast producer's cascade** in `related-value-casts`' `∀ᶜ`
   clause, per the schedule of I.3, using 1–3 plus
   `related-alias-bind-step-expand` (landed) and the assembled
   reveal entry points (`reveal-structural` etc. — RevealStructural
   closes its own induction and does not depend on Cast, so no
   parameter is needed).  Then reshape/delete the kit: Cast stops
   taking `kitᵇ`; `universal-compatible` takes a family-producing
   premise directly (its real producer is the deferred
   `universal-intro` implementer, whose own cascade needs no
   self-alias — the Λ-β always pairs); the `universal-familyᵇ`
   field of `RemainingObligations` goes away.

Items 2 and 3 are each comparable to the existing `PreciseReveal`
development; item 4 is the largest single proof of the plan, as
already flagged.  Landed so far under this finding: the head
relaxation (I.2) and the alias-bind step expansion (first half of
item 4's toolkit).

## Implementation log — the imprecise-side reveal family landed
## (2026-08-27, Finding I item 2)

`proof/LR-narrow/ImpreciseReveal.agda` states and proves the
imprecise-side one-sided structural reveal and conceal
(`ImpreciseRevealAt`/`ImpreciseConcealAt`): when the paired slot's
center avoids the precise endpoint, wrapping only the imprecise
endpoint in the slot conversion exchanges the derivation for its
right-replaced form.  Structure of the development:

* The statements take the source derivation with its
  derivation-restricted avoidance and the center non-occurrence in
  the LEFT endpoint, plus the caller's target derivation with the
  replaced-embedding equation.  Every case produces the clause at
  the canonical replaced derivation (`replace-⊑` with the left
  endpoint fixed by `replaceTy-absent`) and reindexes, so the
  caller's derivation is never inverted — this is what avoids the
  cross-rule ambiguity at `∀`-typed judgments (`∀⊑∀` versus `∀⊑`
  cannot be separated by inversion, only by uniqueness against a
  built witness).
* The recursion is by derivation size alone (`sizeᵖ`, preserved by
  Kripke lifting via `lift-center-size`): the alias case unfolds to
  its premise, the arrow case to its components, and — unlike the
  two-sided induction — the ★-right cases are all identities, so no
  lexicographic index component is needed.  The file is standalone:
  it does not depend on the sized reveal induction.
* The unseal configuration (the conversion at the slot's own
  imprecise variable) is refuted outright by the new inversion
  `paired-var-right-⊑`: under avoidance, a derivation whose right
  endpoint is a paired-mode variable starts at that variable (alias
  detours die on the avoidance, right-universal sources on their
  non-variable body).  With the center avoiding the left endpoint,
  each of the three candidate sources is contradictory.
* The alias case rebuilds the holding through
  `alias-holds-imp-map` (the imprecise-endpoint-changing variant of
  the alias-chain accessor) with the payload recursion at the same
  index and the strictly smaller premise; the avoidance's alias-leaf
  component `center ∉ᵗ T` is exactly the recursion's non-occurrence
  premise.
* The `∀⊑∀` case conses the new `reveal-impreciseᵇ`/
  `conceal-impreciseᵇ` wrappers onto the stored family (the
  imprecise-only kinds added to `UniWrapᵇ`), following the paired
  cons template with a trivial precise side.
* The `∀⊑` case is threaded as the `ImpreciseRightExtension`
  record: the right-universal family's `UniWraps` does not yet have
  an imprecise-only kind, so the two value-level obligations
  (`imprecise-right-reveal-value`/`imprecise-right-conceal-value`)
  are premises.  Nothing in-tree consumes the mirror yet, so no
  deferred obligation enters the theorem path.

### Remaining for item 2 — the right-universal chain extension

Discharging `ImpreciseRightExtension` needs, in order:

1. The imprecise-only wrapper kind in the right-side `UniWraps`
   (mirroring `reveal-imprecise`ᵇ, with `UniShape C` so the
   conversion is value-forming), which forces new cases in the
   right-kit's σ-induction (`UniversalFamilyKit.agda`).
2. The new chain-extension head: the source chain's head must be
   instantiated at the SAME `(Rᴾ, r★)` as the caller's (there is no
   wrapper β on the precise side, so the `＇0`-instantiation trick
   of the existing right heads is unavailable).  This needs the
   canonical instantiated source relation, i.e. a ⊑-substitution
   lemma (`instᵐ μ ⊢ A ⊑ ⇑B → μ ⊢ embP Rᴾ ⊑ ★ → A[embP Rᴾ] ⊑ B`
   at the embedding level), which does not exist in-tree yet.
3. The value-level transformation at the instantiated relation
   splits on whether the center occurs in `embP Rᴾ`:
   * absent — the mirror applies, but its avoidance premise must be
     weakened at ★-right alias leaves (the r★-substituted
     subderivations have ★ right endpoints throughout, where the
     mirror is an identity and needs no avoidance; note
     `replace-⊑` already routes ★-right subtrees through the
     avoidance-free `replace-star`), so the instantiation lemma
     must transport a correspondingly weakened predicate;
   * present — the head is vacuous: a paired center occurring in
     the left endpoint must occur in the right endpoint (the mirror
     image of `target-occurs-sourceᵖ`, with the paired mode ruling
     out the alias and dynamic leaves), and the replaced right
     endpoint provably does not contain the center.

### Addendum — the exact remaining gap is an avoidance weakening

Scoping the `ImpreciseRightExtension` discharge against the tree
sharpened the plan above:

* The ⊑-substitution engine EXISTS: `subst₂-⊑` (with `subst-⊑`,
  `open-head-alias-map`, and the `openRelatedBodyImprecision`
  pattern in `LR-narrow/World.agda`).  The chain-extension head's
  instantiated source relation `t″` is the `instᵐ` mirror of
  `openRelatedBodyImprecision`, with the star discharge at the
  bound variable given by the head's `r★`.
* The head's world plumbing is unproblematic: the right-universal
  head's precise term and post-bind bound are exactly the source
  head's, and the imprecise side settles purely, so the
  transformation is an imprecise-frame composition whose value plug
  is the mirror at `(lift t″ → lift t)` — `UniShape` makes the
  wrapped value a value.
* The one genuine gap: the mirror demands `AliasAvoidᵖ` of `t″`,
  but `subst₂-⊑` copies `r★`'s subderivations into the star
  positions, and their alias leaves (all with ★ right endpoints)
  admit no avoidance guarantee.  The fix is a ★-right-exempt
  avoidance variant — at an alias leaf, `(B ≡ ★) ⊎ (c ∉ᵗ T)` —
  threaded through the mirror in place of `AliasAvoidᵖ`:
  - the mirror's alias case is only reached at `UniShape` types,
    where the ★-branch is refuted by the embedding equation, so its
    proofs are unaffected;
  - the weakened `replace-⊑` is provable: its `⇒⊑★` clause already
    routes through the avoidance-free `replace-star`, and at a
    ★-right alias leaf the replaced judgment can reuse the UNREPLACED
    premise (`T ⊑ ★` is untouched by the replacement, since the
    right endpoint ★ is fixed and the left variable is
    mode-disjoint from the slot);
  - the instantiation lemma then transports the weakened predicate:
    inherited leaves substitute (in the occurs-absent branch the
    center avoids the substituted representatives), star-copied
    leaves take the ★ branch.
* The occurs-present branch of the head is vacuous via the mirror
  image of `target-occurs-sourceᵖ` (a paired center occurring on
  the left occurs on the right; the alias and dynamic leaves are
  ruled out by the paired mode) against the replaced right
  endpoint's center-freeness.

Order for the discharge: the weakened predicate + its transports,
the weakened `replace-⊑`, re-thread `ImpreciseReveal` (mechanical —
every case already treats ★-right positions as identities), the
right-side `UniWraps` kind, the kit's chain-extension via the
instantiation lemma and the occurs split, then instantiate and
delete `ImpreciseRightExtension`.

## Implementation log — the right-universal chain extension landed;
## `ImpreciseRightExtension` discharged and deleted (2026-08-27)

Finding I item 2 is complete.  The right-side `UniWraps` gained the
imprecise-only kinds, the kit's σ-induction gained their chain
extensions, and the `∀⊑` cases of the mirror are now closed in
place, so the extension record is gone.  Four discoveries made the
discharge simpler than the addendum's plan:

* **The extension discharge is a pure cons, not a kit call.**  The
  mirror's `∀⊑` case only needs to cons the imprecise-only wrapper
  onto the *stored* family — `λ W≼W′ σ → fam W≼W′ (w ∷ σ‡)` plus
  the phantom/endpoint transports — exactly like the two-sided
  `∀⊑∀` case.  No recursion into the kit or the reveal induction is
  involved, so `imp-right-universal-value` and
  `imp-conceal-right-universal-value` live before the mutual block
  and the feared cons/kit circularity never materializes.  The kit
  is needed only to keep `universal-family-kit` total once the new
  wrapper kinds exist.
* **Store freshness is a theorem, not a missing atom field.**  The
  `∋` relation of `TyStore` is telescopic (every witness shifts the
  bound type past the entry), so `store-∋-∉ : Σ ∋ X ⦂ B → X ∉ᵗ B`
  falls out by induction with `shift-∈ᵗ-inversion` — no
  `pairedFresh` field and no atom sweep.  Consequently the slot
  variable does not occur in its own representative, and with
  `replaceTy-self-∉` the replaced imprecise endpoint is free of the
  center.
* **There is no occurs split.**  The pre-existing
  `paired-no-occurrence` (the contrapositive of the planned
  occurrence-transfer mirror, already in `StarNoOccurrence`)
  turns the replaced endpoint's center-freeness into
  center-freeness of the *shared precise endpoint*, derived from
  the caller's own `t` (reveal side) or the built `t‴` (conceal
  side).  The mirror's `∉` premise is therefore available
  unconditionally and the head is total outright; the addendum's
  occurs-present vacuity argument is subsumed.
* **The star-map needs no avoidance premise.**  `star-avoid★ᵖ`
  proves the weakened predicate outright for any derivation with ★
  on the right (all its subderivations stay below ★, so every
  alias leaf takes the exemption).  `subst₂-avoid★` therefore
  takes only two premise functions — avoidance of the same-map's
  insertions and the `∉`-transport along the alias map — and each
  `⊑ ★`-output clause is discharged wholesale by `star-avoid★ᵖ`
  applied to the (possibly stuck) recursive output, which
  typechecks because no matching is needed at the application.

The landed pieces:

* `LR-narrow/Atoms.agda` — `store-∋-¬∈`/`store-∋-∉`.
* `proof/LR-narrow/StarNoOccurrence.agda` — `replaceTy-self-∉`.
* `proof/LR-narrow/AliasAvoid.agda` — `star-avoid★ᵖ`,
  `alias-avoid★-subst₂`, the map-closure lemmas
  (`same-avoid-exts/-insts`, `subst-avoid-map-extend`) and
  `subst₂-avoid★` (the transport along `subst₂-⊑`, mirroring its
  clause and with structure; the alias case maps the exemption by
  `cong (substᵗ σᴿ)` and the strong component by the alias-map
  `∉`-transport).
* `LR-narrow/World.agda` — `openRightBodyImprecision`, the `instᵐ`
  mirror of `openRelatedBodyImprecision`: σᴿ is `singleSubᵗ ★`,
  `same`/`star` discharge the bound variable with the caller's
  `r★`, and `shift-openᵗ` fixes the shifted right endpoint.
* `LR-narrow/SlotSequence.agda` — the `reveal-imprecise` and
  `conceal-imprecise` kinds of the right-side `UniWrap` (shape,
  center-freeness of the precise body, carried target
  `BodyImprecision`, weak avoid-fn); identity on the precise term.
* `proof/LR-narrow/ImpreciseReveal.agda` —
  `replace-right-inst-body-⊑` (the canonical replaced `instᵐ`
  body via `replace★-⊑` at `v = I.X⊑★` and `shift-replace`), the
  two cons functions, and the `∀⊑` dispatches rewired onto them
  (baking `Bc := embI Bᴵ` by with-abstracting `sourceᴵ`);
  `ImpreciseRightExtension` deleted and the `ext` parameter
  stripped file-wide.
* `proof/LR-narrow/UniversalFamilyKit.agda` —
  `open-right-body-avoid★` (rebuilding the instantiation with its
  maps in scope and transferring to the World-built derivation by
  `alias-avoid★-any`, since the World lemma's `where`-functions
  are inaccessible), the two heads
  (`reveal-imprecise-right-head`/`conceal-imprecise-right-head`:
  no β-step — the source chain's head at the canonical
  instantiation `t″`/`t‴`, then the one-sided
  `ImpreciseComposition` whose plug returns the mirrored values
  with the post-bind Σ passed through unchanged; the conceal head
  canonicalizes the caller's `t` to `tᶜ` so avoidance always flows
  from the wrapper's carried data, and reindexes by
  `computations-related-post-bind-reindex` at the end), the two
  chain extensions, and the two `extend-wrap` cases (all four
  embedding equations `refl` at the canonical bodies).

With this the mirror is closed: `imprecise-reveal`,
`imprecise-conceal` and their value forms need nothing beyond the
derivation, its weak avoidance, and the center's absence from the
precise endpoint.  Next in Finding I: item 1 (generalize the alias
atom's representative to a `Ty Δᴾ`), item 3 (the one-sided
alias-slot frame transformers), item 4 (the producer cascades for
`lambda-familyᵇ`/`cast-familyᵇ` via
`related-alias-bind-step-expand`), then retiring the deferred
`universal-familyᵇ` field.

## Finding J — general alias representatives break the ★-projection
## tag coherence (2026-08-27)

Finding I item 1 proposed generalizing `aliasRepName : TyVar Δᴾ` to
`aliasRep : Ty Δᴾ`, claiming the only non-trivial consumer beyond
`reveal-alias`/`conceal-alias` is the `ground-imprecise-targets-agree`
recursion, where "the general rep only adds non-variable base cases".
That claim is WRONG, and the failure is not a proof inconvenience
but a design-level fact about the precision rules.

### J.1  The syntactic lemma is false for general representatives

`ground-imprecise-targets-agree` (proof/LR-narrow/Cast.agda) states
that two derivations from one embedded precise ground to nonstar
embedded imprecise targets agree on the target.  Its alias case
recurses through the representative; with variable representatives
every source along the chain is a variable, the chain bottoms at a
non-alias mode, and the target is forced.  With a general
representative the recursion escapes to arbitrary embedded sources,
where the claim fails outright.  Counterexample: let an alias slot
`X` record `R = `∀ (＇0 ⇒ ＇0)`.  Then from the shared source
`embP R = ∀(＇0 ⇒ ＇0)`:

* `w  : ∀(＇0⇒＇0) ⊑ ★⇒★` by `I.∀⊑` — nonvar, `0` occurs, and the
  premise `＇0⇒＇0 ⊑ ★⇒★` holds at `instᵐ` (both components
  `＇0 ⊑ ★` by `X⊑★`, since the bound variable is
  star-discharged);
* `w₂ : ∀(＇0⇒＇0) ⊑ ∀(＇0⇒＇0)` by `I.∀⊑∀` (componentwise `X⊑X`
  at `extᵐ`).

Both targets are nonstar embedded-imprecise images (`★⇒★` and
`∀(＇0⇒＇0)` are their own preimages), yet they do not even agree
in shape.  Prefixing both with the `alias` rule at `X` gives two
derivations `＇X-emb ⊑ B₁ / B₂` with `B₁ = ★⇒★`, `B₂ = ∀(…)`.
So type precision at an alias variable is NOT shape-functional once
representatives may be ∀-types whose bound variable occurs — the
fork between `∀⊑` (target-transparent, star-discharged binder) and
`∀⊑∀` is exactly the ambiguity.

### J.2  The ambiguity reaches the main theorem

The lemma backs the ★-projection coherence of `related-value-casts`
(the `？`-vs-`？` cases): a dynamic payload carries some
`payload-q : embP Hᴾ ⊑ embI Hᴵ` (`DynamicPayloadShape` stores the
imprecise ground `Hᴵ` existentially), the cast pair carries an
independent `q`, and tag agreement of `Hᴵ` with the projection
ground is derived by running both derivations from the shared
precise source.  With the counterexample's slot:

* value side: seal a ∀-value at `X`, inject at `＇X`; the imprecise
  partner is a `∀⊑`-related fun value injected at `★⇒★`
  (`payload-q` via `alias`+`∀⊑`);
* cast side: precise `⟨★？＇X⟩` against imprecise `⟨★？∀★⟩`, the
  target pair related by `q` via `alias`+`∀⊑∀`.

`cast⊑cast²` (proof/DGG/CastTermImprecision.agda) requires exactly
endpoint-⊑ derivations, so this program pair is term-related.
Operationally the precise projection succeeds (`＇X` against `＇X`)
while the imprecise projection blames (`∀★` against tag `★⇒★`) —
violating `forward-blame` of `ComputationsRelated`.  So under
general representatives the ★⊑★/projection story is not merely
harder to prove; the relation (and the DGG argument through it)
admits a genuine counterexample, and a design decision is needed
before item 1's record flip can land:

1. make the alias premise shape-canonical (restrict the `∀⊑`-route
   at alias-unfolding positions) — must check the producer
   cascades (item 4) and the fundamental property's seal/injection
   cases still go through;
2. record a canonical injection tag in the alias atom and constrain
   `DynamicPayloadShape` at alias-variable grounds to factor
   through it — must check real term pairs cannot inject the same
   sealed value under both readings;
3. weaken the projection coherence (allow the imprecise side to
   blame more at mismatched projections) — changes the DGG
   statement itself;
4. keep variable representatives and redesign the cascade's
   self-alias discharge to avoid general reps — contradicts
   I.3/I.4 as currently planned.

### J.3  What landed anyway

`reveal-alias`/`conceal-alias` (proof/LR-narrow/RevealStructural)
no longer consult the representative's shape: the precise side is
an identity conversion by mode-disjointness as before, and the
imprecise side is discharged by the one-sided imprecise reveal
(`imprecise-reveal`/`imprecise-conceal`, with the avoidance
weakened by `alias-avoid-weaken★` and the exemption taken on the
`center ∉ T` side).  `alias-holds-rep` (Atoms) and
`alias-premise-B-shape` (Closure) are deleted — the reveal path is
now compatible with general representatives.  The remaining
consumers of variable-ness are the tag-coherence layer above and
the mechanical record sweep, both gated on the J.2 decision.

### J.4  Correction: the counterexample does not exist (2026-08-27)

J.2 claimed the ambiguity reaches a term pair and forced a design
decision.  That conclusion was WRONG, and the two lemmas that
settle it are now proved.

**What survives of J.1.**  The type-level fork is real, and is now
checked concretely: with `T = ∀(＇0 ⇒ ＇0)` recorded at an alias
mode, both `＇X ⊑ ★ ⇒ ★` (by `alias` + `∀⊑`, the binder
star-discharged) and `＇X ⊑ T` (by `alias` + `∀⊑∀`) are derivable,
as is `＇X ⊑ ★`.  So `⊑` is genuinely not shape-functional at an
alias variable with a general representative.

**Why that does not reach a program pair.**  A runtime tag check
compares GROUNDS, never arbitrary targets, and two facts pin those
down:

* `proof/LR-narrow/GroundReading.agda` — `ground-readings-unique`:
  two derivations from one source to images of imprecise grounds
  reach the same type.  The `∀⊑`/`∀⊑∀` fork dies here, because a
  `∀`-ground's body is `★` and `star-no-occurrence` then forbids the
  binder from occurring, contradicting `∀⊑`'s occurrence premise.
  The side condition is exactly the alias slots' target
  non-occupancy (`NoAliasImage`).
* `proof/LR-narrow/ConsistencyAvoid.agda` — `avoid-target` /
  `avoid-source`: at a variable whose CONSISTENCY mode is paired
  (`X∼X`), avoidance travels across `∼` in both directions.  This is
  the consistency-side twin of `star-no-occurrence`.

The second lemma kills J.2's program pair directly
(`paired-fork-excluded`): to project at the `∀★` ground and land on
a `∀` type, the cast needs `∀★ ∼ ∀D₀`, i.e. `★ ∼ D₀` under a
`∀ᶜ` binder — which `extᵐ` gives the PAIRED consistency mode, so
`D₀` cannot mention the bound variable.  But the `∀⊑∀` reading of
the same pair transports `0 ∈ A₀` into `D₀`
(`source-occurs-target`, the binder being paired on the `⊑` side
too).  The two requirements are contradictory, so no cast pair can
hold the two readings apart.  In the concrete instance the two
lemmas agree with the syntax: `∀★ ∼ T` is underivable, so the
imprecise program of J.2 cannot be written at all.

**Consequence for the plan.**  `related-value-casts` needs NO new
premise, and none of the four options listed in J.2 is required —
that list is withdrawn.  What remains before item 1's record flip:

1. Rewrite the three call sites of `ground-imprecise-targets-agree`
   (`proof/LR-narrow/Cast.agda`) onto ground-level agreement, using
   `ground-readings-unique` plus the projection cast's own
   consistency, which the call sites already carry.
2. Two routes to a `∀`-shaped projection target are not covered by
   `paired-fork-excluded` and need the same treatment: the `gen_`
   constructor (whose binder mode is `★∼X`, not paired) and
   `bot-intro`.  Both put the bound variable back in scope, so each
   needs its own argument or a refutation from the `⊑` side.
3. Then the mechanical record sweep of I.4 item 1.

### J.5  The two residual routes, resolved (2026-08-27)

J.4 left two ways for a cast to reach a `∀`-shaped projection
target that `paired-fork-excluded` does not cover.  Both are now
settled, and NEITHER is refutable — so step 1 of J.4's plan (the
call-site rewrite) is not a straight substitution.

**`gen_` is real.**  Its binder carries the mode `★∼X`, not the
paired `X∼X`, so ★ crosses it freely and the avoidance argument
does not apply.  The consistency really is inhabited:
`gen-crosses-paired-witness` in
`proof/LR-narrow/ConsistencyAvoid.agda` proves
`★ ⇒ ★ ∼ ∀(＇0 ⇒ ＇0)`, a FUN ground consistent with a `∀` type
whose binder occurs.

With a general alias representative this assembles into a live
configuration of `related-value-casts`' `★⊑★` case.  Take the
alias representative `T = ∀(＇0 ⇒ ＇0)`:

* the precise value is sealed at the alias and injected at its own
  ground `＇X`; its cast projects at `＇X`, the tag matches, and the
  projection does not expand;
* the imprecise value is a function injected at `★ ⇒ ★`; its cast
  projects at `★ ⇒ ★` — the tag ALSO matches — and then expands
  through `gen_` into `T`.

Both readings of the alias variable are derivable (`＇X ⊑ ★ ⇒ ★`
by `alias` + `∀⊑`; `＇X ⊑ T` by `alias` + `∀⊑∀`), so the pair is
related and neither side blames.  This is exactly the branch
`projection-same`/`tag-matched` × `projection-expanded` at
`proof/LR-narrow/Cast.agda:3937`, which today is discharged by
refuting `Dᴵ ≢ Gᴵ`.  That refutation rests on target agreement,
which holds only for variable representatives.  So the branch needs
real content: the precise payload related to the imprecise payload
after its generalization cast.  This is a proof obligation, not a
counterexample — the two results are plausibly related (a sealed
polymorphic value against a `Λ`-generalized one at the alias
premise), but it must be proved.

**`bot-intro` is a different risk.**  It reaches the target
`∀(＇0)`, the UNINHABITED bottom type.  If that branch were
reachable, `related-value-casts` would be false rather than
unproved: the precise side returns a value while the imprecise side
cannot.  For the canonical representative it is unreachable, by two
facts checked in Agda — from a fun-bodied `∀`, `∀⊑∀` would need
`fun ⊑ var` and `∀⊑` would need `fun ⊑ ∀`, and neither has a rule.
A general argument still has to cover representatives whose bodies
are themselves `∀`-towers.

**Revised remaining work for item 1.**

1. An unreachability argument for a bottom projection target,
   general in the representative.
2. The `gen_` branch of the `★⊑★` case: relate the precise payload
   to the generalized imprecise payload.
3. Then the call-site rewrite of J.4 (ground-level agreement via
   `ground-readings-unique`) and the mechanical record sweep.

### J.6  General alias representatives landed (2026-08-29)

All three items above are now implemented.  The cast proof excludes the
bottom target, relates expanded imprecise projections, and uses
`ground-readings-unique` for runtime tag agreement.  Consequently
`AliasSemanticAtom` now records `aliasRep : Ty Δᴾ`; alias binding, future
transport, closing substitutions, and operational binding all preserve an
arbitrary representative type.

The record sweep exposed one additional cast-proof edge.  Chasing an alias
inside `right-dynamic-ground-tag-value-at` reaches the representative's
arbitrary source reading, including `∀⊑`, whereas the old helper accepted a
precise ground source.  The general closure lemma `right-ground-tag-values`
is derived from the existing `imprecise-cast-values` obligation and
`related-computation-values`: ground injection is an imprecise-side cast,
and both endpoints are values.  No new cast obligation is required.
