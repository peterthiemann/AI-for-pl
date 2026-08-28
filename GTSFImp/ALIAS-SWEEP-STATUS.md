# Alias-imprecision sweep — status and continuation notes

Branch: `codex/gtsf-alias-imprecision` (upstream: `peterthiemann`).
Goal: make all of `GTSFImp` green (`make check`) after introducing the
alias mode `X⊑ᵗ T` in `VarImp` and the fused `alias` rule in the
imprecision judgment, then sweep `GTSFImp-Interpreter`, then discharge
the four `∀⊑∀` reveal/conceal obligations
(`GTSFImp-Interpreter/REPLACEMENT-CLOSURE-DESIGN.md` has the plan).

## Where things stand

**GTSFImp is DONE**: `make check` (All.agda under `--safe`, LegacyAll,
and postulate-check with the NON_COVERING baseline) is fully green on
this branch, cosmetics included (80-column pass, no rewrite warnings,
`git diff --check` clean).

The legacy sweep finishing touches beyond the earlier checkpoint:

* `SourceColumnStrip` / `SourceSpineStrip` / `SourceTagSealCore` /
  `TargetTagSealWalk` / `TargetSourceStarAt` / `TargetSourceStarChain`
  and `RightInjInversion²` all take a leading `NoAliasWorld` premise;
  the strip Σ-results additionally RETURN `CTX.NoAliasWorld Wᵒ` for the
  output world (between `qᵒ` and the `SpineValue Core` component), which
  is what lets `TargetWalkLemma`/`TargetWalkProof` feed the core.
* `RightInjInversion²`'s six previously-absurd `with q | ()` clauses
  (var-vs-ground obligations) are discharged with `| alias mode p₁ =
  ⊥-elim (na _ mode)`.
* Its live consumers were updated: `GeneratedProjectionReplacementProof`
  (both replacements take `na`), `ExtraCastRightAtProof`'s four
  structural-project wrappers take `na` after the inversion argument.

**GTSFImp-Interpreter is DONE**: `make check` (check-interpreter,
check-isomorphism, check-lr) is fully green.  How the sweep landed:

* `NarrowWiden` gained mirroring `w-alias`/`n-alias` constructors and
  `NarrowWidenIsomorphism` the corresponding cases, keeping the
  isomorphism exact.
* `LR-narrow/World.agda`'s `World` record gained a `noAlias` field
  (`∀ Z {T} → impEnv core Z ≡ X⊑ᵗ T → ⊥`), discharged by every world
  builder via `lift-alias-inv`; `world-aliases-avoid` derives alias
  avoidance from it.  This encodes "run-time worlds are alias-free
  until the alias bind expansion lands" — step 4/5 replaces the field
  with real avoidance/atom reasoning.
* `ValueImprecisionᵏ` has an endpoint-only alias clause (mirrors the
  bot leaves); the closure/size/no-occurrence lemmas gained alias
  cases and `cong I.⇑ᵛ` mode transports.
* `replace-⊑` takes `AliasesAvoid μ Z` (the alias case is
  CONSTRUCTED, not refuted: the representative survives replacement
  by avoidance, and `replace-alias-not-self` shows no self-alias can
  arise); `replace-left-⊑` takes a `μ Z ≡ X⊑★` mode premise;
  `⊑-base-right-no-var` takes a `μ Z ≡ X⊑★` premise.  Reveal/cast
  proofs refute alias cases at world environments via `noAlias W`,
  and Cast's ground-tag uniqueness lemmas take `NoAliases μ` (from
  upstream `ImprecisionConsistency`).

**Step 4 is DONE** (LR clause and alias atom, tree green):

* `LR-narrow/Atoms.agda` has `AliasSemanticAtom` (precise-only
  allocation, representative embedding pinned by the mode via
  `aliasRep-eq`, no stored derivation), the `alias-entry` kind at
  `X⊑ᵗ T`, `AliasHolds`/`AliasAtomHolds` (payload related at the
  alias *premise*), `alias-holds-map`, `alias-atom-no-target`, and
  weakenings through all three bind cores.
* `EntryLift` has `lift-alias`, extended through the entry lifts.
* `ValueImprecisionᵏ` at `I.alias` is `TypedEndpoints ×
  AliasAtomHolds (Vᵏ (suc k)) (semanticEntry W X) eq p` — same
  index, structurally smaller premise (see the termination note).
* Closure: `value-imprecision-downward` maps the alias payload;
  the three future-lifting lemmas (`-paired`/`-precise`/`-imprecise`)
  refute alias via `noAlias` — they get real alias lifting
  (an `alias-holds-lift` mirroring `dynamic-holds-lift`) in step 5.

**Step 5 is IN PROGRESS** — planning it surfaced **Finding H**
(recorded in `GTSFImp-Interpreter/REPLACEMENT-CLOSURE-DESIGN.md`):
once `Future` gains the alias-bind step, the two-sided reveal
statements are falsified through their own Kripke re-entry, and the
robust fix is derivation-restricted avoidance.  Landed so far, all
green and committed:

* real alias closure under futures (`alias-holds-lift`/`-future`,
  `liftCenterMode-alias`; the three future-lifting closure lemmas
  now have real alias cases);
* `proof/LR-narrow/AliasAvoid.agda`: `AliasAvoidᵖ` (avoidance read
  off exactly the derivation's alias leaves — stable under lifting,
  which creates no leaves), with transports along `⊑-unique`,
  renamings, and from `NoAliases` environments, plus
  `target-occurs-sourceᵖ`;
* `replace-⊑` in its final Finding-H form: premise `AliasAvoidᵖ Z p`
  (binder transports definitional), call sites discharged through
  the still-standing `noAlias` invariant.

**Finding-H step (1) is DONE** (tree fully green — both projects'
`make check`):

* the two-sided sized statements (`RevealAtSized`/`ConcealAtSized`)
  and the whole `RevealStructural` machinery take
  `AliasAvoidᵖ (center s) p` after `p`; Kripke re-entries transport
  it with `alias-avoid-lift-center`/`-lift-body`/
  `-lift-dynamic-body` (in `RevealLifting`), endpoint substs with
  `alias-avoid-subst-left/rightᵉ`, and reindexings with
  `alias-avoid-any` (endpoint-propositional catch-all in
  `AliasAvoid`);
* the real two-sided alias cases (`reveal-alias`/`conceal-alias`):
  `alias-premise-B-shape` pins the alias premise's right side to a
  variable or ★ (via the variable-representative atom), so under
  avoidance both replacements are identities and identity
  reveal/conceal steps close the case; `DynamicReveal`'s alias
  clauses are refuted by mode clash (`star-not-alias`), no world
  invariant needed;
* the absent/inert and dyn variants need NO avoidance (they only
  enter the one-sided precise machinery) — their signatures stay
  clean, so `PreciseReveal`'s wrapper constructions are untouched;
* `UniWrap`'s `reveal-paired`/`conceal-paired` constructors carry a
  wrap-level avoid field `(j : BodyImprecision W B C) →
  AliasAvoidᵖ (suc (center s)) (bodyP j)` (quantified over the
  body imprecision at the unreplaced side — `alias-avoid-unique`
  makes one witness serve all); `extend-wrap` instantiates it at
  the iteration's existential imprecision, and the paired-family
  producers in `RevealStructural` discharge it by lifting their
  own `avoidᵇ`.

**Finding-H step (2) is DONE** (tree fully green — both projects'
`make check`):

* the cast machinery is alias-general: the variable-source lemmas
  take dynamic-mode premises, the alias chain through a dynamic
  ground tag recurses structurally on the derivation
  (`right-dynamic-ground-tag-value-at` rebuilds the alias slot at
  the injected payload via `alias-holds-chain`), the payload
  tag-agreement lemmas route variable grounds through the
  derivation-chase `ground-imprecise-targets-agree` (fuel on
  `sizeᵖ`) plus `grounds-consistent-equal`, and the remaining
  μ-level ground lemmas weaken alias-freeness to non-variable
  sources (`ground-targets-unique⊑-nonvar` upstream);
* `related-value-casts`' alias clause delegates to the
  `paired-cast-values` obligation through a new `open-alias` case
  of `OpenPairedCastCase` — the same open-cases regime as the
  dynamic variable and universal sources;
* `World.noAlias` is GONE.  The `World` record instead carries
  `aliasEntry` (an alias-mode center's entry is an alias entry,
  `IsAliasEntry` on the mode-subst entry); the three bind builders
  discharge it by the entry-weakening with-dance and
  `aliasBindWorld` by construction; `proof/LR-narrow/AliasWorld`'s
  accessors (`world-alias-atom`, `alias-mode-no-paired-holds`,
  `alias-holds-chain`, `alias-no-imprecise-target`) are real;
* `aliasBindCore` (embeddings/stores mirror `preciseBindCore`,
  fresh mode `X⊑ᵗ (⇑ᵗ (embP (＇ rep)))`, bound type `＇ rep`),
  the `-aliasbind` weaken-atom family, the fresh alias atom
  (rep-eq holds by computation), `future-alias`, and
  `aliasBindWorld` are in; every `Future` matcher across the LR
  gained the alias case (mirroring `future-precise`, with the
  alias mode at each `shift-⊑`/`shift-star-map`/`shift-alias-map`
  site and `entry-lift-aliasbind`/`alias-local-imprecision`/
  `liftPreciseContext-alias` analogues);
* `value-imprecision-aliasbind` in `proof/LR-narrow/Closure.agda`
  mirrors the three existing per-step closure lemmas, including
  their documented `TERMINATING` pragma (allocation-order
  well-foundedness — the one inherited pragma of the sweep).

**Finding-H steps (3) and (5) are DONE** (tree fully green):

* the `∀⊑∀` clause stores `UniversalFamily` — a wrap-closed Kripke
  family over the two-sided wrapper algebra `UniWrapᵇ`/`UniWrapsᵇ`
  (paired constructors carry the wrap-level avoid, dynamic and
  inert wrappers convert the precise side only; the carried clause
  data is `BodyImprecisionᵇ`, the plain two-sided body
  imprecision);
* consumers project the empty sequence at the reflexive future
  (definitionally the old chain); the closure transports
  (`universals-phantom`, `universal-family-future`, downward, the
  four per-step lemmas) mirror the right-universal family's;
* the producers: the `reveal-universal`/`conceal-universal`
  assemblies and the four previously-blocked obligations
  (`blocked-precise-reveal`/`-conceal`,
  `blocked-dyn-reveal`/`-conceal-universal`) are cons-projections
  (`λ W≼W′ σ → fam W≼W′ (w ∷ σ)` with the lifted wrapper and the
  wrap-term equalities); `RevealObligations` is DELETED and the
  reveal development (`RevealStructural`, `PreciseReveal`,
  `DynamicReveal`, `UniversalFamilyKit`) is obligation-free;
* the from-scratch producers (`universal-compatible` — the `Λ⊑Λ`
  compatibility — and `Cast`'s `∀ᶜ` cast) build the family through
  the `UniversalFamilyKitᵇ` record (`to-familyᵇ` from
  `UniversalData`, the endpoints-plus-chain presentation).

**REMAINING — step (4) residual**: construct the in-tree
`universal-family-kitᵇ : UniversalFamilyKitᵇ` (currently deferred
as the `universal-familyᵇ` field of `RemainingObligations` in
`FundamentalAssembly`).  Its paired chain extensions follow the
existing `reveal-universal-head`/`conceal-universal-head`; the
inert and dynamic extensions are the flagged largest proofs: their
chain obligations run the wrapper β (`bind Rᴾ`) plus the inner
type application (`bind ＇0`) against the single imprecise β
(`bind Rᴵ`), so the trace pairs `(Rᴾ, Rᴵ)` as the paired bind and
classifies `bind ＇0` with `future-alias` at the just-bound paired
variable (the alias representative is the paired center, so the
alias chain ends at a paired mode) — mirror
`reveal-right-universal-absent-inner` with
`aliasBindWorld (pairedBindWorld W′ Rᴾ Rᴵ r) Fin.zero`.

## Recurring mechanical recipes (used dozens of times already)

1. **`ImpEnvMono` is now a record** (`CTX.imp-env-mono starMono
   aliasAgree`).  Old `mono Z eq = …` definitions fail with
   "Cannot eliminate … with pattern".  Fixes:
   - identity: `CTX.idᵉᵐ`
   - pointwise-equal envs: `CTX.eqᵉᵐ (λ Z → refl)` (with a case-split
     helper when the envs only reduce per constructor index);
   - composition:
     ```agda
     CTX.imp-env-mono
       (λ Z eq → CTX.starMono m₂ Z (CTX.starMono m₁ Z eq))
       (CTX.alias-same-trans (CTX.aliasAgree m₁) (CTX.aliasAgree m₂))
     ```
   - lift/inst worlds: star part via `lift-star-inv` + `cong ⇑ᵛ`,
     alias part via `CTX.alias-same-ext`.
2. **Threading `NoAliasWorld`** (`na`): lemmas that invert `＇X ⊑ B`
   (via `variable-obligation-aligns`, `inner-source-pivot-eq(ᴿ)`,
   `target-seal-rebase-source`, `var-source-nonstar-⊥`,
   `STC.seal-transfer`, `SPT.right-var-obligation-view-na`) take an
   `na` first argument.  Transport it:
   - across `mono : ImpEnvMono W W′`:
     `CTX.no-alias-same (CTX.aliasAgree mono) na`
   - across `liftWorldLeft X⊑★`:
     `CTX.no-alias-lift-left {W = W} {v = X⊑★} (λ ()) na`
     (pin BOTH implicits or you get unsolved metas)
   - across `SmartCommaLiftᴸ`: `CTX.no-alias-smart-comma liftW na`
   - across `TargetInsert`: `TE.no-alias-insert ins na`
   - across `WorldExtendᴿ`: `ECR.WorldExtendᴿ.no-alias-extend ext na`
   - across `ParkedEvolve`: `no-alias-evolve evol na`
   - from `ParkedWorld`: `parked-no-alias pw` (ParkedWorldDef).
3. **`SPT.RightVarObligationView` is now a data type** (`rv-aligned` /
   `rv-aliased`), so the old tuple pattern `X₂ , refl , aligned`
   fails.  Two options:
   - if an `na` is available, switch the `with` to
     `SPT.right-var-obligation-view-na … na p` which returns the OLD
     Σ shape, so `X₂ , refl , aligned` patterns keep working
     (this is what TargetChainProof does);
   - otherwise split `rv-aligned`/`rv-aliased`; for non-var `R` the
     absurd `()` still works (the `R ≡ ＇X₂` field conflicts).
4. **`＇X ⊑ non-var-non-★` is no longer empty**: absurd patterns `()`
   on such obligations fail with "ShouldBeEmpty … alias".  Replace with
   a clause matching `(alias mode p)` and discharge `⊥` via `na _ mode`
   (works when the env or source var reduces), or via
   `var-source-nonstar-⊥ na p nonvar-… nonstar-…`.
5. **Coverage regressions in big legacy with-towers**: when a with-tower
   previously refuted `⊑cast²` premises by emptiness of `＇X ⊑ B`, the
   checker now demands new clauses.  See the end of the
   `target-source-star-at` S=★ block in `TargetChainProof.agda`
   (clauses splitting `vU` into `inj ⦃ Gᵍ = … ⦄` per ground; the
   var-tag ground case is closed with `source-typing² D₂` +
   `store-lookup-unique` + `target-source-star-payload`).  Use it as
   the template if the same shape appears in the remaining files.
6. `⇑ᵛ`-index fixes: hypotheses like `impEnvʷ (lift W) (suc Z) ≡ X⊑★`
   no longer accept the un-lifted `eq`; wrap with `cong ⇑ᵛ eq`
   (also `cong lowerᵛ`, `cong (⇑ᵛ ∘ lowerᵛ)` where lowering is used).

## New helpers added this session (reuse, don't duplicate)

* `CtxImp.agda`: `no-alias-smart-comma`.
* `SealPeelToolkit.agda`: `right-var-obligation-view-na` (Σ-shaped).
* `Parked/ParkedWorldDef.agda`: `parked-no-alias`
  (NB: `parked-initial` now takes a `(∀ Z {T} → μ Z ≡ X⊑ᵗ T → ⊥)`
  premise; concrete sites pass `(λ Z ())` or `(λ ())` at Δ = 0).
* `Inversion/TargetStripProof.agda`: `lowerᵛ`, `lowerᵛ-not-alias`
  (aliases collapse to `X⊑★` when a left binder is lowered; the decay
  and mono for `lowerLiftWorldLeft` take `na` premises).
* `Catchup/InstInversionLambdaProof.agda`: `renameᵛ-comp′`,
  `renameᵛ-cong′`, `⇑ᵛ-as-rename`; `ExactSmartFreshGuard` gained the
  `off-old-no-alias` field and `old-mark-exact` is now stated in
  `renameᵛ`-form.
* `CatchupToMorePreciseDef.agda`: `CatchupToMorePrecise` takes
  `CTX.NoAliasWorld Wᵖ` after the boundary (suppliers derive it from
  `parked-no-alias` / boundary monos — see `SimProof.agda`,
  `DynamicGradualGuaranteeProof.agda`, `FuelDischargeProof.agda`).

## Known cosmetic debt (fix before declaring GTSFImp done)

* Prefer `make agda` / `make agda-legacy` over ad-hoc per-file `agda`
  calls: the live target uses `--safe`, the legacy one does not, and
  mixing flags on shared dependencies invalidates `.agdai` files and
  causes very slow rebuild storms (this is why per-file checks near the
  end of the session took >20 min).

## Step 5 — the remaining work

Discharge `blocked-precise-reveal`, `blocked-precise-conceal`,
`blocked-dyn-reveal-universal`, `blocked-dyn-conceal-universal` in
`GTSFImp-Interpreter/proof/LR-narrow/RevealStatements.agda`, per
`GTSFImp-Interpreter/REPLACEMENT-CLOSURE-DESIGN.md` ("Consumer
rewrites").  Concretely:

* an `aliasBindWorld` (alias variant of the precise bind expansion:
  needs no `⊑ ★` derivation; sets the fresh mode to
  `X⊑ᵗ (⇑ᵗ (embP R))` and the entry to a fresh alias atom);
* removing the `World.noAlias` field — every refutation that leans
  on it must become a real case: the reveal machinery
  (`reveal-at`/`conceal-at`, `dyn-reveal-go`/`dyn-conceal-go`,
  `related-value-casts`' alias clause, `right-dynamic-ground-tag-…`),
  the replacement lemmas' `world-aliases-avoid` uses, and the three
  Closure future-lifting lemmas (write `alias-holds-lift` mirroring
  `dynamic-holds-lift`, plus `alias-holds-future`);
* the `∀⊑∀` producers close their head through the producer's body
  relation; then `RevealObligations` becomes empty and is deleted.

The interpreter-facing surface (`CastTermImprecision(+2Typing)`,
`CtxImp`, `WorldInsert`) is alias-general with no `na` hypotheses;
keep it that way.

Standing constraints: no postulates, no holes outside this WIP, no
catch-all `_` cases, no new TERMINATING pragmas, ≤ 80 columns,
`CastTermImprecision.agda` must not be edited textually (only the
approved `ImpEnvMono`-record strengthening reaches it via imports),
commit each green milestone with an imperative message, push to
`peterthiemann` (pushes to `origin` 403).

## Step 6 — Finding I and the in-tree family plan (2026-08-27)

Step 5 landed (`629a6b00`): the four obligations are family
projections and `RevealObligations` is gone.  The residual is the
`universal-familyᵇ : UniversalFamilyKitᵇ` field of
`RemainingObligations`.  Analysis results, in order:

* The chain-based kit (`to-familyᵇ : UniversalData → UniversalFamily`)
  is UNPROVABLE: a chain undercharacterizes the value, and no
  per-wrapper factorization exists at any level.  Do not revive it.
* The only live in-tree kit consumer is `related-value-casts`' `∀ᶜ`
  clause.  The assembly's `Λ⊑Λ²` case routes through the deferred
  `universal-intro`, and `universal-fundamental` has no in-tree
  consumer, so the Λ-producer path stays deferred.
* Every `⦂∀`-application β (`β-Λ`, `β-reveal-∀`, `β-conceal-∀`,
  `β-gen`) BINDS the applied type; the `∀ᶜ` cast-β is PURE.  Peeling a
  wrapper stack therefore binds `Rᴾ` once and then re-binds `＇0`
  (alias binds) on the precise side; the imprecise side binds only at
  paired wrappers (inert/dyn wrappers do not touch the imprecise term).
* Finding I: `UniversalsRelated`'s head fixes the post-bind world to
  `pairedBindWorld W′ Rᴾ Rᴵ r`, i.e. the FIRST fresh center slot must
  be the paired slot.  A Λ-producer can honor that (the imprecise Λ-β
  supplies the paired bind), but the `∀ᶜ` producer under a σ with NO
  imprecise-side wrappers cannot: its precise side must bind `Rᴾ`
  first (one-sided), slot modes are fixed at allocation, and no world
  class exists for a one-sided bind of an arbitrary type against an
  arbitrary imprecise counterpart.  This is the original blocked-⋆
  gap resurfacing at the producer; the design doc's "symmetric, no
  gap" claim for plan (b) was wrong.

The fix (three parts, all in-tree, no new obligations):

1. Relax the `∀⊑∀` head: replace
   `PostBindValueRelation (future-paired future-refl r) s` by
   `FutureValueRelation s` in `UniversalsRelated` (LogicalRelation).
   Producers weaken (`post-bind-weaken` exists); consumers only ever
   thread the factoring, never inspect the bound.  Leave
   `RightUniversalsRelated` alone (its one-sided bound is realizable).
2. Generalize `AliasSemanticAtom`: `aliasRepName : TyVar Δᴾ` becomes
   `aliasRep : Ty Δᴾ` (store binds `aliasRep`, `aliasRep-eq` embeds
   it).  Mode `X⊑ᵗ T` and the GTSFImp `alias` rule are already
   general.  A "self-alias" bind of `Rᴾ` at mode
   `X⊑ᵗ (embP Rᴾ)` then lets `r : Rᴾ ⊑ᵂ Rᴵ` itself discharge the
   alias premise (`＇0 ⊑ Rᴵ` via one `I.alias` hop) — the missing
   world class.  External field uses are tiny: Closure ~1306,
   AliasWorld `alias-holds-chain`, Cast ~489.
3. Build the `∀ᶜ` family directly in `proof/LR-narrow/Cast.agda`
   (import the assembled `reveal-structural`/`conceal-structural`/
   one-sided entry points — RevealStructural closes its own induction
   and does not depend on Cast): per wrapper, paired-expand when both
   sides' next steps bind, else the NEW `related-alias-bind-step-expand`
   (BindStepExpansion, mirrors the precise variant with
   `aliasBindWorld W R`); at the center, pure cast-βs + the SOURCE
   family's head at the composite future with `σ = []` and the
   alias-chain instantiation, framed by `cast-computations-related`.
   Then delete `UniversalFamilyKitᵇ`, its module params, and the
   `universal-familyᵇ` field.

### Step 6 progress (2026-08-27, commits 7c5ecbc6..389d5164)

Landed, green, pushed:

* `7c5ecbc6` — the `∀⊑∀` head relaxed to `FutureValueRelation s`
  (Finding I.2).  Producers weaken; the six `TypeApplication`
  consumers, the reveal producers, Closure transports, Universal,
  and Cast's `universal-head` all re-plumbed.  The right-universal
  head keeps its realizable one-sided bound.
* `c5f15e05` — `related-alias-bind-step-expand` +
  `paired-returns-alias-bind-step` + `alias-step` in
  `proof/LR-narrow/BindStepExpansion.agda` (mirrors the precise
  variant over `aliasBindWorld`; the step binds `＇ rep`).
* `389d5164` — `UniversalFamilyKitᵇ` reshaped from the UNPROVABLE
  chain-in/family-out statement to the two honest producer
  obligations `lambda-familyᵇ` and `cast-familyᵇ`;
  `universal-compatible` takes the family callback directly;
  Cast's `∀ᶜ` clause passes its concrete source data; the dead
  chain builders in the `∀ᶜ` where-block were deleted
  (`UniversalData`/`universal-dataᵇ` are gone).

REMAINING to discharge the (now true) kit fields — the full program
is Finding I.4 in `REPLACEMENT-CLOSURE-DESIGN.md`:

1. Generalize `AliasSemanticAtom`'s representative to a `Ty Δᴾ`
   (self-alias binds).  Mechanical everywhere EXCEPT
   `reveal-alias`/`conceal-alias`, which lose `alias-holds-rep`
   (rep-is-a-variable) and need item 2.
2. New sized statement family: the imprecise-side-only reveal (the
   mirror of `PreciseRevealAt`, center ∉ LHS), plus the
   imprecise-only wrapper kind in `UniWrapᵇ` it forces.
3. New one-sided frame transformers at alias slots (the cascade's
   residual conversions after an alias peel); derivation level is
   the landed `replace-left-⊑`.
4. The two producer cascades (`cast-familyᵇ` per the peel schedule;
   `lambda-familyᵇ` likewise but with every first peel paired
   against the Λ-β).  Note: even the Λ cascade needs items 1–3 for
   σ with inert/dyn wrappers (surplus precise peels).

Do NOT revive a chain-based kit; do NOT re-tighten the `∀⊑∀` head.

### Step 6, item 2 progress (2026-08-27, second session)

* `f421fdad` — imprecise-only wrapper kinds `reveal-impreciseᵇ`/
  `conceal-impreciseᵇ` in `UniWrapᵇ` (SlotSequence).
* `proof/LR-narrow/ImpreciseReveal.agda` (new, in All) — the full
  imprecise-side one-sided reveal/conceal family
  (`ImpreciseRevealAt`/`ImpreciseConcealAt` + value-level entry
  points), total over derivations, standalone recursion by
  `sizeᵖ`, no TERMINATING pragma.  The `∀⊑` case is threaded as
  the `ImpreciseRightExtension` record (two value-level fields);
  nothing consumes the mirror yet, so no deferred obligation is in
  the theorem path.  New reusable pieces: `paired-var-right-⊑`
  (paired-variable right inversion under avoidance),
  `alias-holds-imp-map`, `embI-replace-eq`/`embI-replace-body-eq`,
  `replace-right-⊑`/`replace-right-body-⊑`, `lift-center-∉ᵗ`/
  `lift-center-body-∉ᵗ`.
* REMAINING for item 2: the right-side `UniWraps` imprecise-only
  kind + the right-kit chain extension discharging
  `ImpreciseRightExtension` — needs a ⊑-substitution
  (instantiation) lemma and the occurs-vacuity argument; the full
  plan is in REPLACEMENT-CLOSURE-DESIGN.md ("Remaining for item
  2").

### Step 6, item 2 — weakened avoidance landed (2026-08-27)

`AliasAvoid★ᵖ` (the ★-right-exempt variant: at an alias leaf,
`(B ≡ ★) ⊎ (c ∉ᵗ T)`) now lives beside `AliasAvoidᵖ` in
`proof/LR-narrow/AliasAvoid.agda`, with the full transport set:
`alias-avoid-weaken★` (strong implies weak),
`alias-avoid★-unique`/`-any`, `alias-avoid★-subst-left`/`-rightᵉ`,
`alias-avoid★-rename`, and the occurrence transfer
`target-occurs-source★ᵖ` (the exempted leaves have ★ on the right,
where nothing occurs).  The three future-lifting transports
(`alias-avoid★-lift-center`/`-body`/`-dynamic-body`) are in
`proof/LR-narrow/RevealLifting.agda`.  Next per the design doc's
addendum: the weakened `replace-⊑` (★-right alias leaves reuse
their premises unreplaced), then re-thread `ImpreciseReveal` onto
`AliasAvoid★ᵖ`.

### Step 6, item 2 — weakened replacement landed (2026-08-27)

`replace★-⊑` and `replace-alias-not-self★` now sit beside their
strong versions in `proof/LR-narrow/ReplaceImprecision.agda`,
taking `AliasAvoid★ᵖ`.  All clauses mirror `replace-⊑`; the one new
case is the exempted alias leaf (`inj₁ refl`), where the ★ right
endpoint is fixed by the replacement, the alias variable is
mode-disjoint from the slot, and the leaf is rebuilt VERBATIM —
`I.alias eq {notSelf} p` — reusing the unreplaced premise and the
original notSelf witness.  Next per the design doc's addendum:
re-thread `ImpreciseReveal` from `AliasAvoidᵖ`/`replace-⊑` onto
`AliasAvoid★ᵖ`/`replace★-⊑` (mechanical: the mirror's alias case
extracts the ∉-component at UniShape types, where the ★ branch is
refuted by the embedding equation; `paired-var-right-⊑` gets the
same split, with the ★ branch refuted by its variable right
endpoint).

### Step 6, item 2 — mirror re-threaded onto the weak layer
### (2026-08-27)

`proof/LR-narrow/ImpreciseReveal.agda` now runs entirely on
`AliasAvoid★ᵖ`/`replace★-⊑`: the statements, the extension record's
fields, and every worker take the ★-right-exempt avoidance.  The
imprecise-only wrapper kinds in `UniWrapᵇ` carry the weak avoidance
function too (their peels only ever go through the mirror's own
frame transformers, never the two-sided machinery).  Structure of
the exemption handling:

* `shape-star-∉` discharges the ★ branch at fun- and ∀-shaped
  types (the embedding of a `UniShape` type is never ★), so the
  alias workers extract the strong `c ∉ᵗ T` component exactly
  where the replacement is real.
* At the unseal configuration and in `paired-var-right-⊑`, the ★
  branch contradicts the variable right endpoint outright
  (with-abstract the exemption equation and refute; a standalone
  `＇Z ≡ ★ → ⊥` helper stalls on metas, the with-form does not).

The extension-head can now be fed derivations whose star-copied
subderivations carry no avoidance.  Next per the design doc's
addendum: the right-side `UniWraps` imprecise-only kind and the
right-kit chain extension (the instᵐ instantiation via `subst₂-⊑`
transporting the weak predicate, plus the occurs-vacuity split).

Step 6, item 2 — chain extension landed, extension record deleted
(2026-08-27).  The right-side `UniWraps` gained the imprecise-only
`reveal-imprecise`/`conceal-imprecise` kinds and the kit gained
their chain extensions, so the mirror's `∀⊑` cases now cons the
wrapper onto the stored family directly and
`ImpreciseRightExtension` is gone (the `ext` parameter stripped
from the whole mirror).  Load-bearing simplifications found on the
way:

* The cons is kit-free (a projection of the stored family), so
  there is no circularity between the mirror and the kit.
* `store-∋-∉` (new, in `LR-narrow/Atoms.agda`): the telescopic
  store lookup makes representative freshness a theorem, so the
  planned occurs-present vacuity split disappeared entirely — the
  heads derive the center's absence from the precise endpoint
  unconditionally via the pre-existing `paired-no-occurrence`
  applied to the replaced-endpoint derivation, with
  `replaceTy-self-∉` killing the replaced imprecise endpoint.
* `star-avoid★ᵖ` (new): any `⊑ ★` derivation satisfies the weak
  predicate outright, so `subst₂-avoid★` (the transport along
  `subst₂-⊑`, new in `proof/LR-narrow/AliasAvoid.agda`) needs no
  premise for the star map and discharges every `⊑ ★` output
  clause wholesale.
* `openRightBodyImprecision` (new, `LR-narrow/World.agda`): the
  `instᵐ` instantiation with σᴿ = `singleSubᵗ ★` and the bound
  variable discharged at the caller's `r★`;
  `open-right-body-avoid★` (kit) transports the weak predicate by
  rebuilding the instantiation and transferring by uniqueness.

`make check` green.  Next: Finding I items 1 (alias representative
as a `Ty Δᴾ`), 3 (alias-slot frame transformers) and 4 (the
producer cascades), then retiring `universal-familyᵇ`.

Step 6, item 1 (partial) — alias reveal cases re-based; Finding J
recorded (2026-08-27).  `reveal-alias`/`conceal-alias` in
`RevealStructural` now discharge the imprecise endpoint through the
one-sided imprecise reveal (`imprecise-reveal`/`imprecise-conceal`)
instead of the variable-representative shape analysis: the precise
side is an identity by mode-disjointness as before, the avoidance
weakens with `alias-avoid-weaken★`, and `alias-holds-rep` /
`alias-premise-B-shape` are deleted.  The reveal machinery is now
compatible with general alias representatives.

The record flip itself is BLOCKED by Finding J (see
REPLACEMENT-CLOSURE-DESIGN.md): with a ∀-shaped representative
whose binder occurs (`R = ∀(＇0⇒＇0)`), the `∀⊑`/`∀⊑∀` fork makes
`＇X ⊑ B` non-shape-functional, `ground-imprecise-targets-agree`
becomes false, and a term-related program pair exists whose
imprecise ★-projection blames while the precise one succeeds —
the ★-projection coherence (and the DGG argument through it) needs
a design decision before item 1 can complete.

Step 6, item 1 — Finding J corrected; the blocker is gone
(2026-08-27).  Two new proved modules in GTSFImp-Interpreter:

* `proof/LR-narrow/GroundReading.agda` — `ground-readings-unique`:
  ground readings of a type are unique, for GENERAL alias
  representatives.  Replaces the false-for-general-reps target-level
  agreement lemma.
* `proof/LR-narrow/ConsistencyAvoid.agda` — `avoid-target` /
  `avoid-source`: a paired consistency binder cannot be crossed by
  ★, the consistency twin of `star-no-occurrence`; and
  `paired-fork-excluded`, which refutes the Finding J program pair.

Net: the ★-projection coherence does NOT need a new premise, and
the design decision demanded by the earlier Finding J writeup is
withdrawn (see J.4 in REPLACEMENT-CLOSURE-DESIGN.md).  Remaining
before the record flip: rewrite the three
`ground-imprecise-targets-agree` call sites in
`proof/LR-narrow/Cast.agda` onto ground-level agreement, and cover
the `gen_` and `bot-intro` routes to a ∀-shaped projection target
(their binder modes are not paired, so `paired-fork-excluded` does
not apply to them).

Step 6, item 1 — the two residual consistency routes checked
(2026-08-27).  Neither is refutable (Finding J.5):

* `gen_` — its binder mode is `★∼X`, not paired, so ★ crosses it.
  `gen-crosses-paired-witness` (proof/LR-narrow/ConsistencyAvoid)
  proves `★ ⇒ ★ ∼ ∀(＇0 ⇒ ＇0)`.  With a general representative
  this makes the branch at proof/LR-narrow/Cast.agda:3937 live:
  precise projects at its ground and stops while imprecise projects
  at its own matching ground and expands through the
  generalization.  The branch is currently discharged by refutation
  and now needs a real proof.
* `bot-intro` — reaches the uninhabited `∀(＇0)`.  Unreachable for
  a fun-bodied representative (`fun ⊑ var` and `fun ⊑ ∀` have no
  rules, both checked); a general argument is still owed, and this
  one matters more, since a reachable instance would falsify
  `related-value-casts` rather than merely leave it unproved.

So the call-site rewrite is NOT a straight substitution.  Order of
work: bottom-target unreachability, then the `gen_` branch, then
the ground-level rewrite and the record sweep.
