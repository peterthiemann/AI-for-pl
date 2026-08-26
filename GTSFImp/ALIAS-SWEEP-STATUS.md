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

**NEXT**: sweep `GTSFImp-Interpreter` to green (see below), then the
step-4/5 work.

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

## After GTSFImp is green

1. Sweep `GTSFImp-Interpreter` to green (renamed insert signatures
   such as `liftBoth-insert` bind modes, `LR-narrow/World.agda` shift
   patterns, `FundamentalAssembly`'s WorldInsert uses, worker-type `na`
   where it reaches the interpreter surface).  The interpreter-facing
   surface (`CastTermImprecision(+2Typing)`, `CtxImp`, `WorldInsert`)
   is alias-general with no `na` hypotheses; keep it that way.
2. Then the actual step-4/5 work: the LR alias clause/atom kind and the
   alias bind expansion discharging `blocked-precise-reveal`,
   `blocked-precise-conceal`, `blocked-dyn-reveal-universal`,
   `blocked-dyn-conceal-universal` in
   `GTSFImp-Interpreter/proof/LR-narrow/RevealStatements.agda`,
   per `GTSFImp-Interpreter/REPLACEMENT-CLOSURE-DESIGN.md`.

Standing constraints: no postulates, no holes outside this WIP, no
catch-all `_` cases, no new TERMINATING pragmas, ≤ 80 columns,
`CastTermImprecision.agda` must not be edited textually (only the
approved `ImpEnvMono`-record strengthening reaches it via imports),
commit each green milestone with an imperative message, push to
`peterthiemann` (pushes to `origin` 403).
