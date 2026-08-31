# Integrated `A+B+C′` experiment

Date: 2026-08-31. Branch: `codex/gtsf-alias-free-experiment`.

This experiment implements one shared semantic kernel, not three competing
LRs. The reference regression matrix is
[LR-PRINCIPLE-REGRESSIONS](LR-PRINCIPLE-REGRESSIONS.md). The live LR, CTI,
calculus, and evaluator remain unchanged. Operational tag lemmas formerly
local to `proof.LR-narrow.Cast` are factored into `GroundTagSteps`; their
statements and proofs are unchanged.

## Definition and scope

### `A`: independently growing scopes and observations

`IntegratedWorld` indexes a finite world by the actual two `PhysicalScope`s.
There is no common physical scope, equal-fuel requirement, or lowering of
returned closures into the initial scope.

`IntegratedModel.Observed A W k Mᴵ Mᴾ` has these three clauses:

1. If `Mᴵ` returns `Vᴵ` using `n < k` fuel, then `Mᴾ` either blames or
   returns `Vᴾ` at some independent fuel. In the return case there is a world
   `W′` in the two actual post-run scopes, extending `W`, with
   `related A W′ (k ∸ n) Vᴵ Vᴾ`.
2. If `Mᴾ` returns `Vᴾ` using `n < k` fuel, then `Mᴵ` returns `Vᴵ` at
   some independent fuel, with the analogous post-run world and relation.
3. If `Mᴵ` blames using `n < k` fuel, then `Mᴾ` blames at some fuel.

`SemanticType` packages endpoint types, a value relation, typing/value
evidence, downward closure, and future closure. Concrete constructions are
`natural`, `dataDynamic`, and `arrow`. The arrow test quantifies over every
future world and every related argument there, not just renamed arguments
that already existed at the function's initial scope.

`naturalUniversal` is explicitly a **natural-instantiation test interface**.
It does not interpret arbitrary instantiation types or an arbitrary `∀` body.
Its `NaturalFamily` states both post-instantiation endpoint equalities. Merely
declaring that interface is not counted as a producer proof.

### `B`: nominal matches and precise-only payloads

World growth permits private allocation on either side, paired allocation,
and a precise-only natural allocation. Paired entries may have arbitrary
representation types; in particular, matching an alias-chain name on one
side with a directly represented name on the other is not ruled out.

`Matched W X Y` is an injective partial correspondence. `PreciseOnly W Y`
is disjoint from its precise domain. `Future p q W W′` preserves both
capabilities under the two actual scope embeddings. Neither capability is
inferred from representation equality or from the free variables of a
function's type.

`NaturalPayload S A n V` means exactly:

- `A = ℕ` and `V = n`; or
- `A = X`, the physical store contains `X↦R`, and
  `V = U ↓ seal X R` with `NaturalPayload S R n U`.

Thus finite nominal alias chains are included. A ground packet is that
payload with its actual ground injection, including its consistency
environment and exact runtime syntax. At `dataDynamic`, the three clauses
are:

- natural-tagged packets carrying the same `n`;
- packets tagged `X` and `Y`, carrying the same `n`, with `Matched W X Y`;
- a natural-tagged imprecise packet and a `Y`-tagged precise packet,
  carrying the same `n`, with `PreciseOnly W Y`.

Each clause is available at every index with the same payload condition;
tagging does not add an unjustified index decrement. Typing, valuehood,
downward closure, and future closure are proved for these clauses.

This is a **data fragment**, not the final `★` interpretation. Functions,
universals, Boolean payloads, and dynamic-in-dynamic payloads are not admitted
by `dataDynamic`.

### `C′`: actual frame composition

`IntegratedFrameComposition.frame-observed` proves the following. If
`Observed A W k Mᴵ Mᴾ` and, for every pair of operand histories, resulting
future world `W′`, `j ≤ k`, and `A`-related returned values, the transported
frames produce computations observed at `B,W′,j`, then the framed operands
are observed at `B,W,k`.

The proof composes the operand and frame histories and their world futures.
It does not postulate boundary compatibility. It also does not discard,
commute, or cancel boundaries with equal endpoint types.

`IntegratedProjection.natural-query-values` discharges a concrete boundary
premise: applying `ℕ?` to every pair in `dataDynamic` yields observations at
`natural`. Natural tags return the shared number. Matched and precise-only
nominal tags make the precise query blame. The proof uses actual evaluator
tag steps, not the live LR's open cast obligations.

`natural-query-observed` then uses the common frame theorem to establish
the same result for **arbitrary observed operand computations**, including
allocating operands. Its frame transports the real consistency environment.

## Shared suite and what its results establish

| Evidence | What is checked | What it does not establish |
|---|---|---|
| `IntegratedDataExperiments` | Same-name packets, distinct same-representation names, occupied-erasure exclusion, and arguments created in a future world. | A general interpretation of all dynamic payloads. |
| `IntegratedProjection` | Natural query of all related data packets and arbitrary observed operands, at all indices. | Expanded projections, bottom casts, or general nominal-query/unseal compatibility. |
| `IntegratedFrameComposition` | Three-direction composition with actual post-run worlds and histories. | The missing primitive boundary premises. |
| `IntegratedSuite` | E1–E5, E13–E24, N1/N2 interpreted by the same `Observed natural`, at every index. | Primitive compatibility from their final data/blame outcomes. |
| Existing nominal/replacement controls | E6–E12 retain their typing, evaluator, non-value, and impossible-type-relation results. | New integrated observations for the type-level impossibility statements. |
| Existing historical regression target | Ground-cast and occupied-slot projection counterexamples still check. | Closing the new model's expanded/bottom cast cases. |

Whole-program observations use independent sufficient fuel bounds, not an
equal-fuel premise. In the natural-return cases the model preserves all
capabilities in the initial world while extending along the actual run
histories. These observations do not derive an intermediate tag match from
the fact that both complete programs return the same number.

## Current limits

1. This is not a fundamental-property theorem. No translation of arbitrary
   CTI derivations into `SemanticType`/`Observed` has been proved.
2. The finite world syntax constructs capabilities through scope growth;
   it has no general initialization from the live LR's old-root worlds or
   general rebase theorem. The nominal experiments use allocation histories
   rooted at empty stores. Whole-run suites with nonempty roots do not thereby
   install matches for those old root entries.
3. The natural-instantiation interface is weaker than full universal
   semantics. General producer recursion, type substitution, arbitrary
   bodies, and the R16 size-growth issue still require a proof.
4. The nine open paired cast gates and the one-sided cast obligations in the
   reference matrix are not discharged wholesale. Data-query compatibility
   closes a narrow boundary premise, not all base/variable-dynamic cases.
5. Generic frame composition only composes boundaries whose premises have
   been proved. Repeated examples do not justify universal cancellation.

The appropriate acceptance criterion is therefore a checked integrated
fragment with specific semantic boundary proofs and preserved regressions,
not a declaration that the full candidate architecture is already sound.
