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

`IntegratedNominalProjection.matched-query-observed` proves the value-level
nominal boundary premise. If `Matched W X Y`, both query names have direct
`ℕ` representation, and the input packets are `dataDynamic`-related, then
`Vᴵ⟨X?⟩ ↑ unseal X ℕ` and `Vᴾ⟨Y?⟩ ↑ unseal Y ℕ` are observed at
`natural`. Successful target matching forces the matching source name by
injectivity. Store lookup uniqueness gives the natural payload, and the
actual projection and unseal steps return the shared number. Other cases
produce precise blame; disjointness excludes a precise-only packet from
matching an occupied query.

Arbitrary sealing-chain packets are covered in the mismatch branches. The
query's own representation is still restricted to direct `ℕ`. This theorem
does not yet lift nominal queries over arbitrary operand computations or
decode a matched alias chain.

### Escaping producer: `E13` and `E15` before projection

`IntegratedEscapingProducer` examines `F = Λα.λx:α.x⟨α!⟩` before the final
`ℕ?` query. The actual returned values are:

- `F[ℕ] n` returns `(n ↓ seal Z ℕ)⟨Z!⟩`, after allocating `Z↦ℕ`.
- `(F ↑ ∀↑ id↑ (α⇒★))[ℕ] n` returns
  `((n ↓ seal X ℕ) ↓ seal Y X)⟨Y!⟩`, after allocating `X↦ℕ`, then `Y↦X`.

The post-run world makes `X` private and matches `Y` with `Z`. The checked
`wrapped-call-observed` theorem relates these calls at `dataDynamic` for
every natural input and index. It does not identify `X` with `Y`, or resolve
both nominal tags to `ℕ`. In particular the alias chain is part of the
returned value evidence, not an erased annotation.

For the erased-binder pair, `(λx:★.x) (n⟨ℕ!⟩)` returns the natural-tagged
packet and `F[ℕ] n` returns the `Z`-tagged packet. The post-run world marks
`Z` precise-only. `erased-call-observed` relates these **returned packets**,
before any blame occurs. Composing each theorem with `natural-query-observed`
recovers the complete E13/E15 observation through the common semantic model.

This is an integrated producer/nominal/frame test. It is stronger than merely
checking the final observations, but weaker than relating the universal at
every instantiation type or proving the fundamental property.

`IntegratedProducer.adapters-related` additionally relates the returned
functions at `arrow natural dataDynamic`: the two-layer `X↦ℕ, Y↦X` adapter
and the one-layer `Z↦ℕ` adapter, assuming `Matched W Y Z`. This is proved
for every index, every future world, and every related natural argument.
The lifted evaluator equations return after five and three keep steps,
respectively, and `dataDynamic`'s future-closure theorem supplies the packet
evidence. There is no assumed adapter-compatibility field.

The producer module's `payload-family` proves the result-type equalities;
it does **not** supply a `NaturalUniversalValues` inhabitant. Keeping that
distinction explicit prevents the successful adapter test from being reported
as full universal compatibility.

### Active negative controls

`missing-capability-rejected` proves that even two identical nominal packets
are unrelated in an empty capability world. Together with the concrete
fresh-producing calls, this rules out freezing the initial capability set
while merely growing physical scopes. The implemented observation therefore
returns an explicit future world, not just future stores.

`same-representation-not-related` rejects swapping two names with equal
representation. `occupied-erasure-rejected` rejects using the precise-only
alternative at an occupied match; `fresh-erasure-allowed` checks that the
legitimate alternative remains inhabited. `different-data-rejected` rejects
unequal natural payloads at every index, including zero. These are statements
about this model's value relation, not conclusions drawn from matching final
program outputs.

None of these controls refutes the implemented fragment. They refute the
stronger frozen-world, representation-equality, unconditional-erasure, and
payload-index-loss shortcuts. The old regressions remain independently live;
their successful checking is not counted as a new proof of the missing
general dynamic or universal clauses.

## Shared suite and what its results establish

| Evidence | What is checked | What it does not establish |
|---|---|---|
| `IntegratedDataExperiments` | Same-name packets, distinct same-representation names, occupied-erasure exclusion, positive precise-only erasure, unequal payload rejection even at zero, missing-capability rejection, and arguments created in a future world. | A general interpretation of all dynamic payloads. |
| `IntegratedProjection` | Natural query of all related data packets and arbitrary observed operands, at all indices. | Expanded projections, bottom casts, or general nominal-query/unseal compatibility. |
| `IntegratedNominalProjection` | Matched direct-natural nominal query and unseal of all related data packets, with alias-packet mismatch and precise-only exclusion. | Aliased query representations or arbitrary operand computations. |
| `IntegratedFrameComposition` | Three-direction composition with actual post-run worlds and histories. | The missing primitive boundary premises. |
| `IntegratedSuite` | E1–E5, E13–E24, N1/N2 interpreted by the same `Observed natural`, at every index. | Primitive compatibility from their final data/blame outcomes. |
| `IntegratedEscapingProducer` | E13/E15 calls related at `dataDynamic` with actual fresh post-run capabilities, then composed with natural projection. | A full universal value relation or arbitrary producer bodies. |
| `IntegratedProducer` | Returned one-/two-layer adapter functions related at `arrow natural dataDynamic`, for all indices, futures, and related natural arguments. | Membership of the originating universals in `naturalUniversal`. |
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

## Assessment and next gate

The combined direction has a nonempty working model, semantic packet and
function witnesses, and a reusable composition theorem whose natural-query
premise is actually discharged. It is no longer merely three compatible
informal constraints. The evidence supports continuing with one architecture
containing `A`, `B`, and `C′`; it does not support replacing the live LR yet.

The next focused producer gate is to inhabit `naturalUniversal` for the
concrete payload producer and its identity-universal wrapper, at arbitrary
future scopes. Reuse the checked adapter function theorem, but prove the
instantiation/allocation prefix and its post-run world uniformly. That closes
the explicit gap between a successful concrete call and universal membership.

After that, a general `★` payload interpretation, arbitrary instantiation
types/bodies, and the old-world/CTI bridge remain substantive design work.
Their statements must preserve these regressions and discharge real
compatibility premises. Neither the repeated whole-run suite nor the
natural-only universal interface supplies those results automatically.

## Verification and checkpoints

The completed experiment passes:

- The Agda MCP aggregate load of `LR-narrow/LRNarrowAll.agda`, with no
  remaining goals, invisible metavariables, or error diagnostics.
- Independent `make -C GTSFImp-Interpreter check`, including the interpreter,
  narrow/widen isomorphism, full LR aggregate, and both historical regression
  targets.
- A scan of the new proof modules for holes, postulates, and termination or
  positivity escapes, plus `git diff --check`.

The live imprecision, reduction, CTI, computation relation, and value relation
files are unchanged from the starting checkpoint `c8c37038`. The only change
to an existing cast proof is the operational-lemma extraction noted above.

Successful milestones were committed and pushed separately: kernel and
worlds (`dae52c3d`), data/frame/query compatibility (`9b5c442b`), escaping
producer packets (`a550b089`), and finally all-futures adapter compatibility
and direct-natural nominal queries. No counterexample to the implemented
fragment was found; the broader obligations listed above remain unvalidated.
