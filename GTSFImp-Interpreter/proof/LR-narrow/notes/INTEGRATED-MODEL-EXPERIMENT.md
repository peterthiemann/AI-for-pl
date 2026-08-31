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
that record and the adapter theorem alone do **not** supply a
`NaturalUniversalValues` inhabitant. The next section supplies the separate
membership proof, without extending the interface to arbitrary type arguments.

### Concrete universal membership

Let `F = Λα.λx:α.x⟨α!⟩` and `r = ∀↑ id↑ (α⇒★)`.
`IntegratedUniversal.producer-related` and `wrapper-related` prove,
respectively, that `F` is related to `F` and `F ↑ r` is related to `F` at
`naturalUniversal payload-family`, for every index and every initial world.
The theorems allow arbitrary physical roots and scopes, and retain the actual
consistency environments in the terms.

The membership proof discharges the universal record's future-instantiation
field: for every pair of scope futures and every future world, instantiate
the lifted values at `ℕ` and obtain `Observed (arrow natural dataDynamic)`.
`IntegratedUniversalSteps` proves the uniform evaluator prefixes, not just
closed test runs:

- `F[ℕ]` takes one step, allocates `Z↦ℕ`, and returns the one-layer adapter.
- `(F ↑ r)[ℕ]` takes three steps, allocates `X↦ℕ` then `Y↦X`, and returns
  the two-layer adapter, with the genuinely renamed runtime gate.

For the wrapped/bare pair the post-run world is exactly
`extend-paired (extend-privateI W ℕ) X ℕ`: `X` is private and `Y` matches
`Z`. The future proof preserves every old match and every old precise-only
capability. For the bare/bare pair, one paired natural allocation suffices.
The previously checked all-futures adapter theorems then discharge the result
relation. No universal compatibility premise, postulate, or recursive call to
the membership theorem is used.

The existing `NaturalUniversalValues`, `Observed`, and `World` definitions
are unchanged: these are inhabitants of the prior interface, not a weakened
replacement interface tailored to the examples.

This closes the gap between concrete producer calls and **membership in the
Nat-only universal interface**. It does not establish arbitrary instantiation
types, arbitrary producer bodies, or R16's recursive size-growth case.

`IntegratedUniversalExperiments` ties both membership theorems directly to
the original `DynamicWrapperExamples.payload-function` and `payload-reveal`.
It exercises the universal record's instantiation field after unequal scope
growth, and checks that both an old match and an old precise-only capability
survive the wrapped allocation prefix. Finally, the actual emitted packets
are decoded successfully: the source query unseals `Y↦X↦ℕ`, while the target
query unseals `Z↦ℕ`, returning the same arbitrary natural input. That last
check is concrete operational evidence, not a general alias-query theorem.

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
| `IntegratedUniversal` | Actual `naturalUniversal` membership for the bare producer pair and the identity-reveal wrapper/bare pair, at every world and index, using uniform allocation prefixes. | Universal compatibility for arbitrary type arguments or bodies. |
| `IntegratedUniversalExperiments` | Membership for the original shared-suite terms, instantiation after unequal futures, preservation of old capabilities, and successful emitted-packet decoding for every natural input. | General alias-query compatibility or a new universal clause. |
| `GeneralInstantiationSteps` | Exact, typed producer/wrapper allocation prefixes for every `R : Ty Δ`, including open nominal arguments. | Arbitrary-instantiation semantic membership or general payload compatibility. |
| `GeneralInstantiationExperiments` | Six typed post-prefix executions recovering function, dynamic, and universal payloads and eliminating each to Nat data. | General query compatibility or new whole-program CTI derivations. |
| `ExistentialPayloadCounterexample` | A complete noncanonical natural semantic record, and impossibility of tag/project compatibility from its existential witness. | Refutation of canonical interpretations or abstract-variable relations. |
| `FreshInstantiationObstruction` | A well-typed, executable `F[X]` whose result type has no closed-root preimage. | Refutation of scope-local universal semantics. |
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
   bodies, and the R16 size-growth issue still require a proof. R19 shows
   that arbitrary future-local result types require changing its root-fixed
   endpoints; R18 excludes choosing payload meanings solely by endpoint
   equality. The arbitrary-type operational prefixes do not solve either
   semantic interface obligation.
4. The nine open paired cast gates and the one-sided cast obligations in the
   reference matrix are not discharged wholesale. Data-query compatibility
   closes a narrow boundary premise, not all base/variable-dynamic cases.
5. Generic frame composition only composes boundaries whose premises have
   been proved. Repeated examples do not justify universal cancellation.

The appropriate acceptance criterion is therefore a checked integrated
fragment with specific semantic boundary proofs and preserved regressions,
not a declaration that the full candidate architecture is already sound.

## Assessment and remaining gates

The combined direction has a nonempty working model, semantic packet and
function witnesses, and a reusable composition theorem whose natural-query
premise is actually discharged. It is no longer merely three compatible
informal constraints. The evidence supports continuing with one architecture
containing `A`, `B`, and `C′`; it does not support replacing the live LR yet.

The focused producer gate is now closed: the concrete payload producer and
its identity-universal wrapper inhabit `naturalUniversal` at arbitrary future
scopes. The instantiation/allocation prefixes and their post-run worlds are
proved uniformly, and the returned functions satisfy the all-futures arrow
test. This is stronger than the previous successful concrete calls.

A general `★` payload interpretation, arbitrary instantiation
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
and direct-natural nominal queries (`fb5bbfb7`). No counterexample to the
implemented fragment was found; the broader obligations listed above remain
unvalidated.

The subsequent universal-membership milestones are paired-adapter support
(`56656055`) and the uniform prefix/membership proofs (`27de4f8d`), followed
by the focused regression and documentation checkpoint. Both proof milestones
were checked with Agda MCP and the independent CLI before being pushed.
The follow-up also leaves `IntegratedModel` and `IntegratedWorld` unchanged
from `fb5bbfb7`, in addition to preserving the live definitions listed above.
The final follow-up aggregate passes Agda MCP with no goals or invisible
metavariables, and the complete `make check` passes with the new universal
regressions and both historical regression targets included.

## Generalization gate: arbitrary payload meanings

The next requested extension is general dynamic payloads and arbitrary
instantiations. An unrestricted existential payload meaning fails even
before higher-order payloads are introduced.

`ExistentialPayloadCounterexample.coarseNatural` is a complete inhabitant
of the current `SemanticType` record with endpoints `ℕ, ℕ`. Its relation is
`coarseNatural(W,k,n,m)` for **any** naturals `n,m`. Valuehood, endpoint
typing, downward closure, and closure under all future worlds hold. Thus
`existential-payload-witness` proves, at every index,

`∃ A. impreciseTy A = ℕ ∧ preciseTy A = ℕ ∧ related A W k 0 1`.

Nevertheless, the concrete, well-typed projection computations separate:

Diagram:

    (0 ⟨ℕ!⟩) ⟨ℕ?⟩                (1 ⟨ℕ!⟩) ⟨ℕ?⟩
             │                              │
             │ 1 step                       │ 1 step
             ▼                              ▼
             0                              1

`tag-and-project-separates` proves that these terms cannot satisfy
`Observed natural W 2`. The proof uses the backward-return observation
at precise fuel `1`, uniqueness of the actual imprecise evaluator result
at arbitrary fuel, and inequality of the returned naturals. It does not
assume equal fuel or compare only one sampled imprecise run.

Consequently, `existential-payload-projection-impossible` refutes natural
projection compatibility from the displayed existential premise. Requiring
an actual payload-relatedness proof, rather than merely payload typing,
does **not** repair this shortcut: the counterexample already supplies one.

This is not a counterexample to `natural`, `dataDynamic`, or the qualified
`A+B+C′` direction. The unrestricted record collects semantic invariants;
it does not assert that a relation is the intended interpretation of its
endpoint syntax. A general dynamic clause must use a fixed interpretation
or carry the relevant proved interpretation coherence. Endpoint equality
alone cannot supply it. Arbitrary relations for abstract type variables
are not ruled out; identifying such a relation with the canonical meaning
of an exposed concrete base type is the invalid step.

## Generalization gate: future-fresh instantiation types

`FreshInstantiationObstruction` proves a second, independent obstruction.
Start with empty physical roots, then allocate `X↦ℕ` on the imprecise side.
The concrete producer `F = Λα.λx:α.x⟨α!⟩` can be instantiated at this
fresh name, with the ordinary typing judgment `F[X] : X⇒★`.

However, the current `SemanticType` source endpoint is a type `B` in the
**empty root**. There is no such `B` with `scopeTy S B = X⇒★`, where
`S = allocate root ℕ`. Structural inversion reduces that equation to a
closed root type scoping to `X`, which is impossible. This proves that
merely changing the argument in `NaturalUniversalValues` from `ℕ` to an
arbitrary later type cannot work while its result family keeps root-fixed
`SemanticType` endpoints.

The counterexample includes typing and exact evaluation of `F[X]`, not
just a hypothetical type equation. A fully-applied companion supplies an
`X`-sealed natural, executes the producer, and consumes the dynamic result
in `λd:★.n`; it returns `n` in five steps. That consumer deliberately does
not inspect the packet and is not evidence of general query compatibility.

This does not refute full universal semantics or `A+B+C′`. Anchoring the
result meaning at the current scopes, or changing the endpoint interface
equivalently, can express `X⇒★`. Simply rebasing physical roots is not yet
a solution: old `Matched` and `PreciseOnly` capabilities must survive, and
the current integrated model has no general capability-preserving rebase.

### Requirements for a reviewed semantic extension

The user subsequently approved the
[scope-local semantic interface revision](INTEGRATED-LOCAL-INTERFACE.md).
That note records its implementation and acceptance limits. The following
assessment describes the boundary at the earlier checkpoint, and its
regression requirements continue to apply.

The semantic generalization is stopped at this interface boundary. No
general dynamic relation or arbitrary-instantiation membership is claimed.
The next implementation needs **both** scope-local result meanings and a
fixed, coherent interpretation of payload/argument codes. Small codes are
a possible way to name interpretations without existentially selecting
an arbitrary `Set₁` semantic record; their denotation and recursive
compatibility proofs remain to be built. These are requirements, not a
newly validated full LR design.

The old regression audit imposes the following additional constraints:

| Regression gate | Requirement on that extension |
|---|---|
| R1–R5, R9, R13; E1–E5, E8, E13–E23 | Retain independent physical histories and private names in closures; quantify over later-created arguments. Moving the meaning's anchor must not lower syntax or freeze witnesses. |
| R6, R7, R10 | Keep all three observation clauses and independent fuel. In particular, do not put every nominal payload one index lower: precise-only elimination has no imprecise step to fund that loss. |
| R8; E6–E8, N1/N2 | Preserve old capabilities and argument variance when introducing a fresh argument meaning. Do not derive nominal matches from equal representations. |
| R11; occupied-erasure control | Keep `Matched` and `PreciseOnly` disjoint, including for function, universal, and dynamic-in-dynamic payloads. |
| R12, R14; E9–E12 | Carry the actual pending computation and target-body relation; neither endpoint syntax nor replacement can reconstruct them. |
| R15, R17; E24 | Retain actual ground/consistency checks, expanded casts, bottom blame, and the order of boundaries. Canonical meanings do not justify boundary cancellation. |
| R16 | Supply a checked well-founded construction. Arbitrary substitution can enlarge a universal body; canonical syntax codes alone do not solve recursive cast continuation. |
| R18 | Concrete endpoint equality must not identify an arbitrary payload relation with the canonical interpretation. |
| R19 | Future-local argument/result types must be expressible without a nonexistent closed-root preimage. |

The active counterexample search has already rejected the two simplest
extensions (R18/R19). The proposed requirements do not discard or weaken
any existing regression, but this audit is **not** a proof that a future
canonical, scope-local implementation will pass them. Higher-order,
universal, dynamic-in-dynamic, expanded-cast, and higher-order precise-only
payloads remain required adversarial tests of that implementation.

## Positive operational result at arbitrary instantiation types

Independently of the blocked semantic interface,
`GeneralInstantiationSteps` proves the producer allocation prefixes for
**every** store `Σ`, type `R : Ty Δ`, and admissible injection gate. This
includes dynamic, function, universal, and already-allocated nominal
argument types; it is not a finite list of Nat-specialized runs.

With named variables, `F = Λα.λx:α.x⟨α!⟩` and
`r = ∀↑ id↑ (α⇒★)`, the returned values are:

| Input | Exact history | Returned value, in its actual final scope |
|---|---|---|
| `F[R]` | Allocate `Z↦R`; 1 step | `(λx:Z.x⟨Z!⟩) ↑ (seal Z R ↦↑ id↑ ★)` |
| `(F ↑ r)[R]` | Allocate `X↦R`, then `Y↦X`, then keep; 3 steps | `((λx:Y.x⟨Y!⟩) ↑ (seal Y X ↦↑ id↑ ★)) ↑ (seal X R ↦↑ id↑ ★)` |

The Agda equations retain the actual renamed gate and explicitly expose
the final terms, histories, traces, and value witnesses. The wrapper's
canonical-form equality normalizes the representation weakening; its
typing theorem requires no evaluation premise. The result types are
`⇑ᵗ R ⇒ ★` and `⇑ᵗ (⇑ᵗ R) ⇒ ★` respectively.

These uniform operational lemmas are usable by a revised semantic model.
They do not establish that arbitrary input payloads are related, install
new semantic world capabilities, prove general projection compatibility,
or inhabit an arbitrary-instantiation universal relation. Those claims
still require the scoped, coherent interpretation discussed above.

### Concrete non-Nat payload recovery

`GeneralInstantiationExperiments` starts from the **actual adapter values
and stores returned by those prefixes**. Each test applies the adapter to
a payload, projects the emitted nominal tag, and unseals the payload.
The bare decoder traverses `Z↦R`; the wrapped decoder traverses
`Y↦X↦R`. It then eliminates the recovered value to first-order data:

| Instantiation type `R` | Payload | Elimination after recovery | Bare / wrapped steps |
|---|---|---|---|
| `ℕ⇒ℕ` | `λx:ℕ.x` | Apply to `n` | `6 / 9` |
| `★` | `n⟨ℕ!⟩` | Project with `ℕ?` | `6 / 9` |
| `∀α.α⇒α` | `Λα.λx:α.x` | Instantiate at `ℕ`, then apply to `n` | `9 / 12` |

All six computations return the same arbitrary `n`, with typing and exact
evaluator witnesses. The counts exclude the already-proved initial
producer-instantiation prefixes. Function and dynamic tests contain only
keep steps. Universal recovery has five/eight keeps, one fresh `ℕ`
allocation, then three keeps; its final store is larger than the decoder's
initial store. No comparison of equal fuel or silently joined stores is
used.

These payloads are outside the current `NaturalPayload` fragment: the
dynamic case contains a dynamic packet inside a nominal seal, and the
other two contain genuine higher-order values. The tests establish that
the relevant operational paths work. They are neither inhabitants of a
generalized `dataDynamic` nor proofs that arbitrary payload relations
survive those paths.

### Verification of the generalization checkpoint

The four new proof modules are included in `LR-narrow/LRNarrowAll.agda`.
Agda MCP checks the aggregate with no goals, invisible metavariables, or
errors, and independent `make check` passes all five targets, including
both historical cast/projection regressions. No new postulates, holes,
termination escapes, or positivity escapes were introduced. The live
calculus/LR and `IntegratedModel`/`IntegratedWorld` are unchanged from
`fab31006`.

Successful checkpoints were committed and pushed separately: the payload
meaning counterexample (`28f29a08`), the fresh-endpoint obstruction
(`195c0869`), arbitrary-type producer prefixes (`91a894ff`), and the final
non-Nat recovery suite/documentation checkpoint. The semantic extension
remains paused for review of the interface requirements, not declared
complete on the strength of these operational tests.
