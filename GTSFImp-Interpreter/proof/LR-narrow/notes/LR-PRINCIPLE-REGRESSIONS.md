# LR principles from imprecision examples

Date: 2026-08-30. Branch: `codex/gtsf-alias-free-experiment`.

This is an evidence and review document, not an implemented LR redesign.
The calculus, CTI, and live LR are unchanged. The old endpoint
`RevealObligations` is already refuted; the objective is to find a replacement
interface without losing the earlier counterexamples.

## Reading the evidence

`P ⊑ I` below puts the precise program first, as CTI does. The scoped
`ObservedComputations` API takes the imprecise program first. All executable
examples have typing and evaluator evidence. A negative control is deliberately
**not** claimed to be a CTI pair. Equal observed results alone do not establish
imprecision or contextual equivalence.

The regression inventory combines the current branch's
[experiment log](ALIAS-FREE-EXPERIMENT.md),
[fundamental plan](../../../FUNDAMENTAL-PROPERTY-PLAN.md),
[insertion note](../../../INSERTION-MOTIVE-DESIGN.md), and
[replacement design](../../../REPLACEMENT-CLOSURE-DESIGN.md).
Historical J-findings refer to `REPLACEMENT-CLOSURE-DESIGN.md` on
`codex/gtsf-alias-imprecision`, commit `98eb26252c34353b0b224d921dc978409fd4f6c5`.
They are not silently imported as facts about an alias constructor on this
branch: this branch has no such constructor.

## New checked examples

Write `U = Λα.λx:α.x`, `Kₙ = Λα.n`, and
`H = Λα.λf:(α⇒α).f`. Let `r` and `c` be the identity universal reveal and
conceal at the displayed type. These wrappers still allocate when instantiated.

[WrapperImprecisionExamples](../WrapperImprecisionExamples.agda) proves the
following **whole-program CTI derivations**, not merely operand relations.
The examples are families over every natural `n`.

| ID | Precise program | Imprecise program | Checked observation |
|---|---|---|---|
| E1 | `Kₙ[ℕ]` | `(Kₙ ↑ r)[ℕ]` | Both return `n`; 2 versus 5 steps, 1 versus 2 allocations. |
| E2 | `U[ℕ] n` | `(U ↑ r)[ℕ] n` | Both return `n`; 4 versus 8 steps. At fuel 4 the imprecise program is timed out. |
| E3 | `U[ℕ] n` | `((U ↑ r) ↓ c)[ℕ] n` | Both return `n`; the mixed wrapper run is checked with fuel 16. |
| E4 | `U[ℕ] n` | `(((U ↑ r) ↓ c) ↑ r)[ℕ] n` | Both return `n`; repeated mixed wrappers are checked with fuel 20. |
| E5 | `H[ℕ] (λx:ℕ.x) n` | `(H ↑ r)[ℕ] (λx:ℕ.x) n` | Both return `n`; higher-order argument and result conversions are exercised. |

Fuel bounds in E3–E5 are sufficient bounds, not asserted minimal costs.
These five CTI derivations add wrappers to the **imprecise** side. The previous
scoped wrapper theorems primarily test precise-only wrappers. Both directions
must be covered by a future LR.

[NominalObservationExamples](../NominalObservationExamples.agda) gives the
following negative controls in the store `X↦ℕ, Y↦ℕ`, with `X ≠ Y`.
Write `pack Z n = (n ↓ seal Z ℕ) ⟨ Z! ⟩` and
`inspect Z W n = pack Z n ⟨ W? ⟩ ↑ unseal W ℕ`.

| ID | Experiment | Checked result |
|---|---|---|
| E6 | `inspect Z Z n` | Returns `n` in 2 steps, for either name. |
| E7 | `inspect X Y n` | Blames in 2 steps although `resolveVar X = resolveVar Y = ℕ`. |
| E8 | Replace `pack Z n` by `(λx:ℕ.pack Z n) 0` in E6/E7 | Matching returns `n`; mismatching blames, both in 3 steps. The function type `ℕ⇒★` contains neither name. |
| E9 | `(n ↓ seal Y ℕ) ↑ unseal Y ℕ` | Returns `n` in 1 step, but `Value` of this term is impossible. |

`representation-only-projection-impossible` and
`representation-only-call-impossible` refute the exact proposed shortcut
“equal resolved representations suffice for a successful nominal query.”
E8 tests latent behavior, not merely outer function shapes. E9 is a runtime
computation test, not a newly proved LR observation.

[ReplacementImprecisionExamples](../ReplacementImprecisionExamples.agda)
mechanizes three historical type-level obstructions on the current calculus:

| ID | Experiment | Checked result |
|---|---|---|
| E10 | Paired `X`; replace `X` by `ℕ` in `∀α.X` | The replacement `∀α.ℕ ⊑ ★` holds, but `∀α.X ⊑ ★` is impossible. Generic un-replacement is refuted. |
| E11 | Compare `ℕ` with a fresh nominal `Y` | `μ ⊢ ℕ ⊑ Y` is impossible for every `μ`. |
| E12 | Compare distinct old `X` and fresh `Y` | `μ ⊢ X ⊑ Y` is impossible, whereas `μ ⊢ X ⊑ replace Y X Y` holds. |

E10–E12 are failures of proposed proof premises, not failures of runtime DGG.

The active counterexample search then moved beyond the scoped natural/arrow
body fragment. [DynamicWrapperExamples](../DynamicWrapperExamples.agda) gives
three more whole-program CTI pairs, again for every `n`:

| ID | Precise program | Imprecise program | Checked result |
|---|---|---|---|
| E13 | `(F[ℕ] n) ⟨ ℕ? ⟩`, where `F = Λα.λx:α.x ⟨ α! ⟩` | `((F ↑ r)[ℕ] n) ⟨ ℕ? ⟩` | Both blame: the payload is tagged with the private nominal name, not with `ℕ`. Bounds 8 and 16. |
| E14 | `Q[ℕ] n`, where `Q = Λα.λx:α.(x ⟨ α! ⟩) ⟨ α? ⟩` | `(Q ↑ r)[ℕ] n` | Both return `n`: the internally matching fresh tag survives the wrapper. Bounds 8 and 16. |
| E15 | `(F[ℕ] n) ⟨ ℕ? ⟩` | `((λx:★.x) (n ⟨ ℕ! ⟩)) ⟨ ℕ? ⟩` | Precise blames; imprecise returns `n`. Both typing and CTI are checked. Bounds 8 and 4. |

E13 attempts to expose a wrapper's private allocation through a dynamic
projection. E14 tests the opposite outcome with an internal matching
projection, so the suite does not merely accept “both sides blame.” Neither
found an operational counterexample. They do not yet give semantic closure
for arbitrary consumers, mixed wrappers, or nested universal casts.
The three complete data-observing pairs E13–E15 also instantiate the existing
scoped `ObservedComputations natural` relation at every index. This checks the
three computation clauses for these programs, not a general LR at `★`.

E15 is the most discriminating new positive example. The universal's binder
is erased by the actual one-sided universal CTI rule; the precise variable's
injection is removed in the body derivation, and the imprecise argument is
injected at `ℕ`. Hence the two programs really are imprecise-related, although
their tags and final outcomes differ. This is the **allowed** direction of
blame, not a counterexample to DGG. It actively refutes an unconditional
tag-bijection or equal-outcomes design, independently of historical LR clauses.

## Earlier regression inventory

This inventory retains resolved problems and withdrawn claims, with their
status, so a new design cannot accidentally resurrect them.

| ID | Earlier example or obstruction | Evidence and requirement |
|---|---|---|
| R1 | `Λα.7`, bare versus universal reveal, returns `7` with unequal name chains | [ScopeExperiment](../ScopeExperiment.agda), `no-raw-join`, `not-related`, `inert-universal-reveal-not-closed`. A raw returned-world join is impossible. [RevealObligationsCounterexample](../RevealObligationsCounterexample.agda) lifts this to the actual live obligation package. |
| R2 | `Λα.λx:α.x`, whose returned wrapper retains surplus private seals | [EscapingSealExperiment](../EscapingSealExperiment.agda), `wrapped-function-not-lowered`, `wrapped-function-not-in-paired-scope`. Absence from the result type does not justify syntax lowering. The latter theorem concerns the selected paired scope and its lookup-preserving embeddings. |
| R3 | Hiding an unused name, then allocating a later visible name | [ScopedReturnsExperiment](../ScopedReturnsExperiment.agda), `continue-scope`; [VisibleEnvironmentExperiment](../VisibleEnvironmentExperiment.agda). Preserve the old embedding and allow a private hole below a later visible allocation. These are not unrestricted evaluator-equivariance theorems. |
| R4 | Non-identity allocating function returns a closure capturing `n` | [FunctionSealClosureExperiment](../FunctionSealClosureExperiment.agda), `observe-bare`, `observe-private`; [ScopedFunctionSealExperiment](../ScopedFunctionSealExperiment.agda). After application to any natural, the result is captured `n`, not the argument. Identity-only certificates are insufficient. |
| R5 | Returned function with private seals is used after another instantiation and later allocations | [PrivateSealInstantiationExperiment](../PrivateSealInstantiationExperiment.agda). Behavior and typing must hold in later physical stores, not just at the original return. |
| R6 | Backward observation with arbitrary surplus evaluator fuel | [FunctionSealObservationExperiment](../FunctionSealObservationExperiment.agda). Recover the actual body's trace and final physical scope; do not equate unrelated trace proofs or demand equal fuel. |
| R7 | A right-only seal/unseal, including blame and a freshly returned closure | [ScopedRightSealExperiment](../ScopedRightSealExperiment.agda), [ScopedRightSealClosureExperiment](../ScopedRightSealClosureExperiment.agda). Preserve all three observation clauses, at the same index. |
| R8 | Fresh `α` mixed with old visible `X`, body `(α⇒X)⇒(α⇒X)` | [ScopedRightBodyCompatibilityExperiment](../ScopedRightBodyCompatibilityExperiment.agda), [ScopedVisibleUniversalWrapperExperiment](../ScopedVisibleUniversalWrapperExperiment.agda). Preserve old names, contravariance, and the distinction between fresh argument and old nominal types. Includes 3-step versus 18-step data observations. |
| R9 | A future-created argument is sealed at an older atom | Insertion note, “Atom lifting.” An atom relating only literal weakenings of old values rejects new arguments. Use a relation over arbitrary later arguments, not a frozen set of old values. |
| R10 | Index-zero content and same-index dynamic unseal | Fundamental plan, Findings A/D. Strict `n < k` observations avoid the old zero-index demand. A precise-only unseal has no imprecise step to pay for losing payload content. Higher-order payloads require same-index evidence. Base tests alone cannot detect this loss. |
| R11 | Paired occupied center marked `X⊑★`, representation `★`, with a bare natural-tagged target | [ProjectionMismatchStarRepScratch](../../../../GTSFImp/proof/DGG/notes/ProjectionMismatchStarRepScratch.agda), `projection-mismatch-empty`. This bad CTI route is now excluded by target nonoccupancy. Decayed mode alone does not permit discarding a paired target tag. |
| R12 | Replacement conceals an old paired name from the body relation | Replacement design, Finding G. Newly mechanized as E10. Conceal must carry its target-body relation; replacement cannot be inverted. |
| R13 | A wrapper introduces a non-`★` one-sided allocation | Replacement design, Finding F. The old world model cannot state the required family entry. Independent physical histories must be genuine, not a disguise for the same unavailable world constructor. R1 proves the stronger live-interface failure. |
| R14 | First imprecise-only peel and pending target body | Historical J.8/J.13. The requested `ℕ ⊑ Y′` or `X ⊑ Y′` premise is unavailable; after replacement it can hold. E11/E12 recheck these type-level facts. E9 rechecks the “pending is not a value” subcase. General scoped body closing is still unproved. |
| R15 | General alias representative `T = ∀α.α⇒α` has multiple precision target shapes | Historical J.1–J.4. `X ⊑ ★⇒★` and `X ⊑ T` are possible in that alias calculus. The alleged runtime projection counterexample was **withdrawn**: ground readings plus consistency avoidance exclude it. Never replace actual ground/tag agreement by arbitrary target-shape uniqueness. |
| R16 | Same-index recursive cast continuation; replacement can enlarge the next universal body | Fundamental plan, Findings B/E. The old circular cast proofs were removed; their obligations remain explicit. Neither a termination escape nor recurrence on the replaced type's size is a proof. |
| R17 | Function consistency mistaken for precision; bottom and expanded projections | [GroundCastTargetExamples](../../../../GTSFImp/proof/DGG/GroundCastTargetExamples.agda) refutes dropping the `A ⊑ ★` premise. Live cast proofs distinguish expanded inner ground checks and precise bottom-introduction blame. A new cast argument must retain those branches. |

## Candidate shortcuts rejected before proposing a design

| Candidate | Counterexample/regression | Decision |
|---|---|---|
| Join every returned physical store in the old `PairedReturns` world | R1, R13 | Reject. The old obligations are inconsistent. |
| Hide a name whenever the result type omits it | R2, E8 | Reject. The name can survive in a closure or dynamic payload. |
| Match nominal tags by equality of resolved representations | E6/E7, E8; also R11 | Reject. This changes which projections blame. |
| Require a bijection between **every** pair of dynamic tags, or equal final outcomes | E15, R7, R11 and the live `DynamicAtomTagRelated` clause | Reject. Legitimate precise-only nominal information may be erased under the nonoccupancy condition. Matched and precise-only cases must remain distinct. |
| Use only matching successful-return samples | R4, R6, R7, E8 | Reject. Higher-order behavior, backward return, and forward blame are separate obligations. |
| Require the matching run at the same fuel | E2 | Reject. Bare returns at 4; wrapped times out at 4 and returns at 8. |
| Store every nominal payload one index lower | R10, including R7's higher-order variant | Reject for precise-only seals. No imprecise step pays that decrement. |
| Reconstruct conceal's original body derivation from the replaced type | E10 / R12 | Reject by `un-replacement-impossible`. |
| Treat a pending peel as a value or a mere renaming | E9, E11/E12 / R14 | Reject. A reduction and a semantic body-conversion theorem are needed. |

## Reviewable LR direction

The following are **design constraints**, not a claim that a complete new LR
has passed all tests. Most pieces already have local proofs; the new point is
their required combination and the counterexamples excluding simpler versions.

### A. Independent physical scopes, with persistent semantic observations

Keep the actual returned stores and values. Relate them through a semantic
interface rooted at the caller's visible environment, without lowering either
term and without joining every allocation in a syntactic precision world.
New visible arguments may mention names allocated after the original call.

Retain the three clauses of the scoped prototype: if the imprecise program
returns within `n < k`, the precise program eventually returns related data at
`k - n` or blames; if the precise program returns within `n < k`, the imprecise
program eventually returns related data; if the imprecise program blames within
`n < k`, the precise program eventually blames. Matching fuel is existential.
Quantify over independent future allocations before using a function.

This is constrained by R1–R10 and exercised by E1–E5. It makes **no** claim
that arbitrary well-typed values are related, or that private names can be
forgotten from dynamic observations.
E15 specifically requires the precise-blame alternative; replacing the three
directional clauses with equality of outcomes would regress immediately.

### B. Separate matched nominal capabilities from precise-only payloads

For matched names, keep an injective correspondence of runtime nominal tags,
with the semantic relation for their sealed payloads. Extend this correspondence
consistently through later allocations and observations; never choose unrelated
matches after seeing a projection's outcome. Equality of resolved types does
not establish a match. Actual ground readings and cast consistency evidence
remain part of the projection argument.

For a precise-only name, retain the existing distinct semantic-payload case:
the absent target occupant is a premise, not an inference from `X⊑★` alone;
its payload must be available at the index needed by the silent-side unseal.
An occupied paired center whose mode decays still retains its paired tag
obligation. An old unprotected dynamic witness cannot be transported unchanged
through an operation that adds an occupant.

The correspondence here is not a demand to identify *all* physical names.
Physical private seals may remain inside closures, with behavior justified by
typed conversions. If a private tag becomes observable, how its correspondence
is introduced and preserved is an explicit new obligation, not garbage
collection. E6–E8, E13–E15 and R7/R11/R15 block the weaker and stronger
shortcuts. In particular, E15 makes a single global tag-matching rule too
strong, while E7 makes representation-based matching too weak.

### C. Universal producers supply conversion-aware computations

Keep the original body and closing-environment evidence at universal
introduction/cast producers. For each permitted wrapper sequence, the consumer
must receive a related **computation in the actual post-bind scopes**, not an
assertion that two differently substituted bodies are definitionally equal.
Conceal carries its target-body relation. Function conversion uses the
contravariant input conversion before invoking the body, then the covariant
output conversion. Pending intermediate terms may reduce or blame.

Do not turn this into a new postulate with the old theorem's contents. The
producer construction and its well-founded recursion are part of the design's
proof obligation. E3–E5, E9–E12 and R4/R8/R12–R16 support this boundary, but do
not prove a producer theorem for arbitrary nested universals and casts.

## Full-regression check of these constraints

“Compatible” below means that the proposed constraint retains the stated
requirement or rejects the bad shortcut. It is not an Agda proof that a yet
unimplemented combined LR satisfies the fundamental property.

| Regressions | A: physical observations | B: nominal split | C: producer computations |
|---|---|---|---|
| R1, R13 | No raw join; compatible. | Does not require every allocation to be matched. | Must produce actual post-bind observations; no old-world endpoint. |
| R2–R5, R9 | Retains physical closures and later arguments. | No type-support-only erasure. | Requires non-identity, higher-order body evidence. |
| R6, R7, R10 | Three directions, independent fuel, strict bound. | Precise-only payload stays at the needed index. | Pending reductions carry actual costs; same-index steps need a justified construction. |
| R8 | Old visible environment is retained. | Fresh names cannot overwrite old matches. | Explicit input/output variance and fresh-body meaning. |
| R11 | Does not itself solve projection; B is required. | Occupied and unoccupied cases remain distinct. | Cannot admit a forbidden CTI seal-partner route. |
| R12 | No inference from physical scope alone. | No inference from equal representations. | Explicit target relation; does not use un-replacement. |
| R14 | Physical rebase alone is insufficient. | Fresh and old names remain distinct. | Allows pending computations, but general body closing remains open. |
| R15 | Does not restore alias syntax. | Grounds, not arbitrary target shapes, control tags. | No target-shape uniqueness premise. |
| R16 | No circular same-run continuation. | No hidden index loss. | Producer proof must be checked without termination escapes. |
| R17 | Blame remains an observation. | Preserve the ground/consistency guard. | Expanded and bottom cast cases must be proved explicitly. |
| E13–E15 | Preserves both matching outcomes and allowed precise-only blame. | Tests fresh nominal tags and the erased-binder alternative separately. | Exercises a dynamic body, but not a general cast-producer theorem. |

## Cast gates that have not passed

The current `CastValueObligations` still has both one-sided cast obligations
and the following nine `OpenPairedCastCase` constructors. None is discharged
merely by these examples or the existing scoped wrapper results.

| Constructor | Required adversarial test/proof in the proposed LR |
|---|---|
| `open-function-injection` | Function ground injection followed by application to related arguments and result projection. |
| `open-function-precise-injection` | Precise injection, expanded target projection, and all blame directions. |
| `open-function-precise-generalization` | A real `gen` producer crossing binders; this case cannot be dismissed as impossible. |
| `open-universals` | Paired universal casts with staggered/pending computations and nested bodies. |
| `open-function-dynamic` | Dynamic function payloads whose latent results allocate or blame. |
| `open-base-dynamic` | Ground tag tests, expanded projections, and bottom introduction. |
| `open-variable-dynamic` | Both occupied paired tags and nonoccupied precise-only payloads; E6–E8 are negative controls. |
| `open-right-universal` | Same-index one-sided universal instantiation, beyond identity/body-fragment families. |
| `open-universal-dynamic` | Universal dynamic payloads combining tag checks, wrapper allocation, and body substitution. E13–E15 exercise part of this boundary operationally, not the general cast obligation. |

Consequently a wholesale LR replacement is **not** recommended yet. The next
discriminating prototype should cross the missing boundary: universal wrappers
whose bodies export and consume dynamic nominal payloads, with the occupied and
precise-only cases proved separately in the value relation, using E13–E15 as
concrete acceptance tests. Their endpoint computation observations do not
supply that value-level closure. Any proposal that treats passing the
natural/arrow fragment as passing these cast gates must be rejected.

## Verification and keeping the regressions live

The new proof modules are imported by `LR-narrow/LRNarrowAll.agda`.
`make -C GTSFImp-Interpreter check` also runs the new
`check-lr-regressions` target for the historical ground-cast and occupied-slot
projection examples.

This audit found that `ProjectionMismatchStarRepScratch` still used removed
source-conceal APIs. Its proof was ported to the current two constructors;
the negative theorem and runtime witnesses are unchanged. No CTI rule was
edited. This was a stale regression test, not a newly discovered CTI failure.

The interpreter aggregate is checked with `agda-mcp` and independently with
the Agda CLI. The latter also checks the historical scratch module with its
extra notes include path; standalone MCP loading of that old scratch module
cannot resolve `Types` under its inferred include configuration. No new holes,
postulates, or termination escapes
are introduced. `Imprecision`, `Reduction`, `CastTermImprecision`, and the live
`LogicalRelation`/`Computation` definitions remain unchanged from `fb74f3c6`.
