# LR principles from imprecision examples

Date: 2026-08-31. Branch: `codex/gtsf-alias-free-experiment`.

This is an evidence and review document, not a replacement of the live LR.
The subsequent [integrated model experiment](INTEGRATED-MODEL-EXPERIMENT.md)
implements a shared `A+B+C′` data fragment and distinguishes its semantic
boundary proofs from the whole-program regression results below.
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
`H = Λα.λf:(α⇒α).f`. Here are the actual conversion terms, with named
binders rather than de Bruijn indices:

- `r_K = ∀↑ (id↑ ℕ) : Conv↑ (∀α.ℕ) (∀α.ℕ)`.
- `r_U = ∀↑ (id↑ (α⇒α)) : Conv↑ (∀α.α⇒α) (∀α.α⇒α)`.
- `c_U = ∀↓ (id↓ (α⇒α)) : Conv↓ (∀α.α⇒α) (∀α.α⇒α)`.
- `r_H = ∀↑ (id↑ ((α⇒α)⇒(α⇒α)))`, with both endpoints
  `∀α.(α⇒α)⇒(α⇒α)`.

These are structural universal wrappers, **not** the plain whole-type
conversions `id↑ (∀α.A)` and `id↓ (∀α.A)`. They allocate when instantiated.

[WrapperImprecisionExamples](../WrapperImprecisionExamples.agda) proves the
following **whole-program CTI derivations**, not merely operand relations.
The examples are families over every natural `n`.

| ID | Precise program | Imprecise program | Checked observation |
|---|---|---|---|
| E1 | `Kₙ[ℕ]` | `(Kₙ ↑ r_K)[ℕ]` | Both return `n`; 2 versus 5 steps, 1 versus 2 allocations. |
| E2 | `U[ℕ] n` | `(U ↑ r_U)[ℕ] n` | Both return `n`; 4 versus 8 steps. At fuel 4 the imprecise program is timed out. |
| E3 | `U[ℕ] n` | `((U ↑ r_U) ↓ c_U)[ℕ] n` | Both return `n`; the mixed wrapper run is checked with fuel 16. |
| E4 | `U[ℕ] n` | `(((U ↑ r_U) ↓ c_U) ↑ r_U)[ℕ] n` | Both return `n`; repeated mixed wrappers are checked with fuel 20. |
| E5 | `H[ℕ] (λx:ℕ.x) n` | `(H ↑ r_H)[ℕ] (λx:ℕ.x) n` | Both return `n`; higher-order argument and result conversions are exercised. |

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

Here `r_F = ∀↑ (id↑ (α⇒★)) : Conv↑ (∀α.α⇒★) (∀α.α⇒★)`;
the conversion for `Q` is `r_U` above.

| ID | Precise program | Imprecise program | Checked result |
|---|---|---|---|
| E13 | `(F[ℕ] n) ⟨ ℕ? ⟩`, where `F = Λα.λx:α.x ⟨ α! ⟩` | `((F ↑ r_F)[ℕ] n) ⟨ ℕ? ⟩` | Both blame: the payload is tagged with the private nominal name, not with `ℕ`. Bounds 8 and 16. |
| E14 | `Q[ℕ] n`, where `Q = Λα.λx:α.(x ⟨ α! ⟩) ⟨ α? ⟩` | `(Q ↑ r_U)[ℕ] n` | Both return `n`: the internally matching fresh tag survives the wrapper. Bounds 8 and 16. |
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

## Repeated boundaries: nine additional imprecision pairs

The earlier examples did not adequately test repeated **nonidentity**
boundaries. E16–E24 supply three cast, three sealing, and three mixed examples.
Each row has two syntactically different programs, typing for both, an actual
whole-program CTI derivation, and proof-carrying evaluator results. All final
types are `ℕ`. These are program regressions, not a proof of LR compatibility
for every value inhabiting an intermediate type.

### Concrete casts and conversions

Use `f = λx:ℕ.x + 1`, `a = λg:(ℕ⇒ℕ).g 1`, `U = Λα.λx:α.x`,
`T = ℕ⇒ℕ`, and `D = ★⇒★`. Superscripts on operations mean finite
iteration: `C³(M) = C(C(C(M)))`, not a postulated cast-composition equation.

The casts below include their direction; arrow casts reverse the input:

- `ℕ! = id ℕ ! : ℕ ∼ ★`, `ℕ? = ? (id ℕ) : ★ ∼ ℕ`.
  `𝔹!` and `𝔹?` are the corresponding Boolean casts.
- `u = ℕ? ↦ ℕ! : T ∼ D`, `d = ℕ! ↦ ℕ? : D ∼ T`.
- `u₂ = d ↦ ℕ! : (T⇒ℕ) ∼ (D⇒★)`,
  `d₂ = u ↦ ℕ? : (D⇒★) ∼ (T⇒ℕ)`.
- `u∀ = inst (α? ↦ α!) : (∀α.α⇒α) ∼ D`,
  `d∀ = gen (α! ↦ α?) : D ∼ (∀α.α⇒α)`.
  The injection in `u∀` uses the instantiation environment, and its domain
  projection the flipped environment; `d∀` uses the generalization environment
  and its flip. These are the actual casts in
  [ExampleTerms](../../../../GTSFImp/proof/DGG/ExampleTerms.agda), not a
  universal ground tag or an identity reveal. Their non-dynamic endpoint side
  condition is witnessed by `D ≠ ★`.

Define `B(M) = M ⟨ℕ!⟩ ⟨ℕ?⟩`, `C(M) = M ⟨u⟩ ⟨d⟩`,
`C₂(M) = M ⟨u₂⟩ ⟨d₂⟩`, and `C∀(M) = M ⟨u∀⟩ ⟨d∀⟩`.

For an actual store entry `X↦A`, the function conversions are

- `c_X,A = unseal X A ↦↓ seal X A : Conv↓ (A⇒A) (X⇒X)`;
- `r_X,A = seal X A ↦↑ unseal X A : Conv↑ (X⇒X) (A⇒A)`;
- `S_X,A(M) = (M ↓ c_X,A) ↑ r_X,A : A⇒A` when `M : A⇒A`.

Write `S = S_X,ℕ` when `X↦ℕ`. Under `∀α`, the same **old** `X`
is retained, distinct from `α`:

- `c_X,ℕ∀ = ∀↓ (unseal X ℕ ↦↓ seal X ℕ)` has type
  `Conv↓ (∀α.T) (∀α.X⇒X)`;
- `r_X,ℕ∀ = ∀↑ (seal X ℕ ↦↑ unseal X ℕ)` has the reverse type;
- `S∀(M) = (M ↓ c_X,ℕ∀) ↑ r_X,ℕ∀`;
- `C_b∀(M) = M ⟨∀ᶜ u⟩ ⟨∀ᶜ d⟩`, crossing
  `∀α.T → ∀α.D → ∀α.T`.

Here `C∀` crosses between a universal and a function using `inst/gen`;
`C_b∀` is a structural universal cast. They are different operations.
Likewise `S∀` genuinely changes `X` in the body; it is not E1–E4's
`∀↑ id↑`/`∀↓ id↓` wrapper.

### Cast matrix

[RepeatedCastExamples](../RepeatedCastExamples.agda) checks:

| ID | Precise program | Imprecise program | Boundary types and observation |
|---|---|---|---|
| E16 / C1 | `f n` | `C³(f) n` | Three `T → D → T` cycles. Both return `n + 1`; sufficient fuel 4 / 40. |
| E17 / C2 | `a f` | `C₂²(a) C³(f)` | Two `(T⇒ℕ) → (D⇒★) → (T⇒ℕ)` cycles; three more on the higher-order argument. Both return `2`; fuel 8 / 100. |
| E18 / C3 | `U[ℕ] n` | `C∀²(U)[ℕ] n` | Two `(∀α.α⇒α) → D → (∀α.α⇒α)` cycles, then instantiate and apply. Both return `n`; fuel 6 / 120. Real `inst/gen` produces fresh physical names. |

The CTI witnesses are `first-order²`, `higher-order²`, and `poly-cycle²`.
The equal results do not license erasing allocation histories or demanding
equal fuel.

### Sealing matrix

In E19 the store is `X↦ℕ, Y↦X, Z↦Y`. Define the complete chain traversal

`L(M) = (((((M ↓ seal X ℕ) ↓ seal Y X) ↓ seal Z Y)
↑ unseal Z Y) ↑ unseal Y X) ↑ unseal X ℕ)`.

Its successive types are `ℕ → X → Y → Z → Y → X → ℕ`.
In E20–E21 the store is `X↦ℕ`. For E21, put
`h = λg:(X⇒X).g : (X⇒X)⇒(X⇒X)` and define

- `r₂ = c_X,ℕ ↦↑ r_X,ℕ`, of type
  `Conv↑ ((X⇒X)⇒(X⇒X)) (T⇒T)`;
- `c₂ = r_X,ℕ ↦↓ c_X,ℕ`, of type
  `Conv↓ (T⇒T) ((X⇒X)⇒(X⇒X))`;
- `J(M) = (M ↑ r₂) ↓ c₂`.

Thus `J` goes from a nominal higher-order type to its representation and back;
`S` goes from a representation function type to its nominal type and back.

[RepeatedSealExamples](../RepeatedSealExamples.agda) checks:

| ID | Precise program | Imprecise program | Boundary types and observation |
|---|---|---|---|
| E19 / S1 | `L³(n + 1)` | `B(L³(n + 1))` | Three traversals of the three-name representation chain; the payload computes. Both return `n + 1`; fuel 20 / 30. |
| E20 / S2 | `S²(f) n` | `B(S²(f) B(n))` | Two `T → (X⇒X) → T` cycles. The imprecise side also checks the argument and result. Both return `n + 1`; fuel 18 / 24. |
| E21 / S3 | `J²(h) (f ↓ c_X,ℕ) (n ↓ seal X ℕ) ↑ unseal X ℕ` | `B(J²(h) (f ↓ c_X,ℕ) (B(n) ↓ seal X ℕ) ↑ unseal X ℕ)` | Two higher-order seal cycles, followed by two applications. Both return `n + 1`; fuel 40 / 50. |

The CTI witnesses are `s1-pair²`, `s2-pair²`, and `s3-pair²`.
The matched seal boundaries are present on both sides; their mere deletion
is **not** claimed admissible. The small additional imprecise-side casts make
these genuinely asymmetric CTI tests, not just reflexivity examples.

### Mixed matrix

For E24 let
`bad = λx:ℕ.x ⟨ℕ!⟩ ⟨𝔹?⟩ ⟨𝔹!⟩ ⟨ℕ?⟩ : T`
and `i = λx:★.x : D`. The precise store is `X↦ℕ`, the imprecise
store `X′↦★`. Both occupy the same center, whose mark is `X⊑★`.
Write `S′ = S_X′,★`. The intermediate nominal function types remain
paired: this is not the forbidden occupied-slot, direct-seal erasure of R11.

[MixedBoundaryExamples](../MixedBoundaryExamples.agda) checks:

| ID | Precise program | Imprecise program | Boundary types and observation |
|---|---|---|---|
| E22 / M1 | `S(S(f)) n` | `C(S(C(S(C(f))))) n` | Two nominal function cycles interleaved with three genuine function-cast cycles. Both return `n + 1`; fuel 32 / 64. |
| E23 / M2 | `S∀(S∀(Λα.f))[ℕ] n` | `C_b∀(S∀(C_b∀(S∀(C_b∀(Λα.f)))))[ℕ] n` | Two genuine old-name universal seal cycles interleaved with three structural universal cast cycles. Instantiation allocates between pending layers. Both return `n + 1`; fuel 64 / 128. |
| E24 / M3 | `S(C(S(C(C(bad))))) n` | `(S′(S′(i)) (n ⟨ℕ!⟩)) ⟨ℕ?⟩` | Two matched function-seal cycles at different representations, three extra precise-side cast cycles, then a latent failing check. Precise **blames**, imprecise returns `n`; fuel 128 / 128. |

The CTI witnesses are `interleaved²`, `allocating²`, and `mixed-latent²`.
E24 is legal directional imprecision, not a DGG counterexample. It ensures
that testing repeated boundaries is not restricted to equal successful returns.
The failing check occurs inside the function body; the example does not start
with a literal `blame` surrounded by wrappers.

All fuel numbers in E16–E24 are sufficient bounds, not minimal step counts.

### Active nominal counterexample attempt after repeated crossings

[RepeatedBoundaryControls](../RepeatedBoundaryControls.agda) adds a matched
success/failure control, deliberately **not** asserted to be a CTI pair.
In `X↦ℕ, Y↦ℕ`, let

`R_Z(M) = (((M ↓ seal Z ℕ) ⟨Z!⟩) ⟨Z?⟩) ↑ unseal Z ℕ`,

`g = λx:ℕ.R_X(R_Y(R_X(x + 1)))`,

`F = Λα.λx:ℕ.((g x) ↓ seal X ℕ) ⟨X!⟩ : ∀α.ℕ⇒★`.

Use `r = ∀↑ (id↑ (ℕ⇒★))` and `c = ∀↓ (id↓ (ℕ⇒★))`,
both with endpoints `∀α.ℕ⇒★`. Define

`O_Q(n) = ((((F ↑ r) ↓ c)[ℕ] n) ⟨Q?⟩) ↑ unseal Q ℕ`.

There are three inner `R` cycles, each containing a seal, a nominal injection
cast, a nominal projection cast, and an unseal. Outside them is **one**
allocating universal reveal/conceal pair. These are scalar nominal casts,
not E22–E24's structural function-cast cycles.

| Control | Observation | What it attacks |
|---|---|---|
| N1, `O_X(n)` | Returns `n + 1`, fuel 64. | Preserving a latent old tag through three `R` cycles and fresh universal allocations must still allow the matching query. |
| N2, `O_Y(n)` | Blames, fuel 64. | Equal representations, repeated successful crossings, and a name-free result type do not permit choosing a new nominal match. |

`query-independent-success-impossible` formally refutes the proposed shortcut
that all final queries would succeed. These controls retain names in the
actual computation and add allocation, delayed application, and repeated
crossings to E6–E8; they do not establish arbitrary-future-world closure.

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
| R18 | Choose an arbitrary semantic payload meaning with endpoints `ℕ, ℕ` | [ExistentialPayloadCounterexample](../ExistentialPayloadCounterexample.agda) constructs a complete `SemanticType` relating `0` to `1`, but proves their tag/project computations unrelated at `Observed natural W 2` in the empty root world. Actual payload relatedness plus endpoint equality does not identify the canonical type interpretation. |

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
| Treat every well-typed boundary stack with equal endpoint types as identity | E24's `ℕ → ★ → 𝔹 → ★ → ℕ` body | Reject. Equal endpoints do not eliminate an intermediate failing check. This does not refute a properly restricted inverse-on-image theorem. |
| After several successful crossings, choose nominal matches by the current representation | N1/N2, strengthening E6–E8 | Reject. The old `X` query succeeds and the equally represented `Y` query fails after allocation and three mixed cycles. |
| Choose any `SemanticType` witnessing the payload pair, constrained only by endpoint types | R18 | Reject. All current semantic invariants can hold for a noncanonical relation that equates different naturals. Projection compatibility needs a fixed interpretation or proved coherence with it. |

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
E18 and E23 add repeated genuine cast/conversion allocation paths. E24 again
requires precise-only blame, this time inside alternating structural boundaries.

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
N1/N2 actively retest this distinction after three seal/tag/project/unseal
cycles inside allocating universal wrappers: neither losing the old match nor
matching by representation is acceptable. E24 keeps both nominal occupants
even though their representations and the center's precision mark differ.

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

### C′. Ordered boundary composition, not cancellation

The repeated tests suggest a more concrete implementation of C: use the
existing frame-composition theorem as the composition spine, and require a
local semantic compatibility proof for each cast/reveal/conceal boundary.
Keep the order, intermediate types, actual scopes, and nominal capabilities;
do not normalize a sequence merely because its first and last types agree.

The already checked paired-frame theorem is precise about this obligation:
if `Mᴵ` and `Mᴾ` are observed at semantic type `A` and index `k`, and
for **every** pair of operand histories `χᴵ, χᴾ`, every `j ≤ k`, and every
pair of `A`-related returned values in the resulting physical scopes, plugging
those values into the transported frames `Fᴵ, Fᴾ` gives computations observed
at `B, j`, then `Fᴵ[Mᴵ]` and `Fᴾ[Mᴾ]` are observed at `B, k`.
This is
[`ScopedFrameComposition.Composition.frame-observed`](../ScopedFrameComposition.agda),
not a new postulate or an inference from the nine sample evaluations.

The proposed extension is to establish its boundary premises for the missing
dynamic and universal-cast cases. Their local proofs must retain B's occupied
versus precise-only distinction. One-sided boundaries need the corresponding
one-sided composition/step-expansion argument; a paired-frame theorem alone
does not pay for a silent-side step. Universal producers still owe C's
post-bind computation evidence, including explicit conceal target-body meaning.

For a finite sequence of **already proved compatible boundaries**, compose
these theorems in the syntax's actual order. Induction on that finite sequence
does **not** prove the recursive universal producer, whose reduction can
introduce new boundaries and enlarge a substituted type. R16 remains open.
This proposal separates the reusable composition theorem from its genuinely
unproved cast/producer premises instead of hiding them in a closure field.

## Full-regression check of these constraints

“Compatible” below means that the proposed constraint retains the stated
requirement or rejects the bad shortcut. It is not an Agda proof that a yet
unimplemented combined LR satisfies the fundamental property.

| Regressions | A: physical observations | B: nominal split | C/C′: producer and boundary computations |
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
| E1–E5 | Independent fuel and physical histories retained. | Private names are not lowered out of closures. | Identity universal wrappers remain computations, not definitional identities. |
| E6–E9 | Delayed failure is observed; pending terms may reduce. | Nominal equality is not representation equality. | No pending-value or successful-query shortcut. |
| E10–E12 | Scope separation does not imply a missing type relation. | Distinct old/fresh names are not identified. | Explicit target-body meaning remains required. |
| E13–E15 | Preserves both matching outcomes and allowed precise-only blame. | Tests fresh nominal tags and the erased-binder alternative separately. | Exercises a dynamic body, but not a general cast-producer theorem. |
| E16–E18 / C1–C3 | Unequal costs and real inst/gen allocations allowed. | No conclusion about arbitrary nominal observations from data-only tests. | Repeated first/higher-order and real inst/gen paths pass operationally; general primitive compatibility remains open. |
| E19–E21 / S1–S3 | Complete applied computations, not just function values. | Direct representation chains and nominal higher-order arguments retained. | Direction reverses at function inputs, twice at higher order; no deletion of matched seals assumed. |
| E22–E23 / M1–M2 | The universal case keeps actual post-bind scopes. | Old `X` is not replaced by a fresh binder. | The cast/seal order is retained through application and universal allocation. |
| E24 / M3 | Allows precise blame with imprecise success. | Occupied decayed center retains paired nominal boundaries. | Intermediate Boolean projection is not erased merely because endpoints agree. |
| N1/N2 | Old captured tags remain observable after fresh allocation. | The original match succeeds; a same-representation substitute fails. | Three successful mixed cycles do not authorize changing the later query. |

### Result of the renewed counterexample search

None of A, B, or the explicitly qualified C is refuted by this regression
suite. They survive **as constraints**, not as a completed definition and
fundamental-property proof. C′ supplies an existing proved composition core
and a sharper proposed interface for the missing primitive cases.

The active attacks were:

1. Force repeated casts contravariantly by passing and calling functions,
   rather than merely observing wrapped values: E17/E21 return the computed
   successor result.
2. Cross genuine inst/gen and old-name universal conversions repeatedly:
   E18/E23 return despite fresh physical allocations and pending wrappers.
3. Hide a failing base check behind repeated cast/seal function boundaries:
   E24 exposes the failure only on the precise side, as permitted by CTI.
4. Export an old nominal tag after three mixed cycles and fresh allocations,
   then try both the original and a same-representation name: N1 succeeds,
   N2 blames. B predicts that distinction, without a garbage-collection rule.
5. Reapply all earlier attacks, including occupied-slot erasure, un-replacement,
   pending-value assumptions, bottom/expanded projections, index loss, and
   the withdrawn alias counterexample: R1–R17 and E1–E15 remain in the matrix.

I found no counterexample to the **qualified A+B+C′ direction**. This is not
evidence that an unspecified full LR has passed. In particular, a dynamic
value relation supporting arbitrary future consumers, all nine paired cast
gates, and a noncircular universal-producer construction are still missing.
The new tests reject stronger cancellation and nominal-forgetting principles;
they do not justify adding either to the LR.

## Cast gates that have not passed

The current `CastValueObligations` still has both one-sided cast obligations
and the following nine `OpenPairedCastCase` constructors. None is discharged
merely by these examples or the existing scoped wrapper results.

| Constructor | Required adversarial test/proof in the proposed LR |
|---|---|
| `open-function-injection` | Function ground injection followed by application to related arguments and result projection. |
| `open-function-precise-injection` | Precise injection, expanded target projection, and all blame directions. |
| `open-function-precise-generalization` | A real `gen` producer crossing binders; this case cannot be dismissed as impossible. E18 now checks two concrete inst/gen roundtrips, not this general semantic case. |
| `open-universals` | Paired universal casts with staggered/pending computations and nested bodies. E23 adds concrete repeated old-name conversions interleaved with universal casts. |
| `open-function-dynamic` | Dynamic function payloads whose latent results allocate or blame. E24 adds a checked latent-blame mixed-boundary pair. |
| `open-base-dynamic` | Ground tag tests, expanded projections, and bottom introduction. |
| `open-variable-dynamic` | Both occupied paired tags and nonoccupied precise-only payloads; E6–E8 and N1/N2 are negative controls, not primitive LR compatibility. |
| `open-right-universal` | Same-index one-sided universal instantiation, beyond identity/body-fragment families. |
| `open-universal-dynamic` | Universal dynamic payloads combining tag checks, wrapper allocation, and body substitution. E13–E15 exercise part of this boundary operationally, not the general cast obligation. |

Consequently a wholesale LR replacement is **not** recommended yet. The
integrated prototype now establishes a data-only instance of B's dynamic
nominal relation and natural projection compatibility, including generic
frame composition; see its report for the exact additional producer tests
and limits. The original prototype objective was to establish B's dynamic
nominal value relation and its
projection/unseal boundary premises for C′, keeping occupied and precise-only
cases separate. E13–E15, E24, and N1/N2 are concrete acceptance tests; E18/E23
then test the allocating producer extension. Their endpoint observations do
not supply that value-level closure. Any proposal that treats passing these
examples as discharging the cast gates must be rejected.

The next focused producer gate has also been mechanized:
`IntegratedUniversal` proves membership of the concrete dynamic-payload
producer and its identity-universal reveal wrapper in the existing
`naturalUniversal` interface, for every world, index, and future scope.
Its uniform allocation prefixes preserve old nominal capabilities and relate
the freshly returned adapters. This is a Nat-instantiation theorem for the
concrete family, not a discharge of `open-universals`,
`open-right-universal`, or `open-universal-dynamic`; arbitrary instantiation
types and bodies remain outside this interface. The experiment report records
the exact statement and the additional future/packet-query regressions.

## Verification and keeping the regressions live

The new proof modules are imported by `LR-narrow/LRNarrowAll.agda`.
`make -C GTSFImp-Interpreter check` also runs the
`check-lr-regressions` target for the historical ground-cast and occupied-slot
projection examples.

The August 30 audit found that `ProjectionMismatchStarRepScratch` used removed
source-conceal APIs. Its proof was ported to the current two constructors;
the negative theorem and runtime witnesses are unchanged. No CTI rule was
edited. This was a stale regression test, not a newly discovered CTI failure.

The interpreter aggregate is checked with `agda-mcp` and independently with
the Agda CLI. The latter also checks the historical scratch module with its
extra notes include path; standalone MCP loading of that old scratch module
cannot resolve `Types` under its inferred include configuration. No new holes,
postulates, or termination escapes
are introduced. For the August 31 repeated-boundary additions, `Imprecision`,
`Reduction`, `CastTermImprecision`, and the live `LogicalRelation`/`Computation`
definitions are verified unchanged from the previous checkpoint `d3d2b7bb`.
