# Alias-free scope-transport experiment

## Checkpoint and objective

This experiment starts from `7df863bb` on
`codex/gtsf-alias-free-experiment`. The earlier alias experiment remains
available on `codex/gtsf-alias-imprecision`; its later findings are evidence,
not an implementation plan to replay here.

Keep `VarImp` at `X⊑X` and `X⊑★`. Do not change the reduction rules or the
live cast-term-imprecision relation. Test whether seal-aware scope transport
can discharge a one-sided universal wrapper case without alias-transparent
type imprecision. The initial success criterion is a complete universal
wrapper proof; a typed, checked counterexample to the proposed observation
interface is also a decisive preflight result, not a completed fundamental
theorem.

## First test

Use an existing paired name `X` with representation `ℕ`, and instantiate
`Λα. 7 : ∀α. ℕ` at `X`. Compare this application with the same application
under an absent-slot universal reveal. Both must return `7`.

The bare application allocates `Y ↦ X`. The wrapped application also
allocates `Z ↦ Y`. The crucial question is whether the existing return
observation can accommodate the surplus precise allocation after pairing
the first two endpoint allocations. Choosing `X`, rather than `ℕ`, as the
instantiation also tests that the initial allocation cannot simply be
classified as dynamic.

The scope-transport alternative must preserve seals that escape in values
or subsequent computation. Equality of returned naturals alone does not
justify deleting arbitrary store entries, identifying fresh names, or
changing observable casts.

## Working policy

- Use `agda-mcp` for proof development and check the interpreter aggregate.
- Commit and push each checked milestone to
  `peterthiemann/codex/gtsf-alias-free-experiment`.
- Keep the four existing `RevealObligations` explicit until actually proved.
- Do not introduce new assumed compatibility fields, postulates, or
  termination escapes to make the experiment typecheck.

## Status

The branch has been created at the requested checkpoint. The baseline
`LR-narrow/LRNarrowAll.agda` passes `agda-mcp` with no errors, goals, or
invisible metavariables. The first load exceeded the default two-minute
timeout; retrying with a longer command timeout completed successfully.

## Result: the old return observation rejects an inert wrapper

`proof/LR-narrow/ScopeExperiment.agda` contains the checked preflight.
Let `U = Λα. 7` and let `c` be the slot-generated reveal at the existing
paired name `X`, acting on `∀α. ℕ`. The slot does not occur in that type,
but the conversion is still a universal wrapper, not an atomic identity.

`bare-↠` and `wrapped-↠` check the following complete computations:

Diagram:

    U[ X′ ]                         (U ↑ c)[ X ]
       │                               │
       │                               │
       ▼                               ▼
       7                               7

The bare trace takes two steps and allocates one name. The wrapped trace
takes five steps and allocates two names. The three final precise store
entries, in allocation order, are `X ↦ ℕ`, `Y ↦ X`, and `Z ↦ Y`;
the imprecise store has only `X′ ↦ ℕ` and `Y′ ↦ X′`.

`name-chain-paired`: if a future of the initial paired world has a precise
store consisting of the root followed by bindings to the preceding name,
then every precise name has mode `X⊑X` and the precise context is no larger
than the imprecise context. The proof is induction on the future. A
precise-only step would require its already-paired representative to be
below `★`, which is impossible.

`no-raw-join` applies this invariant to the exact final stores: a future
with precise context size `3` and imprecise context size `2` cannot exist.
This excludes every allocation schedule, not just a chosen first pairing.

`not-related`: for every result relation `R`,
`ComputationsRelated initial R 6 bare wrapped` implies `⊥`. Its backward
return field observes the wrapped return at fuel `5`; the bare evaluator
can only return the recorded bare result. `PairedReturns` would then supply
the impossible raw-store future.

The premise of the intended wrapper lemma is not missing:
`literal-universal-related` proves that `U` is related to itself at every
index and in every semantic world, using the existing body-introduction
theorem with a proved constant body. `wrapped-universal-not-related` and
`inert-universal-reveal-not-closed` refute the corresponding closure
conclusion at index `6`. No reveal or cast obligation is assumed.

This is a counterexample to the logical-relation interface, not to the
dynamic gradual guarantee. Both programs are typed and return `7`.

## The scope boundary and the next design decision

`scope-closed-returns` proves the positive boundary fact at every index:
the precise returned value is the weakening of a value in the paired
scope, its extra store entry is exactly `Z ↦ Y`, and lowering the result
to that scope makes it related to the bare result. The witness uses no
alias mode. No operational store is actually deleted.

The general alias-free proof therefore needs an observation interface that
distinguishes physical allocation history from the visible semantic scope.
Adding a body lemma, strengthening the fundamental motive, or weakening
`PostBindValueRelation` to `FutureValueRelation` cannot repair the current
interface: `not-related` quantifies over *every* result relation.

The next experiment should state a scope-aware replacement for the raw-store
join in `PairedReturns`, first for a provably unused precise allocation.
Before integrating it, prove compatibility with subsequent evaluation and
test a function result carrying a seal. The present constant result does
not establish that escaping seals may be erased, nor does it discharge any
of the four general `RevealObligations`.

## Verification

- `agda-mcp` checks the experiment through `LR-narrow/LRNarrowAll.agda`:
  no errors, interaction goals, or invisible metavariables.
- `make -C GTSFImp-Interpreter check` passes, including the interpreter,
  narrowing/widening isomorphism, and logical-relation aggregate.
- No new postulates, holes, or termination pragmas were added. The existing
  LR's termination pragmas and localized function-extensionality assumption
  are unchanged.
- `Imprecision.agda`, the reduction rules, and the live cast-term-imprecision
  relation are unchanged from `7df863bb`.
