# Alias-free scope-transport experiment

## Checkpoint and objective

This experiment starts from `7df863bb` on
`codex/gtsf-alias-free-experiment`. The completed alias experiment remains
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
The first store/scope test is in progress.
