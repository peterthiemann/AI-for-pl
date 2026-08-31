# Scope-local integrated semantic interface

This is the semantic-interface revision approved after checkpoint
`9618efef`. The live LR and CTI are not changed. The preceding
[assessment](INTEGRATED-MODEL-EXPERIMENT.md#generalization-gate-future-fresh-instantiation-types)
contains the two obstructions R18/R19 and the required regression gates.

## Local endpoints, original worlds

`IntegratedLocal.Local ΣI₀ ΣP₀` uses exactly the original
`IntegratedWorld.Worlds ΣI₀ ΣP₀`. If `S₀,T₀` are physical scopes, then
`Meaning S₀ T₀ A B` has endpoints `A : Ty S₀` and `B : Ty T₀`.
There is no requirement that `A,B` come from the initial roots.

At later scopes `S,T`, its relation is `related A p q W k U V`, where
`p : S₀ ≤ S` and `q : T₀ ≤ T`. Related values are typed at
`liftTy p A` and `liftTy q B`. If `W` evolves along `r,s` to `W′`,
future closure relates `liftTerm r U` and `liftTerm s V` at paths
`p;r` and `q;s`, at the **same** index `k`.

The anchor is not a new world root. Existing matches, precise-only
capabilities, and private physical allocations remain part of `W`.
Re-anchoring therefore must not construct an empty world or lower a term.

`Observed A p q W k M N` keeps the original three observations:

- If `M` returns with fuel `n < k`, then `N` returns at some independent
  fuel with related results at `k∸n`, or `N` blames.
- If `N` returns with fuel `n < k`, then `M` returns at some independent
  fuel with related results at `k∸n`.
- If `M` blames with fuel `n < k`, then `N` blames.

In both return clauses, the future world follows the actual independent
histories `χI,χP`; its paths from the anchors are
`p;advance-future S χI` and `q;advance-future T χP`. The index bound,
blame direction, and actual-result uniqueness argument are unchanged.

The checked kernel supplies canonical natural/boolean meanings, index
downward closure, observations from actual returns or precise blame,
and observations of related values. Semantic records alone remain
unrestricted infrastructure: R18 is addressed by controlling their code
interpretation, not by pretending these invariants determine it.

## Precise-only allocations

The experimental world constructor is now `extend-only W B` for any
representation `B`, replacing the Nat-only constructor. Its fresh name
is precise-only, every old capability persists, and `only-not-matched-at`
still proves disjointness from all occupied matches. The old examples
explicitly pass `ℕ`; there are no compatibility aliases.

This change alone does not extend `dataDynamic`: that relation still
requires its actual natural-payload evidence. Capability allocation and
payload semantics remain separate obligations.

## Fixed code interpretation

`IntegratedLocalCodes.Code S T A B` has the following complete grammar.
The interpretation `denote` is a recursive function, not a caller-supplied
relation.

| Code | Endpoints | Related values at index `k` |
|---|---|---|
| `base-code ι` | `ι,ι` | Equal constants of base type `ι`. |
| `data-code` | `★,★` | The existing `DynamicValues`, including its actual natural-payload evidence. |
| `arrow-code a b` | `AI⇒BI,AP⇒BP` | Typed function values that take every related argument at every future world and `j < k` to `Observed (denote b)` at `j`. |
| `paired-code entryI entryP a` | `X,Y` | Exact seals of payloads related by `denote a` at `k`, and `Matched W X Y`. The entries identify both representations. |
| `precise-code entryP a` | `AI,Y` | An unsealed imprecise payload and its precise seal, related by `denote a` at `k`, and `PreciseOnly W Y`. The entry identifies the precise representation. |

Each interpretation proves valuehood, local endpoint typing, index
downward closure, and future closure. In particular, neither nominal
constructor subtracts an index from its payload. These constructors do
not claim that arbitrary conversion computations preserve membership.

If `a : Code S T ℕ ℕ` and `related (denote a) p q W k U V`, then
`U,V` are the same natural constant. Consequently no code, even one
chosen existentially, relates `0` to `1` at these endpoints. This is
`natural-code-values` and `different-naturals-rejected`; it excludes R18's
arbitrary-record witness. There is no constructor importing a `Meaning`.
Codes with nominal endpoints still require their explicit capability at
the world where membership is asserted; equal store representations do
not create a match.

`reanchor p q A` moves the endpoints to the current scopes while
preserving `A`'s relation over the **same** worlds. Its relation uses path
composition, and membership is equivalent in both directions at the new
anchor. `reanchor-observed` preserves all three observations. This is an
operation on meanings, not permission to inject one into the code grammar.

## Universal interface at future-local codes

`IntegratedLocalUniversal.Family S₀ T₀ CI CP` supplies a result **code**
for every later pair of scopes and argument code `a : Code S T RI RP`:

`result p q a : Code S T ((liftBody p CI)[RI]) ((liftBody q CP)[RP])`.

If `U,V` belong to `universal F` at `p,q,W,k`, then for every future
`r,s,W′`, every `j < k`, and every argument code at those future scopes,
the actual type applications satisfy `Observed (denote (result F (p;r)
(q;s) a)) stay stay W′ j`. Both terms use the displayed, lifted bodies
and actual instantiation types. Thus argument and result types may contain
names allocated after the original roots; they need no root preimage.
The implementation proves downward closure and future closure by composing
the same scope paths and world evolutions.

This interface tests every argument in the displayed grammar, not every
`Ty`. In particular, `data-code` does not add function/universal dynamic
payloads, and there is no universal constructor in `Code` yet.
`universal F` is a meaning built above that grammar. Returning a code
removes arbitrary semantic-record choice, but constructing `F` and proving
membership for a particular polymorphic body remain proof obligations.

## Regression discipline

`IntegratedLocalExperiments` checks the following local claims:

| Test | Checked result |
|---|---|
| R18 existential choice | No `Code S T ℕ ℕ` witnesses relatedness of `0,1`. |
| R19 fresh endpoints | After fresh paired allocations, codes exist for `X⇒★,Y⇒★` and `X⇒X,Y⇒Y`; the latter is inhabited by identities at every index. This is not membership of the dynamic injection producer. |
| Higher-order precise-only payload | `λx:ℕ.x` relates to its precise seal at a slot represented by `ℕ⇒ℕ`, at every index with same-index payload evidence. Unsealing and applying to `7` has typed, data-ending evaluator companions. |
| Occupied erasure | The precise-only function code cannot be inhabited when the target name is occupied by a match. |
| Unequal future histories | Both paired and precise-only memberships survive one imprecise and two precise private allocations. Reanchoring the paired meaning retains the same final world and values. |

`IntegratedLocalUniversalProducer` proves more than selected evaluator runs.
Let `Kₙ = Λα.n : ∀α.ℕ` and `r = ∀↑id↑ℕ`. Both `Kₙ,Kₙ` and
`Kₙ ↑ r,Kₙ` inhabit `universal constant-family` for **every** anchor,
current world, index, future world, and future-local argument code.
The family returns the canonical natural code for every argument.

The proof uses actual instantiations at arbitrary `RI,RP`. The bare pair
returns `n,n` in `2/2` steps after allocating the two representations.
The wrapped imprecise term takes `5` steps, allocating `X↦RI` followed by
`Y↦X`; the precise bare term takes `2` and allocates `Z↦RP`. The returned
world extends the caller's world by the imprecise private `X` and paired
`Y,Z`, preserving all old capabilities. These are proofs of all three
observations at every index, not an equal-fuel comparison. The constant
body deliberately avoids claiming general body-conversion compatibility.

The existing integrated suite and historical counterexamples remain in
`LRNarrowAll`. Their continued typechecking preserves the regression basis;
it is not a migration proof for all their primitive compatibility lemmas.
The local revision additionally needs positive membership and negative
controls, not only endpoint typing or evaluator samples.

The scope/observation kernel retains independent histories, all three
observations, strict `n < k`, and unchanged residual-index accounting
(R1--R7, R9--R10, R13). Nominal membership requires persistent capabilities
and keeps precise-only payloads at the same index (R8, R11). The fixed-code
base separation and future-local endpoints address the specific interface
obstructions R18/R19. Pending computations, replacement-sensitive target
bodies, actual cast checks, and well-founded recursive continuation remain
requirements for later compatibility proofs (R12, R14--R17); this revision
does not discharge them by changing their statements.

## Acceptance boundaries

The code layer must not accept an arbitrary `Meaning` or `SemanticType`
as payload evidence. Its interpretation must be a fixed function of
small codes, with explicit store-entry evidence for nominal boundaries.
Semantic membership and primitive compatibility must then be proved;
neither a record field nor a finite collection of successful runs counts
as such a proof. General recursive dynamic/universal interpretation and
R16's cast-continuation argument remain separate work unless explicitly
discharged below.

## Verification and remaining work

All local modules are included in `LR-narrow/LRNarrowAll.agda`. The complete
aggregate is checked with Agda MCP (no goals, invisible metavariables, or
errors), and independent `make check` includes the interpreter, isomorphism,
LR aggregate, and both historical cast/projection regressions. The new files
introduce no postulates, holes, termination overrides, or positivity escapes.

The live LR, CTI, evaluator, and reduction definitions are unchanged from
`9618efef`. The earlier `IntegratedModel` remains an experimental reference
for existing proofs; it is not a wrapper for the new interface. The shared
experimental world changed only to generalize precise-only allocation;
scope transport laws were added to support local anchors.

The interface revision is complete within the stated finite code grammar.
The next substantive work is a guarded, fixed interpretation for general
dynamic and universal payloads, together with compatibility and membership
for the binder-dependent producer `Λα.λx:α.x⟨α!⟩`. Its former root-endpoint
obstruction is removed, but its arbitrary-code membership is not proved by
the constant-body witness. General body conversions, recursive cast
continuation, and the bridge to CTI/fundamental-property assembly remain.
