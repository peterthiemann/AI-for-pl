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

## Acceptance boundaries

The code layer must not accept an arbitrary `Meaning` or `SemanticType`
as payload evidence. Its interpretation must be a fixed function of
small codes, with explicit store-entry evidence for nominal boundaries.
Semantic membership and primitive compatibility must then be proved;
neither a record field nor a finite collection of successful runs counts
as such a proof. General recursive dynamic/universal interpretation and
R16's cast-continuation argument remain separate work unless explicitly
discharged below.
