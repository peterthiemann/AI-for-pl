# R20: fixed codes do not imply endpoint coherence

The general-dynamic preflight after `4477c47e` found a new obstruction.
Restricting payload witnesses to the existing finite `Code` grammar excludes
R18's arbitrary natural relation, but does not make two codes with the same
endpoints interchangeable. This note records the checked counterexample;
no dynamic definition, world rule, live LR, or CTI rule has been changed.

The proof is [FixedCodeCounterexample](../FixedCodeCounterexample.agda).
[FixedCodeCounterexampleTerms](../FixedCodeCounterexampleTerms.agda) supplies
the typing derivations and actual evaluator results.

## The world and the two argument codes

Use the following direct store entries, all allocated after empty roots:

| Imprecise store | Precise store |
|---|---|
| `X ↦ ℕ` | `Z ↦ ℕ` |
| `P ↦ X⇒ℕ` | `Y ↦ Z` |
| | `Q ↦ Y⇒ℕ` |

The world has `Matched X Y`, `Matched P Q`, and `PreciseOnly Z`.
It is constructed using the existing world constructors. In particular,
`Y` is occupied by its match with `X`, so it is not precise-only.

Write `Pair(X,Y,a)` for a matched-seal code, and `Only(Y,a)` for a
precise-only seal code. Their interpretations retain the actual seals,
the corresponding world capability, and payload membership in `a` at
the same index. Consider the two codes with endpoints `X,Y`:

`a = Pair(X,Y, Only(Z,ℕ))`

`b = Only(Y, Pair(X,Z,ℕ))`.

Both codes are syntactically valid: `X` represents `ℕ`, `Y` represents
`Z`, and `Z` represents `ℕ`. No arbitrary semantic record occurs in
either code.

If `u = 7 ↓ seal X ℕ` and
`v = (7 ↓ seal Z ℕ) ↓ seal Y Z`, then `u,v` belong to `a` at every
index: the required capabilities are exactly `Matched X Y` and
`PreciseOnly Z`.

If `W′` is any future of this world, then no pair belongs to the lifted
interpretation of `b` in `W′`. Such membership would require
`PreciseOnly Y`, while future closure preserves `Matched X Y`.
Disjointness of precise-only and matched slots gives a contradiction.
This is not merely emptiness at the current world: even a future permitted
to add other capabilities cannot remove that existing match.

## Contravariance exposes the ambiguity

Let `F = λx:X.0 : X⇒ℕ` and `G = λy:Y.1 : Y⇒ℕ`.

If the argument code is `b`, then `F,G` belong to `b⇒ℕ` at every index.
The arrow's call obligation quantifies over every future world and every
smaller index, but there are no related arguments at any of them.

If the argument code is `a`, then `F,G` do not belong to `a⇒ℕ` at index
`3`. The arrow test at index `2` may supply the related arguments `u,v`.
Both calls return in one step, giving the unequal naturals `0,1` at
residual index `1`. The backward observation and actual-result uniqueness
exclude a different imprecise result obtained by choosing another fuel.
The contradiction persists at every same-scope future preserving the
original capabilities.

Thus fixed interpretation is not the same as coherence between different
codes. The same-endpoint arrow meanings really differ; this is not just
a failed attempt to construct a proof.

## A matching ground projection cannot choose the reader code

Form nominal payload codes with endpoints `P,Q`:

`packetCode = Pair(P,Q, b⇒ℕ)`

`readerCode = Pair(P,Q, a⇒ℕ)`.

The payloads `f = F ↓ seal P (X⇒ℕ) : P` and
`g = G ↓ seal Q (Y⇒ℕ) : Q` belong to `packetCode` at every index.
Consequently the following existential premise has a checked witness:

`∃ c : Code S T P Q. related (denote c) W k f g`.

Define the actual dynamic packets `p = f⟨P!⟩ : ★` and
`q = g⟨Q!⟩ : ★`. Each packet is a value, and both nominal queries match:
`p⟨P?⟩` returns `f` and `q⟨Q?⟩` returns `g`, each in one step with no
allocation. The outer tags also have the required semantic match `P,Q`.

The checked positive control states that, for every `k`, these two
projections satisfy `Observed (denote packetCode) W k`. All three
observation clauses hold when the exact code is retained.

However, they cannot satisfy `Observed (denote readerCode) W 4`.
The precise one-step return would require the returned payloads to belong
to `readerCode` at index `3` in a future world. Removing the outer matched
seals would give the already refuted membership of `F,G` in `a⇒ℕ`.
The existential witness, endpoint agreement, actual tag checks, and
outer match therefore do not justify decoding into a separate reader code.

The fully applied, well-typed computations expose the difference as data:

Diagram:

    (p⟨P?⟩ ↑ unseal P (X⇒ℕ)) u      (q⟨Q?⟩ ↑ unseal Q (Y⇒ℕ)) v
                   │                                │
                   │ 3 steps                        │ 3 steps
                   ▼                                ▼
                   0                                1

The actual evaluator witnesses use three store-preserving steps: projection,
unseal, and application. `runtime-separates` proves failure of the natural
observation at index `4`, again allowing independent matching fuel.

## What is, and is not, refuted

This refutes endpoint-only recoding of an existential **fixed-code**
payload. R18 had needed an arbitrary semantic record; R20 does not.
It also shows why checking only the packet's outer nominal capability is
insufficient: the conflicting requirement is in an arrow domain.

It does not refute the existing interpretations individually, the
all-code universal identity theorem, exact-code projection, direct-natural
nominal projection, or the calculus's dynamic gradual guarantee. These
programs are typed counterexample fixtures for a proposed semantic rule;
no term-imprecision derivation relating the two whole programs is claimed.

The general dynamic extension is stopped here. The next bounded task is
to state and test a **producer/consumer code-coherence obligation** before
attempting its projection compatibility theorem. Simply adding a
coherence field containing the desired projection theorem would not
discharge that task. Any restriction on which codes are allowed in a world
must be checked recursively through arrow domains, not only where a value
happens to provide positive nominal evidence. No such restriction or
coherence theorem has been adopted or validated in this checkpoint.

## Regression boundary and verification

The existing suite remains imported unchanged; the two new modules are
added to `LR-narrow/LRNarrowAll.agda`.

| Regressions | Effect of this checkpoint |
|---|---|
| R1–R7, R9–R10, R13 | No change to physical scopes, actual histories, independent fuel, three observations, or index accounting. The separation proof itself uses those observations. |
| R8, R11 | No match is changed or discarded. Persistent matched/precise-only disjointness is essential to the new negative proof. |
| R12, R14–R17 | No replacement inversion, pending-value shortcut, cast simplification, or recursive-continuation claim is added. |
| R18 | Equal-natural interpretation and rejection of arbitrary semantic-record witnesses remain valid. The new obstruction is strictly beyond that base-endpoint test. |
| R19 | Both codes live at future-local scopes and retain their actual nominal names. No root-type preimage or scope reset is used. |
| E1–E24, N1/N2 | All previous typed runs, repeated casts/seals, latent blame, and nominal-query controls remain part of the shared suite. No general compatibility conclusion is inferred from them. |

The new negative theorem and exact-code positive control are checked in
the full Agda MCP aggregate without goals, invisible metavariables, or
errors. Independent `make check` passes all five targets, including the
historical ground-cast and occupied-slot projection regressions.
No new postulates, holes, termination overrides, or positivity escapes
are introduced.
