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

## Baseline status

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

## Second experiment: visible return scopes

`proof/LR-narrow/ScopedReturnsExperiment.agda` states a proof-local
`ScopedReturns` replacement for the successful-return join. It retains an
ordinary future world, but embeds its precise scope into the physical
precise result scope. The imprecise scope remains exact. The witness requires:

- An injective, order-preserving embedding `ρ`.
- Preservation of every visible store lookup by `ρ`, using the existing
  `StoreRename` relation. In particular, representations are preserved, not
  merely the number of names.
- Agreement of the runtime and semantic actions on **every caller term**.
- A visible value `V` with physical result exactly `rename ρ V`.
- The existing indexed value relation on the visible results.

`literal-returns` supplies this witness at every index for the first
experiment, hiding only `Z`. This is a new proof-local observation, not a
change to `PairedReturns` or the live LR.

`store-rename-bind`: if `ρ` preserves store lookup, then extending both
stores by `A` and `rename ρ A` preserves lookup under `keep ρ`. This works
for arbitrary types and embeddings. A hidden name need not remain at the
head of the physical store.

For a returned natural `n`, test the continuation
`((Λα. λx:ℕ. x + n)[Y]) 1`. `continue-⊢`, `continue-↠`, and
`continue-eval` prove typing, the complete six-step trace, and the exact
interpreter return `n + 1` at every sufficient fuel. `continue-scope`
proves that this family executes in both scopes with related final stores
and renamed final values, for every lookup-preserving embedding. Applied
after the literal test, the visible allocation history is `X,Y,T`; the
physical history is `X,Y,Z,T`. The final embedding keeps `T`, skips `Z`,
and keeps `Y,X`. Both continuations return `8`.

This establishes stability under fresh allocation and this continuation
family, **not** a general evaluation-renaming theorem.

## Second experiment: an escaping seal prevents lowering

`proof/LR-narrow/EscapingSealExperiment.agda` repeats the test with
`U = Λα. λx:α. x : ∀α. α ⇒ α`, again revealed at the absent old slot
`X` and instantiated at `X`. The input and both returned functions are
typed. The bare application takes one step; the wrapped application takes
two. Their allocation histories are the same as in the literal test.

The returned functions are exactly:

    Vᴵ = (λx. x) ↑ (seal Y′ X′ ↦↑ unseal Y′ X′)

    Vᴾ = (((λx. x) ↑ (seal Z Y ↦↑ unseal Z Y))
                   ↑ (id↓ Y ↦↑ id↑ Y))
                   ↑ (seal Y X ↦↑ unseal Y X)

The precise result has type `X ⇒ X`: neither `Y` nor `Z` appears in its
result type. But `Z` is still present in the returned conversion syntax.

`wrapped-function-not-lowered`: if `Vᴾ` is the weakening of any value or
term in the two-name scope, then `⊥`. The proof uses a syntax probe for
the domain seal of the innermost reveal. Renaming commutes with the probe;
weakening cannot produce the fresh name `Z`.

`wrapped-function-not-in-paired-scope` strengthens this to **every**
lookup-preserving embedding of the selected two-name paired world into
the physical three-name store. Keeping `Z` instead of hiding it gives the
wrong representation for a visible name. Thus merely choosing a different
embedding of that world does not repair this example. This theorem does
not quantify over every alternative future world or every possible
behavioral scope relation.

The escaping seal is not evidence of a behavioral failure. The checked
data observations retain the physical stores:

Diagram:

    (Vᴵ (7 ↓ seal X′ ℕ)) ↑ unseal X′ ℕ
       │
       ▼
       7

    (Vᴾ (7 ↓ seal X ℕ)) ↑ unseal X ℕ
       │
       ▼
       7

`bare-use-⊢` and `wrapped-use-⊢` prove typing; `bare-use-eval` and
`wrapped-use-eval` check exact interpreter returns at fuel `20`.

## Third experiment: behavioral elimination of private seal adapters

`proof/LR-narrow/PrivateSealBehavior.agda` introduces a syntax certificate
`PrivateIdentity Σ A F`, with these explicit clauses:

- `λx. x` is certified at `A ⇒ A` in every store `Σ`.
- If `Σ(X) = R` and `F` is certified at `X ⇒ X`, then
  `F ↑ (seal X R ↦↑ unseal X R)` is certified at `R ⇒ R`.
- If `F` is certified at `A ⇒ A`, then
  `F ↑ (id↓ A ↦↑ id↑ A)` is certified at `A ⇒ A`.

The certificate contains no assumed application or compatibility premise.
`private-value` and `private-typed` derive valuehood and typing.
`private-rename` proves preservation under every lookup-preserving store
embedding, including embeddings that retain private names below later
allocations.

`private-application`: if `F` is certified and `V` is a value, then
`F V` reduces to **exactly `V`**, with only store-preserving steps.
The proof is induction on the certificate. At a seal adapter, apply the
induction hypothesis to `V ↓ seal X R`, lifted through the matching
unseal, and then cancel that seal/unseal pair. There is no restriction
to natural arguments: `V` may itself contain functions, universals,
casts, or private seals.

`private-pair-application`: if two certified functions receive typed value
arguments related by any relation `S` across their physical scopes, then
their applications return `S`-related values in the same physical stores.
This follows from the exact-result theorem; it does not require a common
raw-store future, a representation alias, or lowering the functions.

`bare-certificate` and `wrapped-certificate` certify the exact closures of
the escaping-seal experiment, for **any closed root representation**.
The precise certificate retains `Z`; the imprecise certificate has no
corresponding private slot. Thus this is a behavioral treatment of the
actual escaping functions, not an erasure of their syntax.

### Composition through another universal instantiation

`private-instantiation`: if `F` is certified at `(∀α.B) ⇒ (∀α.B)`,
`U : ∀α.B` is a value, and `U[R]` reduces to `M` with changes `ψ`, then
`(F U)[R]` reduces to `M` with the certified store-preserving prefix
followed by `ψ`. The suffix may allocate names or end in blame.
`private-following-store` proves that the prefix does not change the
suffix's final physical store. This is a proved composition principle for
arbitrary suffix traces, not a new assumed compatibility field.

`proof/LR-narrow/PrivateSealInstantiationExperiment.agda` checks a concrete
instance. Set the old representation to `P = ∀α. α ⇒ α`. Add the matching
old-`X` seal adapter to the bare and wrapped functions, obtaining
`Fᴵ : P ⇒ P` and `Fᴾ : P ⇒ P`. Use arguments
`Uᴵ = Λα. λx:α. x` and `Uᴾ = Uᴵ ↑ c`, where `c` is an absent-slot
universal reveal at the already-private `Z`.

The complete observations are `(Fᴵ Uᴵ)[ℕ] 7` and `(Fᴾ Uᴾ)[ℕ] 7`.
Both return `7`. `observe-bare-↠` and `observe-wrapped-↠` compose the
general application and instantiation lemmas with explicit allocation
traces. Independent proof-carrying interpreter checks succeed at fuel
`9` and `20`, respectively, with exact final contexts and stores.

The imprecise store finishes with three names; the precise store finishes
with five. In addition to the original private `Z`, the precise universal
wrapper creates a second private allocation during the suffix. The final
embedding skips the newest private name, keeps the new paired name,
skips old `Z`, and keeps the original pair. `final-store-embedding`
preserves every visible lookup; `final-values-related` proves the two
natural results related at every index in the visible continued world.
No physical allocation is deleted or identified with another name.

The experiment therefore succeeds both for arbitrary value arguments to
the certified adapters and for a subsequent universal elimination that
introduces another private scope. The elimination theorem concerns
reduction traces; it is not yet the live step-indexed computation relation.

## Generalization: arbitrary function bodies and fresh closure results

`proof/LR-narrow/FunctionSealRetraction.agda` removes the identity-body
restriction for a balanced adapter. Define

    roundtrip X A Y B F =
      (F ↓ (unseal X A ↦↓ seal Y B)) ↑ (seal X A ↦↑ unseal Y B).

`roundtrip-return`: if `F` and `V` are values and `F V` reduces to a value
`U` with store changes `χ`, then `roundtrip X A Y B F V` reduces to
**the same `U`**, with three store-preserving prefix steps, `χ`, and one
store-preserving suffix step. `roundtrip-blame` proves the corresponding
claim for blame, with two suffix steps. The store-action lemmas prove
that the final physical store is exactly `χ` applied to the initial store.

The proof transports the result seal and its matching unseal through
every allocation in `χ`. It never removes seals *inside* `U`. Hence `U`
may be an arbitrary newly returned closure, not just the argument `V`.
This is a computational retraction, not a type-imprecision alias.

### A single function reveal, without a roundtrip assumption

`proof/LR-narrow/FunctionSealCompatibility.agda` goes beyond balanced
adapters. Define

    reveal-function X A Y B F = F ↑ (seal X A ↦↑ unseal Y B).

`typed-reveal-function-return`: if `Σ(X) = A`, `Σ(Y) = B`,
`F : X ⇒ Y` and `V : A` are closed values, and
`F (V ↓ seal X A)` reduces with changes `χ` to a value `Z`, then there
exists a value `U : χB` in the final physical store such that
`Z = U ↓ seal (χY) (χB)` and `reveal-function X A Y B F V` reduces to `U`.
The full trace consists of one prefix step, `χ`, and one suffix step.
The same overhead suffices when the body blames.

Crucially, the sealed shape of `Z` is **derived**, not assumed as a new
compatibility obligation: preservation gives `Z : χY`, lookup transport
gives `(χΣ)(χY) = χB`, and canonical forms plus lookup uniqueness identify
the payload and representation. No syntactic restriction is placed on
`F` beyond its valuehood and typing.

For relational composition, `SealedValues Xᴵ Aᴵ Xᴾ Aᴾ S` has exactly
this clause: if `Uᴵ` and `Uᴾ` are values and `S Uᴵ Uᴾ`, then it relates
`Uᴵ ↓ seal Xᴵ Aᴵ` to `Uᴾ ↓ seal Xᴾ Aᴾ`. The names and representation
types remain concrete endpoint data; the relation does not assert
`Xᴵ ⊑ Aᴾ` or identify either name with its representation.

`related-function-reveals-return`: if the two abstract-body runs return
values related by this seal lifting at their transported output slots,
then the revealed applications return `S`-related payloads. The endpoints
may allocate independently and finish in different physical scopes.
This theorem transports an already established body-result relation; it
does not assert that arbitrary pairs of function bodies are related.

### Non-identity regression with a private allocation inside the body

`proof/LR-narrow/FunctionSealClosureExperiment.agda` starts in a store
containing `X ↦ ℕ` and `Y ↦ (ℕ ⇒ ℕ)`. Its abstract functions are

    Fᴵ = λn:X. (λx:ℕ. n ↑ unseal X ℕ) ↓ seal Y (ℕ ⇒ ℕ)
    Fᴾ = λn:X. ((Λα. λx:α. n ↑ unseal X ℕ)[ℕ])
                   ↓ seal Y (ℕ ⇒ ℕ).

Apply their public reveals to a natural `n`. The bare body returns a new
closure without allocating. The other body allocates `Z ↦ ℕ` and returns
a new closure whose function conversion still mentions `Z`:

    Uᴵ = λx:ℕ. (n ↓ seal X ℕ) ↑ unseal X ℕ
    Uᴾ = (λx:Z. (n ↓ seal X ℕ) ↑ unseal X ℕ)
           ↑ (seal Z ℕ ↦↑ id↑ ℕ).

`public-bare-↠` and `public-private-↠` use the **typed general theorem**
above to obtain these payloads; they do not duplicate the adapter proof.
`related-public-results` uses the relational theorem with a proved
behavioral relation: for every pair of value arguments `Wᴵ`, `Wᴾ`,
`Uᴵ Wᴵ` reduces to `n` in two steps and `Uᴾ Wᴾ` reduces to `n` in four.
These are constant functions, not identity adapters; neither returned
closure is the original natural argument.

The fully applied programs are checked for **all naturals `n` and `m`**.

Diagram:

    (reveal-function X ℕ Y (ℕ⇒ℕ) Fᴵ n) m
       │ 5 steps, no allocation
       ▼
       n

    (reveal-function X ℕ Y (ℕ⇒ℕ) Fᴾ n) m
       │ 8 steps, one private allocation
       ▼
       n

The reduction proofs compose the general adapter theorem with the proved
closure behavior. Independent interpreter equalities check the exact
fuel and final stores: two names on the bare side and three on the private
side. For example, `n = 7` and `m = 9` returns `7`, not `9`.

## Backward observations and fuel accounting

`proof/LR-narrow/FunctionSealObservation.agda` now connects an **actual
interpreter return** to the abstract-body return. This is not a theorem
restricted to the forward traces constructed in the previous experiment.

`unseal-return-invert`: if `Σ(Y) = B`, `M : Y` is closed, and
`M ↑ unseal Y B` returns `U` at fuel `n`, then there are body fuel `b`
and changes `χ` such that the interpreter returns
`U ↓ seal (χY) (χB)` from `M` at fuel `b`, `b + 1 ≤ n`, and the
observed history is exactly `χ` followed by one `keep`. The body return
is in the **observed final physical context**, and `U : χB` in `χΣ`.

`reveal-function-return-invert`: if `Σ(X) = A`, `Σ(Y) = B`,
`F : X ⇒ Y` and `V : A` are closed values, and
`reveal-function X A Y B F V` returns `U` at fuel `n`, then the
interpreter returns `U ↓ seal (χY) (χB)` from `F (V ↓ seal X A)`
at some fuel `b`, where

    b + 2 ≤ n
    observed changes = keep ∷ (χ ++ [keep]).

All private allocations belong to `χ`; neither administrative step
changes the physical store or the action on caller terms. The payload
in the recovered body return is exactly the observed `U`, not a lowered
term or a merely related replacement.

The proof inverts the initial function-reveal step, uses the existing
evaluation-frame phase theorem to recover the operand run, then applies
preservation and canonical forms to its returned value. The final
matching unseal must take one step and cannot allocate. Frame transport
is normalized at one boundary using an equality of context, changes, and
term; no equality of unrelated trace witnesses is assumed.

`function-seal-body-budget`: if `b + 2 ≤ n` and `n < k`, then `b < k`
and `k ∸ n ≤ k ∸ b`. Thus the recovered observation fits below the same
cutoff, and a downward-closed result relation at the body's residual
index can be lowered to the observer's residual index. This arithmetic
fact does not itself establish that value relation's downward closure.

### Regression with arbitrary surplus fuel

`proof/LR-narrow/FunctionSealObservationExperiment.agda` reuses the
allocating, non-identity closure maker above. For every natural `n` and
every surplus fuel `s`, its public application returns `Uᴾ` at fuel
`4 + s`, with the same exact four-step trace and three-name final store.

The general inversion theorem is applied to that interpreter equality.
`recovered-body-fuel` checks that its computed body fuel is always `2`;
`recovered-body-changes` checks that its computed history is exactly one
`keep` followed by the private `ℕ` allocation. `recovered-body-store`
checks the resulting physical store. These tests inspect the witnesses
computed by the general proof, rather than supplying a separate body run.
The earlier fully applied observations still check that both returned
closures yield the captured `n` when subsequently applied to any natural.

## Conclusion and next critical path

Unused-allocation hiding is a viable special case, but it is **not** a
complete return interface for universal wrapper closure. Type-level
non-occurrence alone does not justify dropping a name from returned
syntax. The higher-order example needs its private seal retained.

The behavioral route now has a local compatibility theorem for arbitrary
typed function bodies, including allocating bodies returning new closures.
The identity certificate is no longer the only positive evidence. Keep
physical private scopes and relate the returned values behaviorally;
do not replace the live `PairedReturns` with `ScopedReturns`, which still
requires literal lowering of every returned value.

Backward return decomposition and its two-step fuel bound now check for
arbitrary typed function bodies. No new counterexample was found in this
step. The next critical step is a **proof-local, scope-aware computation
observation** using those results, together with a value relation whose
function clause and nominal seal lifting retain physical private scopes.

Prove downward closure and closure under later visible/private allocations,
then derive the function-reveal case. Complete the interpreter-level
assembly needed for the forward-return and forward-blame clauses, reusing
the existing frame machinery and the forward trace lemmas. The supplied
body-result relation `S` must come from the relation's induction/future
structure, not be added as an assumed compatibility field. Only integrate
the new observation interface into the live LR after this bridge checks.

General evaluation transport, the complete observation interface for
escaping closures, and the four `RevealObligations` remain open. No field
has been discharged by these experiments, and the fundamental property is
not yet complete. `VarImp` and the live LR remain unchanged.

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
