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

## Fixed-root scope-aware semantic model

`proof/LR-narrow/PhysicalScope.agda` keeps a fixed visible root store and
extends its physical store by arbitrary fresh bindings. Every physical
name survives later extensions, including names private to one endpoint.
The two endpoints extend independently. A physical extension need not have
a partner or satisfy the live world's allocation rules.

Write `S` and `T` for physical scopes over their respective roots, and
`p : S ≤ S′` for a future allocation sequence. The maps `pM` and `pA`
shift terms and types through that sequence. Typing and valuehood are
preserved; composition agrees with successive shifting. For an interpreter
history `χ`, the canonical result scope `S·χ` satisfies

    store(S·χ) = χ(store(S))
    (S ≤ S·χ) M = χM.

These are the proved `advance-store` and `advance-term` equations. No
runtime term or store entry is lowered, erased, or equated with a different
name. The root remains fixed: extending the visible semantic environment
is a separate operation not yet defined by this prototype.

### Semantic types and computation observations

`proof/LR-narrow/ScopedBehavior.agda` defines `ScopedType`: two root types
and a relation `V_A(S,T,k,U,V)` on physical values, with typing, downward
closure, and independent-future closure. It constructs three such types:

- `natural`: `V_ℕ(S,T,k,U,V)` iff `U = n` and `V = n` for some natural
  `n`, at every index including zero.
- `arrow A B`: the functions are typed values, and for all independent
  futures `p : S ≤ S′`, `q : T ≤ T′`, all `j < k`, and all
  `V_A(S′,T′,j,U,V)`, their applications satisfy
  `O_B(S′,T′,j,(pF) U,(qG) V)`.
- `nominal A X Y`: if the root entries at `X` and `Y` are the respective
  types of `A`, then the relation contains exactly
  `U ↓ seal (S X) (S Aᴵ)` and `V ↓ seal (T Y) (T Aᴾ)` with
  `V_A(S,T,k,U,V)`. The payload keeps the same index. The constructor uses
  actual store-lookup proofs; it introduces no name-to-representation
  imprecision rule.

Here `O_B`, implemented by `ObservedComputations`, has three clauses:

- If `M` returns `U` with history `χ` at fuel `n < k`, then either `N`
  eventually blames or it returns `V` with history `ψ` and
  `V_B(S·χ,T·ψ,k−n,U,V)`.
- If `N` returns `V` with history `ψ` at fuel `n < k`, then `M` returns
  `U` with history `χ` and `V_B(S·χ,T·ψ,k−n,U,V)`.
- If `M` blames at fuel `n < k`, then `N` eventually blames.

The result terms are interpreted directly in their independently computed
physical scopes. There is no existential join of raw stores and no premise
requiring either returned value to be a weakening of root syntax.

`ScopedComputations` is the Kripke closure of this observation:

    C_B(S,T,k,M,N) iff
      for all p : S ≤ S′ and q : T ≤ T′,
      O_B(S′,T′,k,pM,qN).

Downward closure is proved for both `O` and `C`. Independent-future closure
is proved for `C` by composing futures. This is not an assertion that
arbitrary evaluation commutes with allocation. The typing and closure
invariants of all three semantic-type constructors are proved, not assumed
as new function-reveal compatibility fields. In particular, the arrow
clause quantifies over every smaller index, so downward closure does not
require lifting a domain relation to a larger index.

### Non-vacuous tests of the model

`proof/LR-narrow/ScopedBehaviorExperiment.agda` supplies the following
witnesses, without changing the live logical relation:

- `closures-related` relates the actual non-identity `Uᴵ` and `Uᴾ` above
  at `arrow natural natural`, for every captured natural `n` and every
  index. Their calls are checked after arbitrary independent future
  allocations. The precise function still carries its private `Z` seal.
  Generic interpreter lemmas establish the two- and four-step returns in
  those future stores; determinism then proves all bounded observations.
- `closures-future-related` applies the model's future-closure theorem to
  these escaping values. `body-results-related` relates their sealed body
  results at the model's nominal type for `Y`.
- `decoded-body-results` supplies this nominal/arrow relation to the
  earlier general function-seal return theorem. The payload relation now
  comes from the constructed semantic model rather than an ad hoc
  relation on these two functions.
- `makers-observed` proves all three observation clauses for the public
  maker computations at every index in their initial scopes. It now derives
  that observation from the abstract bodies using general function-seal
  compatibility, rather than directly comparing the public returns. It is an
  `ObservedComputations` witness, not yet a `ScopedComputations` witness
  for makers placed under arbitrary prior allocations.
- `literal-wrapper-observed` accepts the original bare/wrapped literal
  computations at every index despite their different final store sizes.
  Their result type is natural; this is not a universal-value theorem.

`observed-from-returns` is the general introduction lemma used by these
tests: two known interpreter returns with related results at index `k`
imply the three observation clauses at `k`. Fuel-independent uniqueness
identifies all later observed returns; downward closure supplies the
residual index, and terminal uniqueness excludes left blame.

## General scope-aware function-seal compatibility

`proof/LR-narrow/ScopedFunctionSeal.agda` proves the general bridge within
the fixed-root model. Let the root entries at `Xᴵ`, `Xᴾ` be `Aᴵ`, `Aᴾ`,
and those at `Yᴵ`, `Yᴾ` be `Bᴵ`, `Bᴾ`, where `A` and `B` are semantic
types. The endpoints may have different physical scopes `S` and `T`.

`function-seals-related`: if `F` and `G` are related at index `k` at

    arrow (nominal A Xᴵ Xᴾ) (nominal B Yᴵ Yᴾ),

then the following values are related at `arrow A B`, at the same index
and in the same physical scopes:

    F ↑ (seal (S Xᴵ) (S Aᴵ) ↦↑ unseal (S Yᴵ) (S Bᴵ))
    G ↑ (seal (T Xᴾ) (T Aᴾ) ↦↑ unseal (T Yᴾ) (T Bᴾ)).

Every nominal type above includes its actual root-lookup proofs. There is
no hypothesis saying the functions are identities, have balanced wrapper
syntax, terminate, or return root-scoped syntax. Their bodies may allocate
independently, return newly created closures, or blame. As with every
compatibility lemma, their abstract behavior must already be related; the
theorem does not claim that arbitrary typed functions are related.

### Interpreter and observation bridge

`FunctionSealObservation.agda` now also proves:

- `unseal-return-expand`: if the interpreter returns
  `U ↓ seal (χY) (χB)` from `M` with history `χ`, then the interpreter
  returns the same `U` from `M ↑ unseal Y B`, with history
  `χ ++ [keep]`. The return fuel is existential; the context, payload, and
  history are exact. The proof assembles the existing evaluation frames.
- `unseal-blame-invert`: if `Σ(Y) = B`, `M : Y` is closed, and
  `M ↑ unseal Y B` blames at fuel `n`, then `M` blames at some fuel
  `b ≤ n`. If instead its operand phase returned, preservation and
  canonical forms would give a matching seal; terminal uniqueness excludes
  blame from that matching unseal. Thus this is not an assumed blame rule.

`observed-unseals` applies these facts and the earlier return inversion
to prove all three observation clauses. It decodes an observation at
`nominal B Xᴵ Xᴾ` into an observation at `B`. On each observed return,
the body runs at fuel `b ≤ n`; downward closure changes its residual
index from `k−b` to `k−n`. On the matching endpoint, frame assembly
supplies the required interpreter run. A permitted precise blame is
propagated through its unseal; a left blame is first inverted, passed
through the body observation, and then propagated on the right.

`advance-variable` and `advance-type` equate the runtime transport of root
names and types with their readings in the result scope. `advance-keep`
proves that the suffix `keep` leaves exactly the same physical scope.
These equations normalize the boundary without lowering returned terms.

`observed-pure-steps` adds the initial function-reveal step at both
endpoints, preserving the same observation index. Together these give
`observed-function-seals`, a general computation theorem from related
abstract-body computations to related public applications.

Finally, `function-seals-related` obtains the body observation from the
abstract arrow clause, at every independent future and every `j < k`.
The nominal input clause seals the related arguments; the computation
theorem supplies the public calls. The body relation is therefore derived
from the model, not added as an assumed compatibility field.

### Regressions through the general theorem

`ScopedBehaviorExperiment.makers-observed` now uses the general computation
theorem on the non-identity maker bodies, including the private allocation
and the returned function that retains its private seal. The body-result
relation is the model's nominal lifting of its arrow relation.

`ScopedFunctionSealExperiment.agda` separately instantiates the **value**
theorem. The abstract function `λx:X. n ↓ seal X ℕ` is related to itself
at every index and under all independent future allocations. Its public
reveal is consequently related at `ℕ ⇒ ℕ`. Complete reduction chains and
interpreter equalities show that applying it to any `m` returns `n` in
three steps, so this is not an identity-body test.

The same module proves relatedness when the precise abstract function is
`λx:X. blame`, both with a constant left function and with a blaming left
function. `observed-from-right-blame` justifies the abstract observations
using an actual right blame run and terminal uniqueness. Exact public
three-step blame runs are checked, and `forward-blame-through-compatibility`
invokes the forward-blame clause obtained from the general value theorem.

## Visible-environment extension after private allocations

The next checkpoint separates the **physical model roots** from the
**visible semantic names**. A root contains the complete physical store,
including private slots. Visibility is a separate pair of injective,
order-preserving embeddings into the endpoint roots. Changing roots never
erases a slot or rewrites a runtime term.

### Physical rebasing and semantic stability

`PhysicalScope.graft S P` regards an extension `P` of `store(S)` as an
extension of the original root. The checked equations include

    store(graft S P) = store(P)
    type(graft S P, A) = type(P, type(S, A))
    graft S (advance P χ) = advance (graft S P) χ.

The variable and future-term actions satisfy corresponding equations.
Every future of `graft S P` factors through a future of `P`, with equality
of both the endpoint scope and the future path. Thus rebasing does not
remove any of the later calls tested by an arrow relation.

`ScopeRebase.Rebase S T` takes old semantic types to the model rooted at
the complete stores of `S` and `T`. Its value relation is defined by

    related(rebase A, P, Q, k, U, V)
      = related(A, graft S P, graft T Q, k, U, V).

Endpoint types are transported through `S` and `T`; `U` and `V` are
unchanged. Valuehood, typing, downward closure, and future closure are
proved for the rebased type. The observation and Kripke-computation
relations transfer **in both directions**, at the same index and with
the same runtime terms. This includes forward return, backward return,
and forward blame, not just terminating examples.

Rebasing commutes with natural and nominal value relations. It commutes
with arrows in the following precise sense: if two values belong to
`rebase (arrow A B)`, then they belong to `arrow (rebase A) (rebase B)`,
and conversely. These are proved implications between value relations,
not asserted equality of the proof-carrying semantic records. The
converse uses the future-factorization theorem.

### Visible names and fresh extension

`VisibleEnvironment Σᴵ Σᴾ n` consists of

- two embeddings from the `n` visible names into the physical roots;
- a semantic representation type for each visible name;
- actual endpoint store lookups at that type's endpoint representations.

The meaning of a visible name is the nominal lifting of its representation
at the two selected slots. Rerooting through independent physical scopes
keeps the visible count unchanged and skips their private allocations.
Every old meaning agrees with its rebased relation.

`Extend env A` adds one physical binding of `Aᴵ` and one of `Aᴾ`, and
one visible name selecting those fresh slots. Its head represents the
rebased `A`; old representations are rebased through the paired bindings.
`old-meaning` proves preservation of every old name's value relation in
arbitrary subsequent physical scopes. The embeddings retain their skips,
so adding a visible pair does not expose intervening private names.

This environment deliberately describes **paired nominal names**. It is
not yet a general interpretation of syntactic type substitution or of
world entries with a missing endpoint. Neither a universal type nor its
compatibility rule is defined by this checkpoint.

### Private-before-visible regression

`VisibleEnvironmentExperiment.agda` starts with the earlier visible names
`X : ℕ` and `Y : ℕ⇒ℕ`. The precise maker allocates private `Z : ℕ` and
returns its non-identity closure. After rerooting, a new visible pair
`W : ℕ⇒ℕ` is added. The precise physical order is `W, Z, Y, X`, while
the visible order is `W, Y, X`. A checked exclusion theorem states that
no visible name maps to `Z`.

At every index, the old escaped closures remain related at their rebased
arrow type and at the new model's arrow of rebased component types.
Consequently their arrow clause still tests arbitrary independent future
allocations. Sealing these closures at the fresh `W` pair satisfies its
new nominal meaning. The precise closure continues to contain `Z`; no
root-scoped replacement or alias is used.

The module also performs the later allocation in the interpreter. For
the bare and private closures `F`, respectively, it checks the typed
continuation

    ((Λα. F) [ℕ⇒ℕ]) m.

Here `α` is unused in the result type, but instantiation still allocates
the fresh function slot. The closure syntax is weakened under the binder
in Agda. For every captured natural `n` and input natural `m`, both calls
return `n`: six steps on the bare side and eight on the private side.
Each run records exactly one new binding and otherwise only `keep`
steps; the final stores are exactly the extension's endpoint roots.
Explicit reduction chains show the private seal used after that binding.
All three computation-observation clauses also hold at every index by
the return theorem and the checked rebasing bridge. The earlier maker
theorems supply the preceding private allocation; these are staged runs,
not a new general theorem about universal instantiation.

## Family-indexed universal clauses

`ScopedUniversal.agda` now constructs paired and right-only universal
semantic types. Both have proved downward and independent-future closure;
both observe actual type applications in their physical result scopes.
This is a family-indexed interpretation, not yet a recursive interpretation
of every type-imprecision derivation.

### Small result families

The model's value relations live in `Set`, while the record `ScopedType`
lives in `Set₁`. Quantifying directly over all such records inside the
universal value relation would therefore leave the current universe. This
checkpoint does not add resizing, impredicativity, or a termination escape.

A `PairedFamily Cᴵ Cᴾ` instead supplies, for every independent physical
scope pair `S,T`:

- a small set `Argument(S,T)` of argument codes/evidence;
- endpoint argument types `Rᴵ(a)` and `Rᴾ(a)`;
- an interpreted result type `F(S,T,a)` rooted at `store(S),store(T)`;
- endpoint equalities
  `F(S,T,a)ᴵ = (S Cᴵ)[Rᴵ(a)/α]` and
  `F(S,T,a)ᴾ = (T Cᴾ)[Rᴾ(a)/α]`.

Here `S C` lifts the free physical names under the bound variable `α`.
The new `scopeBody` laws justify that action. Codes may include syntactic
types and admissibility derivations; they do not contain arbitrary
`ScopedType` records. A fixed family itself may be large without making
quantification over its codes large.

`RightFamily Cᴵ Cᴾ` supplies the same data except that only the precise
argument is selected, and the imprecise endpoint of `F(S,T,a)` is `S Cᴵ`.
The precise argument is not restricted to `★`.

These records contain result interpretations and their typing equations,
not wrapper-compatibility hypotheses. They deliberately do **not** yet
assert that a chosen argument family covers every live imprecision rule,
or that different argument presentations have coherent interpretations.
Those properties must come from a body/type-environment interpretation.

### Paired and right-only tests

By definition, typed universal values `U,V` are related at
`universal F`, scopes `S,T`, and index `k` if, for all independent futures
`p:S→S′`, `q:T→T′`, all `j<k`, and all `a:Argument(S′,T′)`,

    Observed(F(S′,T′,a), root, root, j,
             (p U)[Rᴵ(a)], (q V)[Rᴾ(a)]).

The result model is rooted at the actual call-site stores. Subsequent
bindings, including surplus wrapper bindings, remain in its independent
result scopes. The usual valuehood and endpoint-typing requirements are
part of the clause even at index zero.

For `rightUniversal F`, the corresponding clause is

    Observed(F(S′,T′,a), root, root, j,
             p U, (q V)[Rᴾ(a)])

for all `j≤k`, **including `j=k`**. The imprecise term performs no type
application, so there is no imprecise step to pay for an index decrement.
`right-at-same-index` explicitly exercises this boundary. Paired tests use
`j<k`; right-only tests must not inherit that strict bound accidentally.

Downward closure follows by composing the index inequalities. Future
closure composes the physical future paths and uses `lift-term-comp`.
Neither proof assumes that evaluation is equivariant under arbitrary
allocation or that returned syntax lowers to a visible root.

### Occurring-binder identity and wrapper regressions

`ScopedIdentity.identity-related` proves that `λx.x` belongs to
`arrow A A` for every scoped semantic type `A`, at every index. Its call
clause uses actual one-step beta returns and all three observation clauses.

`ScopedUniversalExperiment.IdentityFamily` then proves that
`Λα.λx:α.x` belongs to the constructed paired universal for **any supplied
small, scope-indexed family of semantic arguments**. The argument's
interpretation is supplied at the current physical scope pair, so it is
not restricted to types mentioning only the original roots.

For each argument interpretation `A`, instantiation allocates fresh
`Xᴵ:Aᴵ` and `Xᴾ:Aᴾ` and returns

    (λx.x) ↑ (seal Xᴵ Aᴵ ↦↑ unseal Xᴵ Aᴵ)
    (λx.x) ↑ (seal Xᴾ Aᴾ ↦↑ unseal Xᴾ Aᴾ).

The abstract identity is related at the fresh nominal type. General
function-seal compatibility yields the public adapters, and `arrow-from`
transfers that result from the rebased roots back to the actual allocated
result scopes. Thus the binder really occurs and the result is higher
order; this is not just a constant-body test.

An infinite nonempty family uses naturals and iterated endofunction types.
`tower-instantiations` eliminates the universal relation for every code
in that family. The fully applied `((Λα.λx:α.x)[ℕ]) n` has a typing proof,
an explicit four-step reduction chain, and an exact interpreter result `n`.

The constant-body family admits **all** syntactic type-argument pairs.
It relates `Λα.n` to `(Λα.n) ↑ ∀(id ℕ)` at every index and future scope;
their instantiations take two and five steps respectively. The wrapped
run allocates its outer argument slot and then a second slot representing
the first, exactly as in the original raw-store counterexample.

The right-only family relates `n` to that wrapped universal. Its tests
compare the zero-step imprecise return with the five-step precise return,
for every precise type argument and without reducing the index. This
isolates the asymmetric observation boundary; the constant body does not
satisfy the live `∀⊑` rule's bound-variable-occurrence premise, so this
test is **not** a fundamental-property instance of that rule.

## Body-derived result families and one-sided allocation

`ScopedBodyInterpretation` interprets a checked fragment of the existing
`Ty` syntax: naturals, variables, and arrows. There is no second type
language. Dynamic, boolean, and nested universal constructors are outside
this fragment; an environment entry can nevertheless denote **any**
already constructed `ScopedType`, including a nominal or universal type.

### Interpretation and coherence

The interpretation is defined by the following clauses:

- `⟦ℕ⟧η = natural`.
- `⟦X⟧η = η(X)`.
- `⟦A ⇒ B⟧η = arrow (⟦A⟧η) (⟦B⟧η)`.

If `C` and each `σ(X)` belong to the fragment, then
`⟦C[σ]⟧η = ⟦C⟧(X ↦ ⟦σ(X)⟧η)`.
`interpret-substitution` proves equality of the constructed records by
structural induction; `interpret-renaming` proves the renaming analogue.
The two endpoint types are exactly the syntactic endpoint substitutions.

`ScopedTypeEquivalence` records equal endpoint types and both directions
of the value relation, at every index and independent physical scope.
It does not require equality of records carrying proofs. It transports
all three computation-observation clauses and respects arrows, using the
reverse direction in the domain and the forward direction in the result.

If `S` and `T` are physical future roots, then
`rebase(S,T,⟦C⟧η) ≃ ⟦C⟧(X ↦ rebase(S,T,η(X)))`.
`BodyRebase.interpret-rebase` proves this equivalence recursively using
the already checked natural and arrow rebasing theorems.

If visible environments are extended by fresh slots `Xᴵ:Aᴵ` and
`Xᴾ:Aᴾ`, then interpreting a body in the extended environment is
equivalent to interpreting it with the fresh **nominal** meaning at its
head and rebased old meanings in its tail.
`VisibleBodyExtension.interpret-extended` proves this for every body in
the fragment. The new head is not identified with its representation.

### Derived paired families

`ScopedBodyFamily.BodyFamily` now constructs `PairedFamily` from a body
`C`, an old semantic environment `η`, and small argument codes with
denotations. At physical scopes `S,T`, an argument denoting `A` has result

    ⟦C⟧(α ↦ A, X ↦ rebase(S,T,η(X))).

Thus result interpretations are no longer independent assignments in this
construction. `ScopedTypeSubstitution.scope-instantiate` proves their
endpoint opening equations, allowing `A` to mention newly allocated
physical slots. The syntactic scope/opening, body-shift, and grafting laws
hold for all `Ty` syntax, not only the interpreted fragment.

Small codes still determine the tested arguments. This construction does
not assert coverage of all semantic types or invent a future action on
arbitrary codes. It derives the result from each given denotation.

`ScopedBodyFamilyExperiment` transfers the existing polymorphic identity
proof to the derived family and eliminates it for the nonempty infinite
natural/endofunction argument tower. It also checks the higher-order body
`(α ⇒ X) ⇒ (α ⇒ X)` with both a bound argument and an old environment
entry under arbitrary independent physical scopes. The existing typed,
four-step natural-result identity regression remains in the aggregate.

### Same-index right-only step expansion

`ScopedStepExpansion.observed-right-step` proves: if the evaluator takes
`N —→[χ] N′` from `T`, `N` is neither blame nor a value, and `M,N′`
are observed at index `k` in `S,step-scope(χ,T)`, then `M,N` are observed
at the **same** index `k` in `S,T`.

For `χ = bind A`, the continuation scope is `allocate T A`. Every returned
or blamed history is prefixed by the actual step. Forward return and
forward blame preserve their witnesses; backward return inverts the
precise step and uses downward closure from `k−n` to `k−(n+1)`.
There is no loss of the outer index and no lowering of returned syntax.

`ScopedStepExpansionExperiment` checks a right beta-return prefix, a
right beta prefix ending in blame, and a type-beta allocation with the
imprecise natural unchanged. These are all three-clause observations,
not just forward simulation tests.

## Structural body conversion compatibility

`ScopedBodyConversion` compiles both directions through the existing
natural/variable/arrow body fragment. A variable keeps its meaning or
exchanges a paired nominal slot for its stored representation. The latter
choice carries the two actual store lookups, not a compatibility premise.
For unchanged meanings the conversions are `id↑` and `id↓`; for a nominal
meaning they are `unseal X R` and `seal X R` at the corresponding endpoint.

The arrow clauses are the actual conversion constructors:

- `reveal(A ⇒ B) = conceal(A) ↦↑ reveal(B)`.
- `conceal(A ⇒ B) = reveal(A) ↦↓ conceal(B)`.

Thus negative occurrences use the opposite direction. All four endpoint
conversions have proved store validity. `ScopedConversionTransport` lifts
them through independent physical scopes and proves their frame transport
along actual allocation histories.

### Observations under frames and applications

`ScopedFrameComposition.frame-observed` proves: if the operands are
observed at `A` and the transported frames map related returned values
to observations at `B`, at every residual index `j≤k` and pair of operand
histories, then the framed computations are observed at `B` at index `k`.
It splits and assembles the real evaluator phases. The final scope is
`advance(S, operand-history ++ call-history)`, not a raw-store join or a
lowered value. Forward return, backward return, and forward blame are
all preserved.

`ScopedApplication.application-observed` proves: if `F,G` are related
at `arrow A B` at index `k`, `j<k`, and `M,N` are observed at `A` at
index `j`, then `F M,G N` are observed at `B` at index `j`.
If arguments allocate, the functions are transported along those exact
histories. Every residual call index is at most `j`, so it remains
strictly below the function's original `k`.

### Both conversion directions

If `M,N` are observed at the abstract interpretation of `C` at index `k`,
then applying the compiled reveals gives observations at the public
interpretation at the same `k`. Conversely, if `M,N` are observed at the
public interpretation, applying the compiled conceals gives observations
at the abstract interpretation at the same `k`.

`ScopedBodyCompatibility.reveal-observed` and `conceal-observed` prove
these statements mutually with their value-input versions. The induction
is structural on the body; no termination override is needed.

For a reveal at an arrow, the proof follows the whole-term reduction
`(F ↑ (c ↦↑ d)) U —→ (F (U ↓ c)) ↑ d` on both sides. The domain induction
gives the concealed argument computation; `application-observed` supplies
the call; the range induction reveals its result. The conceal proof uses
`(F ↓ (c ↦↓ d)) U —→ (F (U ↑ c)) ↓ d`, reversing the domain induction.
The paired beta prefixes are restored without reducing the outer index.

This includes non-value converted arguments: even an identity conversion
on an unchanged leaf can take a step. It also includes function bodies
that allocate or return closures retaining private names. Those histories
are handled by frame composition, not erased by the structural induction.

### Fresh visible binder

`ScopedFreshBodyCompatibility` specializes the theorem to the environment
created by a paired fresh allocation. Its head conversion exchanges the
fresh nominal meaning with the rebased argument `A`; every old visible
entry uses an unchanged conversion.

If a computation pair is observed in the extended visible body environment,
then applying those reveals gives observations at the rebasing of
`⟦C⟧(α ↦ A, η)` at every index and independent physical future. Conceal
proves the opposite direction. Both use the previous body-rebasing and
environment-extension equivalences; neither assumes that a nominal name
equals its representation. The public theorems now use canonical generators,
as described below, rather than retaining a second compiled-only interface.

The compiler's unchanged-variable case uses an identity conversion on the
assigned endpoint type. Its general theorem does not equate that identity
with structural generation through an arbitrary composite substitution.
The fresh visible environment has the stronger property needed below:
old meanings still have nominal-variable endpoints.

### Higher-order and allocating-argument regressions

`ScopedBodyCompatibilityExperiment` instantiates the body
`(α ⇒ α) ⇒ (α ⇒ α)` with a paired slot storing `ℕ`. Both compiled
conversions agree definitionally with the existing runtime generators
for this fixture. The higher-order identity satisfies both the reveal
and conceal observation theorems at every index.

Applying the revealed higher-order identity to `λx. x` and then `n`
returns `n` in seven steps. The checked trace includes a function conceal,
an argument seal/unseal cancellation, and a result seal/unseal cancellation.
Both endpoints have typing derivations, data-ending traces, and exact
interpreter equations.

The application regression puts the existing allocating universal wrapper
in argument position. It proves observations at the same index between
`(λx. x) n` and `(λx. x) (((Λα. n) ↑ ∀ idℕ)[R])`, using the actual
right-only allocation history through the application frame.

## Canonical fresh-generator alignment

`ScopedFreshBodyCompatibility` now connects those compiled conversions to
the evaluator's actual generators. Let `ηᴵ,ηᴾ` embed the old visible names
in the physical stores. Extend each embedding with a fresh name `α`, and
let `Cᴵ,Cᴾ` be the endpoint spellings of the body under those embeddings.
The new slots store `Aᴵ,Aᴾ`; write `Rᴵ,Rᴾ` for those representations
weakened into the extended stores.

If `C` belongs to the natural/variable/arrow fragment, then its compiled
reveal is `〖 α , R ↑ C 〗` at each endpoint, and its compiled conceal is
`makeConceal α R C`. The proof is structural: the new variable is a
seal/unseal, an old visible variable is an identity, and arrows exchange
the two directions in their domains. Old stored representations may be
composite; the generator still sees their nominal names, not their contents.

If `S` is any physical future scope, then
`scope↑ S 〖 α , R ↑ C 〗 = 〖 scopeVar S α , scopeTy S R ↑ scopeTy S C 〗`,
and analogously for conceal. `ScopedConversionTransport` proves these
syntax laws for every type body, using the existing injective-renaming
lemmas. The body-compatibility theorem itself remains fragment-restricted.

The four `revealᴵ-generated`, `concealᴵ-generated`, `revealᴾ-generated`,
and `concealᴾ-generated` equalities include the intrinsic endpoints and
hold at arbitrary independent future scopes. No allocation is discarded,
and the selected fresh pivot may have moved away from the newest position.

If `M,N` are observed in the freshly extended nominal body environment,
then their canonical reveals are observed at the rebased original body
with argument `A`. `canonical-reveal-observed` proves this at the same
index; `canonical-conceal-observed` proves the reverse conversion. Both
preserve all three observation clauses. At the new roots, the reveal
syntax is exactly the one produced by
`(Λα. V)[A] —→ V ↑ 〖 α , R ↑ C 〗` after allocating `α ↦ A`.

These results identify conversions, not universal values or whole wrapper
applications. In particular, they do not turn a paired nominal meaning
into a right-only nominal interpretation.

### Mixed fresh and old names

`ScopedFreshBodyCompatibilityExperiment` checks `(α ⇒ X) ⇒ (α ⇒ X)`
over the existing environment with an extra private precise allocation.
All four generator equalities are instantiated after one further imprecise
allocation and two precise allocations. Their conclusions explicitly name
the resulting distinct physical pivots and the shifted old natural name.
Both canonical observation theorems are exercised at every index.

The runtime test reveals the higher-order identity, applies it to
`λx. x ↓ seal X ℕ` and then `n`, and unseals the result at `X`. Both
endpoints are typed and return `n` in exactly nine steps. Besides the
fresh argument seal/unseal cancellation, the trace executes the identity
conceal and reveal on the unchanged old name before the final old-name
unseal. No store entry or conversion rule is changed for the test.

## Precise-only nominal slots

`ScopedRightNominal` supplies the asymmetric base case. If `A` is a scoped
semantic type and the precise root contains `Y ↦ Aᴾ`, then
`right-nominal A Y` has endpoints `Aᴵ` and `＇Y`. At physical scopes `S,T`
and index `k`, its value relation is defined by

`U ~ V ↓ seal (scopeVar T Y) (scopeTy T Aᴾ)` if and only if
`U ~[A,S,T,k] V` and `V` is a value.

There is no imprecise name or lookup premise. The constructor proves both
endpoint typings, downward closure, and closure under independent physical
futures. Its rebasing law preserves the same relation while transporting
the precise pivot and representation to the new root.

If `M,N` are observed at `A`, then `M` and
`N ↓ seal (scopeVar T Y) (scopeTy T Aᴾ)` are observed at this right-only
nominal type. If `M,N` are observed at the right-only nominal type, then
`M` and `N ↑ unseal (scopeVar T Y) (scopeTy T Aᴾ)` are observed at `A`.
`ScopedRightSealCompatibility` proves both statements at the same outer
index, preserving forward return, backward return, and forward blame.
The imprecise syntax is literally `M` in both conclusions.

`ScopedRightFrameComposition` composes observations through a precise-only
evaluation frame. It retains the actual operand histories on both sides
and appends only the precise frame's history. In the backward-return proof,
the imprecise continuation starts at an already returned value; value
evaluation and result uniqueness show that this continuation contributes
no new source term or allocation. Seal compatibility uses related values;
unseal compatibility additionally uses same-index precise-step expansion
for the cancellation. Neither theorem assumes evaluation equivariance.

### Allocating, blaming, and higher-order regressions

`ScopedRightSealExperiment` starts with an empty imprecise root and one
precise natural slot. Its precise payload allocates twice before returning
`n`. The enclosing seal moves from pivot `0` to pivot `2`; sealing and
unsealing the payload returns `n` in six steps. The two observation proofs
invoke the new compatibility APIs, while separate typed traces and exact
interpreter equations check the concrete run. The blame regression also
uses both APIs and checks the two-step precise blame propagation.

`ScopedRightSealClosureExperiment` retains the earlier escaped private
precise name and adds a fresh precise-only function slot. The imprecise
closure is not shifted or wrapped. The sealed precise payload is the
shifted non-identity closure, whose argument conversion still uses its
private name. Seal/unseal observations hold at every index and arbitrary
independent future scopes, using the full arrow relation rather than only
one concrete call. The typed fully applied roundtrip returns its captured
`n` in five steps, independently of its argument `m`; the unchanged
imprecise closure returns `n` in two steps.

These results discharge the one-sided nominal base case, not structural
one-sided conversion for whole bodies or the absent-slot universal wrapper.

## Structural precise-only body compatibility

`ScopedRightBodyConversion` lifts the right-only nominal interpretation
through `BodyFragment`. A variable description is either an unchanged
semantic type `A` or a precise slot `Y ↦ Aᴾ`. Its abstract meaning is,
respectively, `A` or `right-nominal A Y`; its public meaning is `A` in
both cases. These descriptions contain store evidence, not compatibility
assumptions.

If `C` is a body in the fragment, write `⟦C⟧abs` and `⟦C⟧pub` for its
interpretations under the abstract and public variable meanings.
Their imprecise endpoints are equal. This equality transports typing of
the unchanged imprecise term; it does not identify the two value relations.

Only precise conversions are compiled. At naturals and unchanged variables
they are identities; at a precise slot they are `unseal Y Aᴾ` and
`seal Y Aᴾ`. If the compiled reveal and conceal for a body `C` are
`rC` and `cC`, then the arrow clauses are
`r(C ⇒ D) = cC ↦↑ rD` and `c(C ⇒ D) = rC ↦↓ cD`.
Both conversions are proved well-typed in the precise root store.

`ScopedRightBodyCompatibility` proves the following two statements at
every physical scope pair `S,T` and every index `k`:

- If `M,N` are observed at `⟦C⟧abs`, then `M` and
  `N ↑ scope↑ T rC` are observed at `⟦C⟧pub`.
- If `M,N` are observed at `⟦C⟧pub`, then `M` and
  `N ↓ scope↓ T cC` are observed at `⟦C⟧abs`.

Both preserve forward return, backward return, and forward blame. No
identity conversion or administrative step is inserted on the imprecise
side. General computation operands use precise-only frame composition,
retaining their independent allocation histories.

For a revealed arrow, related public arguments `U,V` first give observed
abstract arguments `U, V ↓ cC`. Scoped application uses the original
related functions at these arguments. The recursive result theorem then
relates `F · U` to `(G · (V ↓ cC)) ↑ rD`. Precise-only beta expansion
finishes at `(G ↑ (cC ↦↑ rD)) · V`, with `F · U` unchanged. Conceal
exchanges the two directions. The arrow call uses its usual strict index
bound; precise administrative reductions do not decrease the outer
compatibility index. The value-level induction helpers remain private.

### Mixed-name contravariant regression

`ScopedRightBodyCompatibilityExperiment` uses
`C = (α ⇒ X) ⇒ (α ⇒ X)`. The imprecise root has only the old natural
slot `X`; the precise root additionally has the fresh natural slot `α`.
The old name retains its paired nominal meaning. Both body-compatibility
directions are tested with the higher-order identity at arbitrary physical
scopes and indices. The concrete compiled reveal agrees with the canonical
generator for this fixture. A further instantiation uses one imprecise
allocation and two precise allocations, checking the generated reveal with
the precise fresh pivot at `2` and old pivot at `3`.

The imprecise program is the unconverted higher-order identity applied to
`λn. n ↓ seal X ℕ`, then to `n`, followed by `unseal X ℕ`. It returns
`n` in three steps. Its precise counterpart applies the generated reveal
to the higher-order identity and returns `n` in nine steps. The additional
precise reductions exercise arrow conceal, fresh argument seal/unseal,
and identity conversions at the unchanged old name. Both endpoints have
typing derivations, explicit data-ending traces, and exact interpreter
equations.

This closes structural precise-only compatibility for existing slots in
the fragment. It does not yet identify an arbitrary freshly extended
right-only environment with the canonical generator, construct the
required admissible fresh-name argument, or prove universal-wrapper closure.

## Fresh precise-only generation and allocating type application

`ScopedRightFreshBodyCompatibility` now specializes the asymmetric body
theorem to a fresh precise slot. Given an old paired visible environment
`η` and scoped argument interpretation `A`, the new physical roots are
`Σᴵ` and `Σᴾ, α ↦ Aᴾ`. Only the precise root grows.

The fresh body meaning assigns `right-nominal (rebase A) α` to the new
variable and the rerooted old nominal meanings to old variables. This is
a local semantic assignment, not a paired `VisibleEnvironment` extension:
there is no imprecise name or lookup for `α`. The proof identifies the
compiled abstract body with this assignment. It also identifies the public
body with the rebased original body interpretation whose binder denotes
`A`. These are semantic equivalences, preserving both endpoint types and
value membership in both directions.

If `C` is in `BodyFragment`, let `Cᴾ` be its spelling under the old precise
visible-name embedding extended by `α`. The compiled precise reveal is
`〖 α , ⇑ Aᴾ ↑ Cᴾ 〗`, and its conceal is
`makeConceal α (⇑ Aᴾ) Cᴾ`. The general proof handles old variables as
identities and reverses directions in arrow domains. Both equalities hold
under every subsequent precise physical future: the pivot, representation,
and body are transported together. The imprecise future remains independent.

If `M,N` are observed in the fresh abstract body, then `M` and the canonical
reveal of `N` are observed in the rebased public body, at the same index.
Canonical conceal proves the reverse direction. These statements preserve
all three observation clauses and leave `M` literally unchanged.

The operational corollary `instantiate-observed` also incorporates the
actual allocating type-beta step. If `V` is a value and `M,V` are observed
in the fresh abstract body at index `k`, then `M` and `(Λα. V)[Aᴾ]` are
observed in the original public body at index `k`. The proof first performs
canonical reveal compatibility, transfers its observation back to the old
model with the precise allocation retained, and expands the precise
type-beta step. It requires the supplied body observation; it does not
derive a fundamental property for `V` or construct a universal-family
argument.

### Canonical and allocating regressions

`ScopedRightFreshBodyCompatibilityExperiment` instantiates the general
specialization with one old natural name and body
`(α ⇒ X) ⇒ (α ⇒ X)`. Both canonical observation APIs are exercised at
arbitrary independent future scopes. The generated reveal and conceal
are also checked after two further precise allocations, where the fresh
pivot is `2` and the old pivot is `3`. A concrete observation combines
those with one further imprecise allocation. A compiler equality connects
the specialization to the existing three-step/nine-step runtime fixture;
its runtime definitions and traces are reused directly, not re-exported
under wrapper aliases.

`ScopedRightFreshInstantiationExperiment` tests the actual allocating call.
It instantiates `Λα. λf. f`, passes the old-name sealing function, applies
the result to `n`, and unseals at the old name. The precise program first
allocates `α`, then reaches the existing nine-step precise runtime fixture;
it returns `n` in ten steps. The unchanged imprecise program returns `n`
in three steps and does not allocate. The higher-order type application
is observed at every index by applying `instantiate-observed` to the
abstract identity-body observation. Separate typing, explicit reduction,
and exact interpreter proofs check the fully applied data endpoint.

## Body-derived right families and admissible fresh arguments

`ScopedBodyFamily.RightBodyFamily` now derives the right-only family from
the same natural/variable/arrow body interpretation as the paired family.
For a body `C`, old assignment `η`, and fixed imprecise argument `Aᴵ`, the
associated right-universal type has endpoints `C[ηᴵ][Aᴵ]` and `∀α. C[ηᴾ]`.
At physical scopes `S, T`, a code `a` denotes a semantic type with imprecise
endpoint `scopeTy S Aᴵ`;
the result is the interpretation of `C` with `α` assigned that denotation
and old meanings rebased to `S, T`. Endpoint coherence is proved from
substitution and opening, not supplied as a separate result-family axiom.

### Small codes closed under precise-only fresh names

`ScopedRightArguments` fixes one seed semantic type `A` and defines a small
code family. A code is a rebased seed, an independently grown code, or a
fresh precise nominal over an existing code. The source endpoint is always
`scopeTy S (impreciseTy A)`. The precise endpoint of a fresh code is the
new name, whose store entry is the previous precise endpoint. No constructor
contains an arbitrary `ScopedType` record.

For every code `a` at `S, T`, the construction provides a code at
`S, allocate T (preciseTy (denote a))`. Its denotation is equivalent to
the precise-only nominal over the one-step rebase of `denote a`. Thus the
fresh argument needed by a subsequent type application exists within this
small family; it is not an assumption about arbitrary argument families.

If `U` and `V` are related at `denote a`, then `U` and the shifted `V`
sealed at the fresh precise name are related at the fresh code, at the
same index. If the physical scopes grow independently, the lifted values
are related at the corresponding grown code. These facts follow from the
seed's semantic invariants and the proved precise-only nominal constructor.

The scope of this code language is intentionally limited: one seed and its
nominal extensions, with arbitrary independent store growth. It is not a
small encoding of all semantic types or a general interpretation of every
type-imprecision derivation.

### Occurring-binder right identity and nested nominal arguments

`ScopedRightUniversalIdentity` proves, at every index, that the ordinary
identity at the fixed source type is related to `Λα. λx. x` by the derived
right family for `α ⇒ α`. Its instantiation clause quantifies over arbitrary
independent futures and uses the same-index `j ≤ k` boundary. The proof
constructs the abstract identity observation at a fresh right nominal and
uses the canonical allocating type-application theorem; it does not replace
type application with a semantic axiom.

`ScopedRightArgumentExperiment` instantiates this theorem with the natural
seed and two successive fresh codes. In named form, the target store has
`X ↦ ℕ` and `Y ↦ X`, while the source store is empty. The code relates `n`
to `(n ↓ seal X) ↓ seal Y`. The regression checks that this relation survives
independent subsequent allocations and that instantiating the right identity
at `Y` satisfies all three computation-observation clauses at every index.
It also checks the family-result equivalence between a fresh code and the
abstract identity-body interpretation used by canonical body compatibility.

The fully applied target program instantiates `Λα. λx. x` at `Y`, applies
it to the doubly sealed natural, and unseals first `Y`, then `X`. Its typed,
explicit reduction and evaluator witnesses reach `n` in six steps: one
allocation followed by five store-preserving steps. The literal source
endpoint returns `n` without stepping. These tests retain every private
seal; they do not lower returned syntax to the original physical scope.

## Identity universal reveal-wrapper closure

`ScopedRightUniversalWrapper` now proves closure for arbitrary related
values, rather than proving only that a particular identity inhabits a
universal relation. Fix a seed semantic type `A`, the small argument codes
constructed above, and a binder-only natural/variable/arrow body `C`.
If `U` and `V` are related by the body-derived right-universal relation at
`S, T, k`, then `U` and `V ↑ ∀α. id(C)` are related by that same relation
at `S, T, k`. The conversion is scoped at the current precise endpoint.
There is no requirement that `V` be a syntactic type abstraction.

### Fresh instantiation and the actual wrapper step

At an arbitrary pair of future scopes, let `a` be the tested code and
`R` its precise endpoint. Allocate a fresh precise name `X ↦ R`, keeping
the imprecise store unchanged. The original universal relation can be
tested at the constructed fresh code, at the same index `j ≤ k`.
Fresh-argument coherence and body interpretation congruence identify its
result with the abstract body interpretation.

Diagram: the wrapper's actual next step, in named notation.

    (V ↑ ∀α. id(C))[R]
            │
            ▼
    (V[X] ↑ id(C[X/α])) ↑ 〖 X , R ↑ C[X/α] 〗

The universal instantiation clause supplies the observation of `V[X]`.
Computation-level identity compatibility inserts the inner conversion;
this operand may itself allocate, so a value-only identity lemma would
not suffice. Canonical precise-only body compatibility supplies the outer
conversion. Rebase transport interprets the result at its actual extended
physical scope. Same-index right-step expansion then proves the original
wrapper test. The imprecise computation remains unchanged throughout.

All three observation clauses are preserved. Neither the fresh argument
nor conversion compatibility is assumed as a new obligation, and no
evaluation-equivariance theorem is used to erase the allocation.

### Regression coverage

`ScopedRightUniversalWrapperExperiment` applies the closure theorem to the
right identity and then applies it again to the already wrapped value.
It also wraps constant universals, so the input relation is not restricted
to identity functions or to bodies with an occurring binder. Instantiation
after unequal store growth uses the previous nested-nominal argument code:
the source has one physical slot and the target has three.

The fully applied identity regression returns `n` in one source step and
eight target steps. The target allocates two distinct names, eliminates the
intermediate identity conversion, calls both function adapters, and cancels
both seals. Typing, the explicit reduction chain, exact interpreter returns,
and the three computation observations all check.

This closes the identity **reveal** wrapper for the stated body fragment
and code family. It is not yet the general structural universal conversion,
the conceal-wrapper case, or an interpretation of bodies with old variables.

## Identity reveal wrappers over old visible names

`ScopedRightUniversalWrapper.Compatibility` now takes an arbitrary paired
`VisibleEnvironment`, not an empty assignment. Its body may contain old
visible variables as well as the new precise-only binder. Write `C[ρᵀ]`
for capture-avoiding renaming of the old visible names into target scope
`T`, leaving the new parameter `α` bound. If `M` and `V` are related by
the body-derived right-universal family at index `k` and physical scopes
`S,T`, then `M` and `V ↑ ∀↑ id(C[ρᵀ])` are related by the same family
at the same scopes and index. The source term is unchanged.

The extension needs two separate coherence facts. Rebasing a visible
variable's nominal meaning agrees with its meaning in the rebased visible
environment. Rebasing directly into a fresh target allocation also agrees
with rebasing first to the current roots and then allocating there. Both
facts preserve endpoint types and the value relation in both directions;
the wrapper proof uses them under arbitrary future scopes, not only at the
initial empty history.

`ScopedBodyInterpretation.scoped-body-visible` identifies the current body
annotation with the old-name embedding extended by the fresh binder. Thus
the canonical generated reveal is still the evaluator's actual conversion,
including shifted old names. The existing empty-environment identity,
constant, repeated-wrapper, and unequal-growth tests use the generalized
API directly.

`ScopedVisibleUniversalWrapperExperiment` supplies a nonempty-environment
inhabitant: `λf. f` is related to `Λα. λf. f` at
`(ℕ⇒X)⇒(ℕ⇒X)` versus `∀α. (α⇒X′)⇒(α⇒X′)`, with the old paired names
`X,X′` representing naturals. Both single and repeated reveal wrapping
preserve this relation at every index. A further test first allocates one
private source slot and two target slots, wraps at those non-root scopes,
and instantiates at a target nominal argument distinct from `X′`.

The fully applied regression supplies `λx. seal X x`, applies the returned
function to `n`, and unseals the old result name. It returns `n` in three
source steps and eighteen target steps. The target allocates two fresh
names in addition to the old visible name. The exact interpreter-return
theorem exposes its proof-carrying trace as an existential witness, which
the reduction theorem reuses with the explicit allocation history and final
data value. Typing and computation observations check as well.

This is still identity reveal-wrapper closure for the natural/variable/
arrow fragment. It does not prove structural non-identity universal
conversions, conceal wrappers, dynamic bodies, or the live fundamental
property.

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

The fixed-root model now proves downward and independent-physical-future
closure for naturals, arrows, and nominal seals. The allocating maker and
its escaping non-identity closure inhabit the new observation and value
relations. No new counterexample was found in this step. This supports
continuing the same behavioral line, without claiming a full LR model.

General function-seal compatibility now checks for the new observation
and value relations, including all three observation directions. This
closes the local bridge identified in the previous checkpoint. It does
not discharge the live structural reveal cases or the universal wrapper.

Visible-environment extension now checks across independently grown
physical stores. Old meanings, computation observations, and arrow tests
survive rebasing; the private-before-visible regression retains and uses
its escaping seal. No new counterexample was found at this checkpoint.

Paired and right-only family-indexed universal constructors now check,
including the same-index right-only boundary. The occurring-binder identity
inhabits the paired clause for arbitrary supplied small argument families;
constant wrappers exercise the extra allocation under both clauses.

Body-derived paired result families now check for the natural/variable/
arrow fragment, including renaming, substitution, rebasing, and fresh
visible-environment coherence. Same-index expansion through one-sided
allocating steps also checks. No new counterexample was found.

Structural paired seal/unseal compatibility now checks through that
fragment, including contravariant arrow domains and computation operands.
The proof converts between nominal and representation interpretations
operationally; it does not equate them by substitution coherence.

Canonical paired fresh-generator alignment now checks, including arbitrary
independent physical futures and unchanged old nominal names. Precise-only
nominal interpretation and structural same-index seal/unseal compatibility
also check through the body fragment, including contravariant arrow domains,
without inventing an imprecise slot or altering its program.
Fresh precise-only body meanings and canonical generators now agree across
rebasing and independent futures. The same-index allocating type-beta
corollary also checks, given the post-allocation body observation.
Body-derived `RightFamily` endpoints and a concrete small fresh-closed
argument language now check. This boundary concerns one new precise-only
slot over an old paired visible environment, not a general interpretation
of all missing endpoints.
The occurring-binder right identity now inhabits the derived family, and
the nested nominal argument and its data-ending runtime check as well.

Identity universal reveal-wrapper closure now checks for arbitrary related
values, at arbitrary current scopes and without decreasing the right-only
index. Repeated wrapping and constant-body tests exercise the theorem beyond
the original identity inhabitance proof.

The visible-old-environment extension and its rebase coherence now check.
The next critical step is the actual structural body conversion required
by universal reveal, followed by the conceal-wrapper analogue. An arbitrary
semantic assignment does not supply the old-name data required by canonical
generation; use the visible environment established here. These are still
proof-local extensions, not permission to change the live term-imprecision
relation or replace its obligations.

The structural theorem covers the current body fragment, not arbitrary
universal bodies. Dynamic types, nested universal syntax, missing-endpoint
world interpretation, and the full syntax interpretation remain outside
this fragment. Do not integrate the replacement into the live LR before
the general universal-wrapper case checks.

General evaluation equivariance and full scoped universal-wrapper closure
remain open. The bounded audit below refutes the unchanged live
`RevealObligations` package; it must be restated over a replacement
interface, not filled in as it stands. No live obligation has been
discharged by these experiments, and the fundamental property is not yet
complete. `VarImp` and the live LR remain unchanged.

## Historical work estimate (2026-08-30; superseded below)

At the start of this checkpoint (`669d1c15`), the planning estimate
was **5–7 substantial work packages for universal-wrapper/conversion closure**
and **12–18 for the full fundamental property**, including this checkpoint.
After the visible-environment step, that leaves approximately **4–6** and
**11–17**, respectively. These are work packages, not predicted chat turns
or a count of equally difficult lemmas. Some packages may split, and the
dynamic/full-syntax cases still carry mathematical risk.

The wrapper/conversion path is:

- [x] Preserve old visible meanings through the identity reveal wrapper.
- [ ] Generalize to the structural generated body conversion and align its
  statement with the precise reveal obligation.
- [ ] Prove the conceal-wrapper counterpart and its precise obligation
  alignment.
- [ ] Handle dynamic universal reveal and conceal, where replacement changes
  the compared endpoint rather than only introducing an inert wrapper.
- [ ] Extend body interpretation to the needed dynamic and nested universal
  syntax, and interpret the required missing-endpoint worlds.
- [ ] Replace the live observation/value interface and restate its closure
  obligations before integration. Discharging the four *unchanged* fields
  of `RevealObligations` is impossible; see the bounded audit below.

Full fundamental-property work also includes the independently parameterized
`CastValueObligations`, paired and right/smart universal introductions,
source/target and paired reveal/conceal compatibility, the seal-star cases,
nonstructural type applications, and final assembly. The exact outstanding
interface is `RemainingObligations` in
`proof/LR-narrow/FundamentalAssembly.agda`; its fourteen fields are not
fourteen independent next steps, because they share lower-level machinery.

The main uncertainty is whether dynamic types, nested universals, and the
full world interpretation admit the intended closure with the current
invariants. Cast-value compatibility is separate debt and may expose an
independent obstruction. Successful local wrapper experiments do not, by
themselves, resolve those questions.

## Bounded closure audit: the unchanged live endpoint is impossible

The follow-up request imposed two stopping conditions: stop at a roadblock
and construct a counterexample; also stop if closure requires more than six
milestones. The preflight triggered the first condition, before any new
closure milestone was implemented.

`RevealObligationsCounterexample.reveal-obligations-impossible` proves:

`RevealObligations → ⊥`.

The witness is the existing inert-wrapper counterexample, now connected
directly to the exact live obligation package. Let `U = Λα. 7` and let `c`
be the reveal generated at the paired natural name `X` on `∀α. ℕ`.
The slot is absent from the type, and `c = ∀↑ id(ℕ)`. At index six, `U`
is related to itself, but `U` is not related to `U ↑ c`. Instantiating
at the paired names gives `7` on both sides: the bare computation takes
two steps and allocates once; the wrapped computation takes five steps
and allocates twice. The exact final stores cannot inhabit the old raw-store
future relation, as `ScopeExperiment.no-raw-join` proves.

If an obligation package `ob` existed, then `RevealStructural ob` would
provide all smaller-index/size statements. They discharge the `Below`
premise of its precise reveal field at index six and size zero. That field
would preserve the universal relation for the absent-slot wrapper above,
contradicting `ScopeExperiment.inert-universal-reveal-not-closed`. This is
a proof by contradiction from the hypothetical package, not an assumption
that the smaller statements already hold without it.

This does **not** refute the scoped model, and it is not a new operational
counterexample to the dynamic gradual guarantee: both programs return `7`.
The original experiment already identified the raw-store mismatch. The
new result makes the impossibility of the promised unchanged live endpoint
explicit at its actual Agda interface.

The earlier **4–6** closure and **11–17** fundamental-property estimates
are withdrawn. They treated live integration as closing an existing
interface, whereas it requires replacing that interface and re-establishing
its consumers. Paired universal wrapper closure is also distinct from the
right-only wrapper theorem currently proved. The audit does not assert an
artificially precise new milestone count or claim a new impossibility
result for the intended replacement. A revised replacement contract and
dependency audit are needed before a six-milestone completion bound can
be justified. No additional closure or live-relation redesign was started.

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

## Example-driven LR reassessment (2026-08-30)

The current review document is
[LR principles from imprecision examples](LR-PRINCIPLE-REGRESSIONS.md).
It catalogs fifteen new example families, including eight whole-program CTI
pairs, against seventeen earlier regression groups. It distinguishes checked
counterexamples, positive executions, historical proof obstructions, and
unproved cast obligations.

The strongest new contrast is nominal: equal representations do not suffice
for matching projection tags, but unconditional tag matching is too strong.
A checked universal-erasure CTI pair has precise blame and imprecise natural
return. The review therefore separates matched nominal capabilities from
precise-only semantic payloads and retains directional observations.

The note proposes constraints on a future LR, not live changes: independent
physical result scopes, the occupancy-sensitive nominal split, and
conversion-aware producer computations. It does not claim that the complete
redesign passes the outstanding universal/dynamic cast cases. The old
`RevealObligations` impossibility and the withdrawn milestone estimates remain
in force.

The new modules are in the aggregate check. The historical occupied-slot
projection regression was ported from removed source-conceal APIs and is now
also part of `make check`, alongside the ground-cast-target regressions.
