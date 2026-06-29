# OracleComp, SubSpec, and SimSemantics

## OracleSpec

An oracle specification maps index types to response types:

```lean
def OracleSpec (ι : Type u) : Type _ := ι → Type v
```

Concretely, `spec t` is the response type at query index `t : ι`. `OracleSpec ι` is the `B`-component of a polynomial functor with position type `A := ι`; `spec.toPFunctor` packages the two together, and `OracleSpec.ofPFunctor` is its inverse (both `rfl`-invertible). This is the connection that makes `OracleComp` a free monad: see [`OracleComp`](#oraclecomp) below.

| Constructor | Notation | Example |
|-------------|----------|---------|
| Singleton spec | `A →ₒ B` | `Bool →ₒ Fin 6` |
| Empty spec | `[]ₒ` | No oracles |
| Combined specs | `spec₁ + spec₂` | `unifSpec + (M →ₒ C)` |

Required typeclass instances for probability reasoning:

- `[spec.Fintype]` — all response types are `Fintype`
- `[spec.Inhabited]` — all response types are `Inhabited`

Without both, `evalDist`, `probOutput`, and `Pr[...]` will fail with confusing typeclass errors.

## OracleComp

Computations with oracle access, defined as a free monad:

```lean
def OracleComp {ι : Type u} (spec : OracleSpec.{u,v} ι) : Type w → Type _ :=
  PFunctor.FreeM spec.toPFunctor
```

### Key API

| Function | Purpose |
|----------|---------|
| `query t` | Issue an oracle query in the ambient monad (resolves to `HasQuery.query`) |
| `spec.query t` | Primitive single-query syntax (returns `OracleQuery spec (spec.Range t)`) |
| `OracleSpec.query t` | Same as `spec.query t` (the `protected` definition's full name) |
| `OracleComp.inductionOn` | Induction: `pure` case + `query_bind` case |
| `OracleComp.construct` | Same but result is `Type*` (not `Prop`) |
| `isPure` | Check if computation is `pure` (no queries) |
| `totalQueries` | Count total oracle queries |

### Key lemmas

| Lemma | Use |
|-------|-----|
| `bind_eq_pure_iff` | `oa >>= ob = pure y ↔ ∃ x, oa = pure x ∧ ob x = pure y` |
| `pure_ne_query` | `pure x ≠ query t >>= f` |

### `query` resolution: `HasQuery.query` (monadic) vs `spec.query` (primitive)

The bare identifier `query` is the `export`ed `HasQuery.query`, so `query t : OracleComp spec _` (or any `m` with `HasQuery spec m`) returns the result in the ambient monad and supports `evalDist (query t : OracleComp spec _)` directly. Use `spec.query t` (or `OracleSpec.query t`) when you need the primitive single-query syntax `OracleQuery spec _` for `liftM`, `OracleQuery.cont`, structural induction, etc. The `OracleSpec.query` definition is `protected`; the dot-notation form `spec.query t` works regardless.

### Elimination pattern

Prefer `OracleComp.inductionOn` over pattern matching on `PFunctor.FreeM.pure`/`roll`:

```lean
induction oa using OracleComp.inductionOn with
| pure x => ...
| query_bind t oa ih => ...
```

## SubSpec (⊂ₒ)

`spec ⊂ₒ superSpec` means every query in `spec` can be simulated in `superSpec` without changing the distribution.

```lean
class SubSpec (spec : OracleSpec.{u, w} ι) (superSpec : OracleSpec.{v, w} τ)
    extends MonadLift (OracleQuery spec) (OracleQuery superSpec) where
  onQuery    : spec.Domain → superSpec.Domain
  onResponse : (t : spec.Domain) → superSpec.Range (onQuery t) → spec.Range t
  liftM_eq_lift :
    ∀ {β} (q : OracleQuery spec β),
      monadLift q = ⟨onQuery q.input, q.cont ∘ onResponse q.input⟩ := by intros; rfl
```

### Lens semantics

`onQuery` and `onResponse` together package a `PFunctor.Lens spec.toPFunctor superSpec.toPFunctor` (call it `h.toLens`):

| Class field | Lens field |
|-------------|------------|
| `onQuery : spec.Domain → superSpec.Domain` | `toFunA : P.A → Q.A` |
| `onResponse t : superSpec.Range (onQuery t) → spec.Range t` | `toFunB t : Q.B (toFunA t) → P.B t` |

By the Yoneda lemma for polynomial functors this lens data is in bijection with natural transformations `OracleQuery spec ⟹ OracleQuery superSpec`. The `MonadLift` parent records that natural transformation; the `liftM_eq_lift` field is the propositional coherence axiom forcing it to agree with the lens. Concrete `SubSpec` instances spell `monadLift` out *by hand* (rather than letting it default from the lens data), so that the lifted query reduces fully under `isDefEq` — this is what makes pattern-matching simp lemmas like `probEvent_liftComp` actually fire.

`SubSpec.toLens` exposes the underlying lens; `SubSpec.trans` is composition of these lenses; `MonadLiftT.refl` covers the identity.

#### Why `SubSpec` extends `MonadLift` rather than `PFunctor.Lens`

The fields *are* a lens. We extend `MonadLift` for two pragmatic reasons:

1. **Typeclass synthesis.** Lifting `OracleComp spec α → OracleComp superSpec α` is plumbed through the `MonadLift` / `MonadLiftT` mechanism; bridging through `PFunctor.Lens` separately would require an instance of the form `PFunctor.Lens A B → MonadLift (Obj A) (Obj B)`, which Lean cannot synthesize from `OracleQuery spec` because `OracleQuery` is a `def` (and `def`-headed instance heads cannot be matched).
2. **Reducibility under `rw` / `simp`.** A defaulted `monadLift` field becomes opaque to `isDefEq` during pattern matching. Hand-written `monadLift` per instance keeps the lifted query fully reducible.

### LawfulSubSpec ↔ cartesian lens

`LawfulSubSpec spec superSpec` extends `SubSpec spec superSpec` with the propositional requirement that **every backward fiber `onResponse t` is a bijection**. This is *exactly* the `PFunctor.Lens.IsCartesian` predicate from `PolyFun.PFunctor.Lens.Cartesian`:

```lean
def Lens.IsCartesian (l : Lens P Q) : Prop := ∀ a, Function.Bijective (l.toFunB a)
```

The bridge lemma `LawfulSubSpec.toLens_isCartesian` is the one-line statement that the underlying lens of a `LawfulSubSpec` is cartesian.

A *cartesian* lens is a fiberwise isomorphism over an arbitrary forward map on positions. This is **strictly weaker** than `PFunctor.Lens.Equiv` (an isomorphism in the lens category), which would *also* require `onQuery` to be a bijection. We intentionally only require fiberwise bijectivity because the basic `SubSpec` instances embed a small spec into a larger one (e.g. `spec₁ ⊂ₒ (spec₁ + spec₂)` with `onQuery = Sum.inl`); these embeddings are essential and would be ruled out by `Equiv`.

Cartesianness is the precise condition needed to push uniform distributions through the lift: `LawfulSubSpec.evalDist_liftM_query` shows that pulling the uniform distribution on `superSpec.Range (onQuery t)` back through `onResponse t` recovers the uniform distribution on `spec.Range t`.

### When you need SubSpec

When lifting `OracleComp spec α` to `OracleComp superSpec α` (e.g., a sub-computation uses fewer oracles than the enclosing computation).

### Structural lemmas (require `[MonadLift (OracleQuery spec) (OracleQuery superSpec)]`)

| Lemma | Signature |
|-------|-----------|
| `liftComp_pure` | `liftComp (pure x) superSpec = pure x` |
| `liftComp_bind` | `liftComp (mx >>= my) superSpec = liftComp mx superSpec >>= ...` |

### Probability lemmas (additionally require `[spec ⊂ₒ superSpec] [LawfulSubSpec spec superSpec]` and uniform probability specs on both specs)

| Lemma | Signature |
|-------|-----------|
| `evalDist_liftComp` | `evalDist (liftComp mx superSpec) = evalDist mx` |
| `probOutput_liftComp` | `Pr[= x \| liftComp mx superSpec] = Pr[= x \| mx]` |
| `probEvent_liftComp` | `Pr[p \| liftComp mx superSpec] = Pr[p \| mx]` |

## QueryImpl and simulateQ

### QueryImpl

Maps each oracle input to a monadic response:

```lean
@[reducible] def QueryImpl (spec : OracleSpec ι) (m : Type u → Type v) :=
  (x : spec.Domain) → m (spec.Range x)
```

Constructors:

| Constructor | Use |
|-------------|-----|
| `QueryImpl.id spec` | Identity (returns queries unchanged) |
| `QueryImpl.id' spec` | Identity lifted to `OracleComp` |
| `QueryImpl.ofLift spec m` | From `MonadLift` instance |
| `QueryImpl.ofFn f` | From pure function `f : (t : Domain) → Range t` |
| `impl.liftTarget n` | Lift impl from `m` to `n` via `MonadLiftT` |

### simulateQ

Substitutes every `query t` in a computation with `impl t`:

```lean
def simulateQ [Monad r] (impl : QueryImpl spec r) (mx : OracleComp spec α) : r α
```

**Universal property.** `simulateQ impl` is the *unique* monad morphism `OracleComp spec →ᵐ r` that agrees with `impl` on queries. Internally it is `PFunctor.FreeM.mapM impl`, i.e. the fold of the free-monad syntax tree into `r`. Every way of "running" an `OracleComp` factors through `simulateQ`; there is no other primitive interpreter.

**Handler vs denotation.** The target monad `r` determines how `simulateQ impl` reads:

- `r` effectful (`StateT`, `WriterT`, `OptionT`, another `OracleComp`, `IO`, …) — `simulateQ impl` is an **effect handler**: caching, logging, query counting, lazy sampling, simulating a hash oracle, embedding one game in a richer oracle context.
- `r` semantic (`PMF`, `SPMF`, `Set`, `Finset`) — `simulateQ impl` is a **denotation**. `evalDist` and `support` are both `simulateQ` into a semantic monad (see [evalDist IS simulateQ](#evaldist-is-simulateq) below).

So "operational vs denotational" is not a primitive split; both are `simulateQ` parameterized by the target monad.

### Key lemmas (all `@[simp, grind =]`)

| Lemma | Statement |
|-------|-----------|
| `simulateQ_pure` | `simulateQ impl (pure x) = pure x` |
| `simulateQ_bind` | `simulateQ impl (mx >>= my) = simulateQ impl mx >>= fun x => simulateQ impl (my x)` |
| `simulateQ_query` | `simulateQ impl (liftM q) = q.cont <$> (impl q.input)` |
| `simulateQ_map` | `simulateQ impl (f <$> mx) = f <$> simulateQ impl mx` |
| `simulateQ_id'` | `simulateQ (QueryImpl.id' spec) mx = mx` |

### QueryImpl composition

```lean
def compose (so' : QueryImpl spec' m) (so : QueryImpl spec (OracleComp spec')) :
    QueryImpl spec m

infixl : 65 " ∘ₛ " => QueryImpl.compose
```

Key lemma: `simulateQ (so' ∘ₛ so) oa = simulateQ so' (simulateQ so oa)`

### Wrapping a QueryImpl with a per-query side effect (`preInsert` / `postInsert`)

**Prefer these combinators (or their downstream wrappers) over hand-rolling a new `QueryImpl`** whenever the wrapper has the shape "for each query, run a side effect and then delegate to a base implementation". They are defined in `VCVio/OracleComp/SimSemantics/QueryImpl/Constructions.lean`:

```lean
def preInsert  (so : QueryImpl spec m) (nx : spec.Domain → n α) :
    QueryImpl spec n
def postInsert (so : QueryImpl spec m) (nx : (t : spec.Domain) → spec.Range t → n α) :
    QueryImpl spec n
```

| | `preInsert` | `postInsert` |
|---|---|---|
| Side effect runs | **before** the handler | **after** the handler |
| Sees the response? | No | Yes (the response is passed to `nx`) |
| If the handler fails | Side effect still happens | Side effect skipped |

Both come with a complete generic theory: induction principles (`simulateQ_preInsert.induct` / `simulateQ_postInsert.induct`), projection / strip lemmas (`proj_simulateQ_preInsert`, `proj_simulateQ_postInsert`), and bridge lemmas for `probFailure`, `NeverFail`, `evalDist`, `probOutput`, `support`, `finSupport`, plus `IsTotalQueryBound` / `IsQueryBoundP` transfer in `QueryBound.lean`. Defining a wrapper via `preInsert` / `postInsert` makes all of this theory available immediately and avoids re-proving instance-specific lemmas.

#### Already in the repo (use these directly when applicable)

| Wrapper | File | Built on |
|---|---|---|
| `withTraceBefore` (response-independent monoid trace) | `QueryTracking/Tracing.lean` | `preInsert` |
| `withTrace` (response-dependent monoid trace) | `QueryTracking/Tracing.lean` | `postInsert` |
| `withTraceAppendBefore` / `withTraceAppend` (`Append`-flavoured) | `QueryTracking/Tracing.lean` | `preInsert` / `postInsert` |
| `withCost`, `withCounting` | `QueryTracking/CountingOracle.lean` | `withTraceBefore` |
| `withAddCost`, `withUnitCost` | `QueryTracking/WriterCost.lean` | `withCost` |
| `withLogging` | `QueryTracking/LoggingOracle.lean` | `withTraceAppend` |
| `appendInputLog` (StateT input log) | `QueryTracking/LoggingOracle.lean` | `preInsert` |

If a new wrapper looks like one of these, add it as a small specialization rather than starting from `fun t => ...` from scratch.

#### When `preInsert` / `postInsert` is *not* the right shape

The combinators assume the underlying handler **always runs**. They are not the right tool when the wrapper's control flow is conditional on external state or on the would-be response — for instance:

- **Cache-on-hit logic** (`withCaching` in `CachingOracle.lean`): a cache hit replaces the query body entirely.
- **Fallback-style seeding** (`withPregen` in `SeededOracle.lean`): consumes a pre-generated value when available, otherwise queries.
- **Budget gating** (`enforceOracle` in `Enforcement.lean`): if the budget is exhausted, returns `default` and skips the handler.
- **Game-state handlers** that branch on session state, gating flags, or bad-event flags.

These are genuinely custom and stay as hand-written `QueryImpl` definitions. If you find yourself reaching for `preInsert` / `postInsert` and discovering that you need to inspect external state to decide *whether* to query, you are in this category — write the impl directly.

### evalDist IS simulateQ

For `OracleComp`, `support` is always available and is *definitionally* `simulateQ` into `SetM`, with each query interpreted by `Set.univ`.

`evalDist : OracleComp spec α → SPMF α` is available under `[IsProbabilitySpec spec]` and is *definitionally* (`rfl`) `simulateQ` into `PMF`, then lifted to `SPMF`, with each query interpreted by `IsProbabilitySpec.toPMF`:

```lean
noncomputable instance instMonadLiftTPMF [IsProbabilitySpec spec] :
    MonadLiftT (OracleComp spec) PMF where
  monadLift mx := simulateQ IsProbabilitySpec.toPMF mx
```

Uniform response semantics are supplied by `[IsUniformSpec spec]`, which bundles `[spec.Fintype]`, `[spec.Inhabited]`, `[IsProbabilitySpec spec]`, and a proof that `toPMF` is `PMF.uniformOfFintype`. The bridge from `support` to `SPMF.support 𝒟[...]` is `EvalDistCompatible (OracleComp spec)` and also requires `[IsUniformSpec spec]`.

Distinct from the `PMF`-target `evalDist`, there is also a *syntactic* uniform-sampling handler that rewrites queries into `ProbComp` (i.e. target `OracleComp unifSpec`, not `PMF`):

```lean
def uniformSampleImpl [∀ i, SampleableType (spec.Range i)] :
    QueryImpl spec ProbComp := fun t => $ᵗ spec.Range t
```

Preservation of `evalDist` through `uniformSampleImpl` is a **lemma**, not definitional: `uniformSampleImpl.evalDist_simulateQ : evalDist (simulateQ uniformSampleImpl oa) = evalDist oa` (`VCVio/OracleComp/Constructions/SampleableType.lean:517-523`). Companion lemmas `probOutput_simulateQ`, `probEvent_simulateQ`, `support_simulateQ`, `finSupport_simulateQ` live in the same namespace and are what you reach for when you want to stay inside `ProbComp` rather than drop to `PMF`.

## Oracle strategies (the coalgebra dual)

`VCVio/OracleComp/Coinductive/DynSystem.lean` develops the dual view of `OracleComp`. `OracleComp spec`
is the *inductive* free monad on `spec.toPFunctor` — a program that **asks** queries. A stateful,
adaptive querier is the *coalgebraic* dual: a PolyFun dynamical system over the same polynomial functor
(Niu–Spivak, *Polynomial Functors*, Ch. 4).

- `OracleStrategy spec := PFunctor.DynSystem spec.toPFunctor` — `expose : State → ι` chooses the next
  query, `update : State → spec.Range _ → State` digests the answer. The whole `PFunctor.DynSystem` /
  `PFunctor.Lens` combinator library applies directly (it is an `abbrev`).
- `OracleHandler spec := PFunctor.Section spec.toPFunctor` — a deterministic oracle as a PolyFun
  **section** (a lens `spec.toPFunctor ⟹ X`). Build one with `OracleHandler.ofFn`, apply it as a
  function via its `DFunLike` coercion (`h t : spec.Range t`), and recover the underlying
  `QueryImpl spec Id` via `OracleHandler.toQueryImpl` / the `Coe` (so a handler drops straight into the
  deterministic-handler API, e.g. `evalWithAnswerFn h oa`). Being the section lens, it is exactly what
  closes a strategy: `OracleStrategy.runAgainst h A := PFunctor.DynSystem.wrap h A`.
- `OracleStrategy.{stateAfter, queryStream, answerStream, transcript}` read off the closed-loop run; the
  cofree behaviour tree is `PFunctor.DynSystem.trajectory` with spine `next_iterate_trajectory`.
- Combinators: `reduce` (a reduction is `wrap` along `SubSpec.toLens`; `reduce_trans` is free from
  `wrap_comp`), `pair` (shared-state product oracle `*` via `pairing`), `juxtapose` (parallel `⊗`).
- Randomized handler `ProbHandler spec := QueryImpl spec SPMF` turns the closed loop into a Markov chain
  on states (`kleisliStep`/`kleisliIterate`/`transcriptDist`); the deterministic run embeds as the Dirac
  special case (`ProbHandler.ofHandler`, `transcriptDist_ofHandler`).

The **headline correspondence** reads a program back as its own state machine and shows the dynamical
iterate *computes* `simulateQ`:

```lean
theorem iterate_advance_eq_simulate (h : OracleHandler spec) (oa : OracleComp spec α) :
    (advance h)^[stepsToHalt h oa] oa = pure (evalWithAnswerFn (QueryImpl.ofFn h) oa)
```

with `OracleComp.evalSystem` packaging the same thing as a `PFunctor.Closed`, and the probabilistic
`simulateQ_eq_advanceK_bind` exhibiting `simulateQ` as one coalgebraic Kleisli step. The new transcript
is not a new notion: `run_simulateQ_ofFn_withLogging` proves it equals the existing
`QueryImpl.withLogging` output, and the operational query bounds become denotational bounds on the
transcript: `transcript_length_le_of_isTotalQueryBound` (total), `transcript_countQ_le_of_isQueryBoundP`
(per predicate), and `transcript_countQ_le_of_isPerIndexQueryBound` (per oracle index, via
`QueryLog.countQ`).

The flat transcript is the *answer-erasure of a typed one*: since `OracleComp spec` is
`PFunctor.FreeM spec.toPFunctor`, a `PFunctor.FreeM.Path` is a typed root-to-leaf branch choice
(a sequence of typed answers). `handlerPath` builds the handler-induced path; its leaf is the run
value (`output_handlerPath`) and its erasure is the flat log (`logOfPath_handlerPath`). The
lens-relative form `outputAlong_runAlong` runs a program *along a reduction lens* (`PFunctor.FreeM.PathAlong`
of `SubSpec.toLens`) answered by a super-spec handler, recovering the pulled-back handler's value —
the denotational content of "a reduction is a lens". Worked examples: `Examples/DynamicalSystems/Basic.lean`.

### Logs and counts are PFunctor traces

`VCVio/OracleComp/QueryTracking/Trace.lean` formalizes that the query-tracking carriers *are* the
generic `PolyFun.PFunctor.Trace` types (the identification is latent in the defs — these are `rfl`).
`QueryLog spec = PFunctor.TraceList spec.toPFunctor` (the free monoid on query events
`PFunctor.Idx spec.toPFunctor`): the empty log is `1`, a single entry is `FreeMonoid.of`, and
`withLogging`'s instrumentation is `FreeMonoid.of` (`withLogging_traceFn_eq_of`). `QueryCount ι =
Control.Trace ℕ ι` — but with the bespoke *additive* monoid, **not** `Control.Trace`'s default
multiplicative `Pi.monoid` (do not infer the monoid through the equality). Every monoid-valued readout
of a run factors through the log by the free-monoid universal property `FreeMonoid.lift φ`, and the
coalgebraic `OracleComp.transcript` is such a word (`lift_transcript_pure`/`lift_transcript_queryBind`).

## Enforcement Oracle

Defined in `VCVio/OracleComp/QueryTracking/Enforcement.lean`. Wraps an oracle with a
per-index query budget tracked via `StateT`. Queries exceeding the budget return `default`.

```lean
def enforceOracle [DecidableEq ι] [spec.Inhabited] :
    QueryImpl spec (StateT (ι → ℕ) (OracleComp spec))
```

Key result: `enforceOracle.fst_map_run_simulateQ` — if a computation satisfies
`IsPerIndexQueryBound oa qb`, then running under enforcement with budget `qb` produces
the same output distribution as running without enforcement.

Requires `[DecidableEq ι]` and `[spec.Inhabited]` (for `default` values).

## Patterns

### Wiring oracle implementations (stateful)

For stateful oracle simulations, use `StateT`:

```lean
def myImpl : QueryImpl spec (StateT MyState ProbComp) := fun t => do
  let st ← get
  -- process query using state
  set newState
  return response
```

Then run with `(simulateQ myImpl computation).run initialState`.
