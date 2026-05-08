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

`LawfulSubSpec spec superSpec` extends `SubSpec spec superSpec` with the propositional requirement that **every backward fiber `onResponse t` is a bijection**. This is *exactly* the `PFunctor.Lens.IsCartesian` predicate from `ToMathlib/PFunctor/Lens/Cartesian.lean`:

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

### Probability lemmas (additionally require `[spec ⊂ₒ superSpec] [LawfulSubSpec spec superSpec]` and `Fintype`/`Inhabited` on both specs)

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

`evalDist : OracleComp spec α → PMF α` is *definitionally* (`rfl`) `simulateQ` into `PMF`, with each query interpreted as the uniform distribution over its response type. The `HasEvalPMF` instance at `VCVio/OracleComp/EvalDist.lean:154-156` reads:

```lean
noncomputable instance : HasEvalPMF (OracleComp spec) where
  toPMF := simulateQ' fun t => PMF.uniformOfFintype (spec.Range t)
```

(requires `[spec.Fintype] [spec.Inhabited]`). `support : OracleComp spec α → Set α` has the same shape but target `SetM` with `impl _ := Set.univ`. Both are instances of the same universal fold, not separate primitives.

Distinct from the `PMF`-target `evalDist`, there is also a *syntactic* uniform-sampling handler that rewrites queries into `ProbComp` (i.e. target `OracleComp unifSpec`, not `PMF`):

```lean
def uniformSampleImpl [∀ i, SampleableType (spec.Range i)] :
    QueryImpl spec ProbComp := fun t => $ᵗ spec.Range t
```

Preservation of `evalDist` through `uniformSampleImpl` is a **lemma**, not definitional: `uniformSampleImpl.evalDist_simulateQ : evalDist (simulateQ uniformSampleImpl oa) = evalDist oa` (`VCVio/OracleComp/Constructions/SampleableType.lean:517-523`). Companion lemmas `probOutput_simulateQ`, `probEvent_simulateQ`, `support_simulateQ`, `finSupport_simulateQ` live in the same namespace and are what you reach for when you want to stay inside `ProbComp` rather than drop to `PMF`.

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
