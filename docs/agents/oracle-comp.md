# OracleComp, SubSpec, and SimSemantics

## OracleSpec

An oracle specification maps index types to response types:

```lean
def OracleSpec (ι : Type u) : Type _ := ι → Type v
```

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
| `query t` | Single oracle query (returns `OracleQuery spec (spec.Range t)`) |
| `liftM (query t)` | Lift query to `OracleComp` (needed for `evalDist`) |
| `OracleComp.inductionOn` | Induction: `pure` case + `query_bind` case |
| `OracleComp.construct` | Same but result is `Type*` (not `Prop`) |
| `isPure` | Check if computation is `pure` (no queries) |
| `totalQueries` | Count total oracle queries |

### Key lemmas

| Lemma | Use |
|-------|-----|
| `bind_eq_pure_iff` | `oa >>= ob = pure y ↔ ∃ x, oa = pure x ∧ ob x = pure y` |
| `pure_ne_query` | `pure x ≠ query t >>= f` |

### Gotcha: `query t` is `OracleQuery`, not `OracleComp`

`query t : OracleQuery spec _`, not `OracleComp spec _`. To use `evalDist` on a bare query, write `evalDist (liftM (query t) : OracleComp spec _)`.

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
class SubSpec (spec : OracleSpec ι) (superSpec : OracleSpec τ)
    extends MonadLift (OracleQuery spec) (OracleQuery superSpec)
```

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

### evalDist IS simulateQ

`evalDist` is literally `simulateQ` with uniform distributions as the oracle implementation. This is definitional (`rfl`). The implementation is `uniformSampleImpl`:

```lean
def uniformSampleImpl [∀ i, SampleableType (spec.Range i)] :
    QueryImpl spec ProbComp := fun t => $ᵗ spec.Range t
```

Key simp lemmas: `evalDist_simulateQ`, `probOutput_simulateQ`, `probEvent_simulateQ` (all with `uniformSampleImpl`).

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
