# Probability Reasoning (EvalDist and ProbComp)

## Core Definitions

| Definition | Type | Notation | Defined in |
|-----------|------|----------|------------|
| `evalDist mx` | `SPMF α` | — | `EvalDist/Defs/Basic.lean` |
| `probOutput mx x` | `ℝ≥0∞` | `Pr[= x \| mx]` | `EvalDist/Defs/Basic.lean` |
| `probEvent mx p` | `ℝ≥0∞` | `Pr[p \| mx]` | `EvalDist/Defs/Basic.lean` |
| `probFailure mx` | `ℝ≥0∞` | `Pr[⊥ \| mx]` | `EvalDist/Defs/Basic.lean` |
| `support mx` | `Set α` | — | `EvalDist/Defs/Support.lean` |
| `finSupport mx` | `Finset α` | — | `EvalDist/Defs/Support.lean` |

## ProbComp and Sampling

`ProbComp α = OracleComp unifSpec α` — computations with only uniform sampling.

### Sampling notations

| Notation | Function | Type | Requirement |
|----------|----------|------|-------------|
| `$ᵗ T` | `uniformSample` | `ProbComp T` | `[SampleableType T]` |
| `$[0..n]` | `uniformFin n` | `ProbComp (Fin (n + 1))` | — |
| `$[n⋯m]` | `uniformRange n m` | `ProbComp (Fin (m + 1))` | `n < m` |
| `$ xs` | `uniformSelect` | `OptionT ProbComp β` | `[HasUniformSelect cont β]` |
| `$! xs` | `uniformSelect!` | `ProbComp β` | `[HasUniformSelect! cont β]` |

### SampleableType instances

Available for: `Bool`, `Fin n` (for `[NeZero n]`), `ZMod n`, `BitVec n`, `α × β` (from components), `Vector α n`, `Fin n → α`, `Matrix`.

### HasUniformSelect instances

- `$ xs` works for `List`, `Finset`, `Array` (can fail with `none` on empty)
- `$! xs` works for `Vector α (n+1)`, `List.Vector α (n+1)` (guaranteed non-empty)

## Simp Lemma Catalog

### Pure

| Lemma | Statement |
|-------|-----------|
| `evalDist_pure` | `evalDist (pure x : m α) = pure x` |
| `probOutput_pure` | `Pr[= x \| pure y] = if x = y then 1 else 0` |
| `probOutput_pure_self` | `Pr[= x \| pure x] = 1` |
| `probEvent_pure` | `Pr[p \| pure x] = if p x then 1 else 0` |
| `probFailure_pure` | `Pr[⊥ \| pure x] = 0` |
| `support_pure` | `support (pure x) = {x}` |

### Bind

| Lemma | Statement |
|-------|-----------|
| `evalDist_bind` | `evalDist (mx >>= my) = evalDist mx >>= fun x => evalDist (my x)` |
| `probOutput_bind_eq_tsum` | `Pr[= y \| mx >>= my] = ∑' x, Pr[= x \| mx] * Pr[= y \| my x]` |
| `probEvent_bind_eq_tsum` | `Pr[q \| mx >>= my] = ∑' x, Pr[= x \| mx] * Pr[q \| my x]` |
| `probFailure_bind_eq_add_tsum` | `Pr[⊥ \| mx >>= my] = Pr[⊥ \| mx] + ∑' x, Pr[= x \| mx] * Pr[⊥ \| my x]` |
| `support_bind` | `support (mx >>= my) = ⋃ x ∈ support mx, support (my x)` |
| `finSupport_bind` | `finSupport (mx >>= my) = (finSupport mx).biUnion (fun x => finSupport (my x))` |

### Bind (constant continuation)

| Lemma | Statement |
|-------|-----------|
| `probOutput_bind_const` | `Pr[= y \| mx >>= fun _ => my] = (1 - Pr[⊥ \| mx]) * Pr[= y \| my]` |
| `probEvent_bind_const` | `Pr[p \| mx >>= fun _ => my] = (1 - Pr[⊥ \| mx]) * Pr[p \| my]` |

### Map

| Lemma | Statement |
|-------|-----------|
| `evalDist_map` | `evalDist (f <$> mx) = f <$> evalDist mx` |
| `probEvent_map` | `Pr[q \| f <$> mx] = Pr[q ∘ f \| mx]` |
| `probFailure_map` | `Pr[⊥ \| f <$> mx] = Pr[⊥ \| mx]` |
| `support_map` | `support (f <$> mx) = f '' support mx` |
| `probOutput_map_injective` | `f.Injective → Pr[= f x \| f <$> mx] = Pr[= x \| mx]` |

### Bind swapping

| Lemma | Use |
|-------|-----|
| `probEvent_bind_bind_swap` | Swap two independent binds (used internally by `qvcgen_step` probability-equality rewrites) |
| `probOutput_bind_congr` | Congruence: equal on support → equal probability |
| `probEvent_bind_congr` | Same for events |

### Zero / membership

| Lemma | Use |
|-------|-----|
| `probOutput_eq_zero_of_not_mem_support` | `x ∉ support mx → Pr[= x \| mx] = 0` |
| `probOutput_bind_eq_tsum_subtype` | Restrict tsum to `support mx` |
| `probOutput_bind_eq_sum_finSupport` | Finite sum over `finSupport` |

## Decision Tree: Which Lemma Do I Reach For?

1. **Goal is `Pr[= y | mx >>= my] = ...`?**
   → Start with `probOutput_bind_eq_tsum`

2. **Goal is `Pr[p | mx >>= my] = ...`?**
   → Start with `probEvent_bind_eq_tsum`

3. **Need to swap two binds?**
   → Use `qvcgen_step` if the swap should close the equality
   → Use `qvcgen_step rw` / `qvcgen_step rw under n` if you need an explicit rewrite step

4. **Need `Pr[= y | f <$> mx]`?**
   → If `f` is injective: `probOutput_map_injective`
   → Otherwise: `probOutput_map_eq_tsum_subtype` or `probOutput_map_eq_sum_finSupport_ite`

5. **Need to restrict a sum to support?**
   → `probOutput_bind_eq_tsum_subtype` or `probOutput_bind_eq_sum_finSupport`

6. **Continuation doesn't depend on result?**
   → `probOutput_bind_const` / `probEvent_bind_const`

7. **Two computations have same distribution?**
   → Show `evalDist oa = evalDist ob`, or use `relTriple_eqRel_of_evalDist_eq`

## Common Mistakes

1. **Missing `[spec.Fintype]` and `[spec.Inhabited]`**: required for all `evalDist`/`probOutput`/`Pr[...]` usage. Check this first when debugging typeclass failures.

2. **Using `support` when `finSupport` is needed**: `probOutput_bind_eq_sum_finSupport` requires `[DecidableEq α]` and `[HasEvalFinset m]`.

3. **Forgetting `probOutput_eq_zero_of_not_mem_support`**: useful when restricting sums.

4. **`evalDist` on bare `query t`**: fails because `query t : OracleQuery`, not `OracleComp`. Use `liftM (query t)`.
