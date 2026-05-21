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

## Lift framework (the EvalDist hypotheses)

Every `evalDist`/`probOutput`/`probFailure`/`support` definition is a thin wrapper around a monad
lift. They each have their own typeclass; assume the minimum your lemma actually uses:

| Hypothesis | Provides |
|------------|----------|
| `[MonadLiftT m SPMF]` | `evalDist`, `probOutput`, `probEvent`, `probFailure` (the `Pr[…]` notations) |
| `[MonadLiftT m SetM] [LawfulMonadLiftT m SetM]` | `support`, all support-membership reasoning |
| `[EvalDistCompatible m]` | the **proposition** that `support` and `Pr[= x]` agree on reachable outputs (needed for lemmas that bridge the two, e.g. `probOutput_eq_zero_iff'`) |
| `[HasEvalFinset m]` | `finSupport`, plus any finite-sum form (`probOutput_bind_eq_sum_finSupport`) |
| `[HasEvalSet.LawfulFailure m]` | `support (failure : m α) = ∅` when `m` is `AlternativeMonad` |

The legacy data typeclasses `HasEvalSet`/`HasEvalPMF`/`HasEvalSPMF` are gone; only the namespaces
`HasEvalSet.Decidable` and `HasEvalSet.LawfulFailure` survive (as sub-typeclasses), and the data
class `HasEvalFinset` survives as the way to declare a finite version of the support. The lift
classes (`MonadLiftT m {SetM, SPMF, PMF}`) carry the actual semantics; `EvalDistCompatible` is the
coherence witness.

For `OracleComp spec`, the canonical lifts are derived from `[spec.Fintype]` and `[spec.Inhabited]`
— having those two in scope is enough to use any of `Pr[…]`, `support`, `finSupport` (the latter
also needs `[DecidableEq α]` on the result type). `Examples/OneTimePad/Basic.lean` is the canonical
reference.

### Where to put the hypotheses (inline vs. section vs. omit)

Three patterns appear in the codebase:

1. **Inline on each lemma** — best when the file has a handful of lemmas and most types mention
   `support` or `Pr[…]`. Each lemma's signature documents exactly what it needs. See
   `Examples/CommitmentScheme/Binding.lean` for a fully-migrated example.
2. **Section `variable` block** — best when *all* declarations in the file need the same
   hypotheses (typical of cryptographic algebra files). Less repetition, but the linter will warn
   about lemmas whose *type* doesn't reference them (use `omit […] in` before the affected lemma
   to suppress).
3. **`omit […] in` against a wide section block** — appropriate when most lemmas need the
   instances but a minority don't. Don't use omit for *warning suppression alone* if it's cheap
   to drop the instance from the section instead and add it inline to the few that need it.

If a typeclass shows up in `n / m` of the omit clauses in a file, it's a strong signal that the
section variable for it should be pushed outward (out of the section) and added back inline only
where needed. `VCVio/CryptoFoundations/FiatShamir/Sigma/Stateful/Compatibility.lean` was migrated
this way: 23 identical `omit [SampleableType Stmt] [SampleableType Wit] in` clauses became zero.

### `[Fintype X]` vs. `[Finite X]` for body-only hypotheses

If your lemma's *body* uses `[Fintype M]` (e.g. to call a downstream lemma) but its *type* never
mentions `M` finitely, the `unusedFintypeInType` linter will flag it. The recommended fix is to
declare `[Finite M]` instead, and add `haveI : Fintype M := Fintype.ofFinite M` at the top of the
proof body. `Examples/CommitmentScheme/Binding.lean` uses this for `[Finite M] [Finite S]` in the
`binding_rest_noCollision_le_inv` family.

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
| `probEvent_bind_bind_swap` | Swap two independent binds (used internally by `vcstep` probability-equality rewrites) |
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
   → Use `vcstep` if the swap should close the equality
   → Use `vcstep rw` / `vcstep rw under n` if you need an explicit rewrite step

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

4. **`evalDist` on bare `query t`**: works directly when the expected type pins `query t` to a monadic form, since `query` resolves to `HasQuery.query`. Write `evalDist (query t : OracleComp spec _)` (or hand the result to a context that provides the same ascription). If you need the primitive `OracleQuery spec _` (e.g. for `OracleQuery.cont`), use `spec.query t` instead.

5. **`subst hy` fails after `simp only [simulateQ_pure] at hy`**: this is the common shape after destructuring `support`. The `simulateQ_pure` rewrite alone doesn't reduce `support ((pure x).run st)` to a singleton — you need to add `StateT.run_pure, support_pure, Set.mem_singleton_iff`. The canonical recipe for "extract the pure result out of a chain of simulateQ binds" is:

   ```lean
   simp only [simulateQ_pure, StateT.run_pure, support_pure,
     Set.mem_singleton_iff] at hy
   subst hy   -- or `obtain rfl := hy`
   ```

   When the outer monad is `OracleComp spec` (no `StateT`), drop `StateT.run_pure`. When there's
   an extra `bind (pure ...)` in the way (e.g. cache-miss branch of `cachingOracle`), add
   `pure_bind` or `monad_norm` to the simp set.
