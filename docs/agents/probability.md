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

## `grind` vs `simp` on Probability Goals

`grind` and `simp` have complementary strengths here, and reaching for the wrong one is the most
common way to get a `grind` that hangs.

**Use `simp` to compute a concrete probability or factor structure.** `simp` evaluates
`Pr[= x | $ᵗ T]`, `Pr[p | $ᵗ T]`, products of uniform draws, etc.; `grind` is not an `ℝ≥0∞`/`Fintype.card`
arithmetic engine and will not finish these (it fails fast).

**Use `grind` for symbolic / membership / directed-iff goals.** Equiprobability
(`Pr[= x | $ᵗ T] = Pr[= y | $ᵗ T]`), `x ∈ support (…)`, `Pr[= x | mx] = 0 ↔ x ∉ support mx`, and
similar are squarely in `grind`'s wheelhouse.

**Why some characterization lemmas are `@[simp]` but not `@[grind]`.** A characterization whose RHS
introduces an *unbounded* quantifier or set over the support —
`Pr[…] = 0/1 ↔ ∃/∀ x ∈ support …`, `support = {x}`, `support = ∅` — is a `grind` **saturation
hazard**: as `grind` case-splits the iff it instantiates and Skolemizes the support quantifier into
fresh witnesses that re-trigger each other, with no finite grounding (`support ($ᵗ α) = Set.univ` is
infinite). Such lemmas are kept `@[simp]` (fixed orientation, no case-split — safe) and **dropped from
the default `grind` set**. The *directed single-variable* membership bridges
(`probOutput_eq_zero_iff : … ↔ x ∉ support`, `probOutput_pos_iff`, `mem_finSupport_iff`,
`mem_finSupport_iff_mem_support`) are confluent and stay `@[grind =]`.

Lemmas that are `@[simp]`-only by this rule (in `EvalDist/Defs/Basic.lean` unless noted):
`probEvent_eq_zero_iff(')`, `probEvent_ne_zero_iff(')`, `probEvent_pos_iff(')`,
`probEvent_eq_one_iff(')`, `one_eq_probEvent_iff(')`, `probOutput_eq_one_iff(')`,
`one_eq_probOutput_iff`, `probFailure_eq_one_iff`; and in `EvalDist/Monad/Basic.lean`,
`probFailure_bind_eq_zero_iff` (`@[simp]`), `mem_support_bind_iff` / `mem_finSupport_bind_iff`
(untagged — `support_bind` / `finSupport_bind` are the `simp` forms).

**If a `grind` proof needs one of these, re-supply it locally:** `grind [probEvent_eq_zero_iff]`. This
keeps the bridge out of the default set (so naive `grind` on a probability goal fails fast instead of
hanging) while letting the proof that genuinely needs it opt in.

`VCVioTest/ProbabilityTactics.lean` is the living benchmark for this: a curated corpus of
high-school-probability facts, each closed by the weakest of `simp` / `grind` / `simp; grind`, with
`target(grind)` markers where `grind` is not yet enough.

## Common Mistakes

1. **Missing probability spec classes**: on `OracleComp spec`, `evalDist`/`probOutput`/`Pr[...]` require `[IsProbabilitySpec spec]`. Uniform/cardinality lemmas and support-probability lemmas require `[IsUniformSpec spec]`, not just `[spec.Fintype] [spec.Inhabited]`. Use `IsUniformSpec.ofFintypeInhabited spec` when a concrete finite inhabited spec should use uniform sampling.

2. **Carrying duplicate probability instances**: do not add a separate `[IsProbabilitySpec spec]` when `[IsUniformSpec spec]` is already in scope. `IsUniformSpec` extends `IsProbabilitySpec`; a second instance can make instance search ambiguous and may not describe the same distributions.

3. **Using `support` when `finSupport` is needed**: `probOutput_bind_eq_sum_finSupport` requires `[DecidableEq α]` and `[HasEvalFinset m]`.

4. **Forgetting `probOutput_eq_zero_of_not_mem_support`**: useful when restricting sums.

5. **`evalDist` on bare `query t`**: works directly when the expected type pins `query t` to a monadic form, since `query` resolves to `HasQuery.query`. Write `evalDist (query t : OracleComp spec _)` (or hand the result to a context that provides the same ascription). If you need the primitive `OracleQuery spec _` (e.g. for `OracleQuery.cont`), use `spec.query t` instead.
