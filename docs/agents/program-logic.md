# Program Logic Tactics and Relational Reasoning

## Current Module Boundary

- Import `VCVio.ProgramLogic.Tactics` for normal proof work. This is the canonical user-facing proof mode.
- Internally the tactic implementation is split into `VCVio.ProgramLogic.Tactics.Unary` and
  `VCVio.ProgramLogic.Tactics.Relational`; the umbrella import is still the intended default.
- `VCVio.ProgramLogic.Notation` provides the core notation and convenience predicates used by
  the tactic surface.
- Prefer the step-through tactics from `Tactics` for new proofs.
- `VCVio.ProgramLogic.Unary.StdDoBridge` is a narrow unary bridge for almost-sure correctness in the `.pure`
  `Std.Do` view. It is not the main engine for quantitative or relational VCGen.

## Tactic Quick Reference

### Proof Mode Entry

| Tactic | Goal shape | What it does |
|--------|-----------|--------------|
| `by_equiv` | `g₁ ≡ₚ g₂` or `evalDist g₁ = evalDist g₂` | Enters relational proof mode (`RelTriple`) |
| `game_trans g₂` | `g₁ ≡ₚ g₃` | Splits into `g₁ ≡ₚ g₂` and `g₂ ≡ₚ g₃` |
| `by_dist` | `AdvBound game ε` | Enters TV distance reasoning |
| `by_upto bad` | identical-until-bad TV-distance goals | Applies the `simulateQ` up-to-bad bound |
| `by_hoare` | `Pr[p \| oa] = ...` | Enters quantitative WP reasoning (legacy; prefer `qvcgen_step` which lowers probability goals automatically) |

`by_equiv` enters the coupling-based `RelTriple` shell, not `RelTriple'`, so that
`rvcgen_step` / `rvcgen` can keep decomposing the relational goal.

`by_dist ε` is the explicit variant that fixes the TV-distance contribution to `ε`
before generating the remaining subgoals.

### Relational (pRHL) Tactics

| Tactic | Goal shape | What it does |
|--------|-----------|--------------|
| `rvcgen_step` | `g₁ ≡ₚ g₂`, `evalDist g₁ = evalDist g₂`, or `⟪oa ~ ob \| R⟫` | Lowers into `RelTriple` if needed, then applies one obvious relational step |
| `rvcgen_step using t` | same | Supplies the explicit witness needed by the current shape (bind cut relation, bijection, traversal input relation, or simulation state relation) |
| `rvcgen_step?` | same | Performs one relational step and emits a `Try this` script, usually surfacing a needed `using` hint or `as ⟨...⟩` clause |
| `rvcgen` | same | Repeats relational VCGen across all current goals until stuck |
| `rvcgen using t` | same | Uses `t` for the first step on the main goal, then continues with ordinary `rvcgen` |
| `rvcgen?` | same | Runs `rvcgen` and emits the corresponding explicit script |
| `rel_conseq` | `⟪oa ~ ob \| R'⟫` | Weakens/strengthens postcondition |
| `rel_inline foo` | `⟪... ~ ... \| R⟫` | Unfolds definitions, simplifies |
| `rel_dist` | `⟪oa ~ ob \| EqRel α⟫` | Exits relational mode back to `evalDist oa = evalDist ob` |

### Optional arguments

- `rvcgen_step using R` — on bind goals, provide the intermediate relation explicitly
- `rvcgen_step using f` — on random/query goals, provide the coupling bijection explicitly
- `rvcgen_step using Rin` — on `List.mapM` / `List.foldlM` goals, provide the input relation
- `rvcgen_step using R_state` — on `simulateQ` goals, provide the state invariant relation
- `rvcgen_step as ⟨x₁, x₂, h⟩` — explicitly name the binders introduced by the current step
- `rvcgen using t` — use one explicit first hint, then keep stepping automatically
- `rel_conseq with R` — provide explicit weaker postcondition

### Quantitative VCGen (`qvcgen`)

`qvcgen` is the primary unary tactic for new proofs. It accepts both `Triple` goals and
probability goals, automatically lowering `Pr[...]` into the quantitative engine.

| Tactic | What it does |
|--------|--------------|
| `qvcgen` | Exhaustively decomposes a `Triple` or probability goal with spec-aware stepping, loop invariant auto-detection, and support/indicator leaf closure |
| `qvcgen_step` | One step: probability lowering → bind → conditional → match → loop → leaf |
| `qvcgen_step?` | Performs one step and emits the corresponding explicit script, often including binder names |
| `qvcgen?` | Runs `qvcgen` and emits the full explicit script |
| `qvcgen_step using cut` | Explicit intermediate postcondition for a bind step |
| `qvcgen_step as ⟨x, hx⟩` | Explicit names for binders introduced by the current step |
| `qvcgen_step inv I` | Explicit loop invariant for `replicate`/`foldlM`/`mapM` |
| `qvcgen_step rw` | One explicit top-level bind-swap rewrite on a `Pr[...] = Pr[...]` goal |
| `qvcgen_step rw under n` | One bind-swap rewrite under `n` shared outer bind prefixes |
| `qvcgen_step rw congr` | Expose one shared bind plus its support hypothesis |
| `qvcgen_step rw congr'` | Expose one shared bind without a support hypothesis |
| `exp_norm` | Normalize indicator (`propInd`) and expectation (`wp`) arithmetic |

**Probability-goal handling**: `qvcgen` and `qvcgen_step` automatically handle three
classes of probability goals:

1. **`Pr[...] = 1` lowering** → rewrites into `Triple` form for structural decomposition:
   - `Pr[p | oa] = 1` → `Triple 1 oa (fun x => ⌜p x⌝)`
   - `Pr[= x | oa] = 1` → `Triple 1 oa (fun y => if y = x then 1 else 0)`

2. **`Pr[...] = Pr[...]` equality**:
   - Plain `qvcgen_step` heuristically tries bind swap, bind congruence, swap-then-congr,
     congr-then-swap, and the current bounded under-prefix rewrite sequence
   - `qvcgen_step rw` performs exactly one top-level bind-swap rewrite
   - `qvcgen_step rw under n` rewrites one swap beneath `n` shared outer bind prefixes
   - `qvcgen_step rw congr` / `qvcgen_step rw congr'` expose one shared bind explicitly

3. **General `Pr[...]`** → fallback rewrite to raw `wp` form

**Loop invariants**: `qvcgen` auto-detects `replicate`, `List.foldlM`, and `List.mapM`
in `Triple` goals and applies matching invariant hypotheses from context.
Use `qvcgen_step inv I` to provide an explicit invariant.

**Support-sensitive leaf closure**: `qvcgen` final pass tries `triple_support`,
`triple_propInd_of_support`, `triple_probEvent_eq_one`, and `triple_probOutput_eq_one`
in addition to the standard `triple_pure`, `triple_zero`, and consequence search.

**Naming and suggestions**: plain `qvcgen_step` / `rvcgen_step` now try to pick useful binder
names automatically. The `?` variants run the same step but also emit a concrete `Try this`
script, typically surfacing an explicit `using ...` hint or `as ⟨...⟩` clause that you can paste
back into the proof.

**Opt-in unary lookup**: mark a unary `Triple` theorem with `@[vcgen]` to register it for
bounded head-symbol lookup. This is intentionally narrow: `qvcgen_step` first tries the built-in
leaf rules and local hypotheses, then consults only `@[vcgen]` theorems whose computation head
matches the current goal.

**Pass budget**: exhaustive `qvcgen` / `rvcgen` runs are bounded by
`set_option vcvio.vcgen.maxPasses <n>`. The default is conservative so large proofs stay
predictable; if you intentionally want a longer exhaustive run, raise the option locally around
that proof.

### Raw WP Tactics

These operate on bare `wp` goals (`_ ≤ wp _ _`) without the `Triple` wrapper.
Use them when working directly at the weakest-precondition level.

| Tactic | What it does |
|--------|--------------|
| `wp_step` | One WP decomposition (`wp_bind`, `wp_pure`, `wp_replicate`, `wp_list_mapM`, `wp_list_foldlM`, `wp_query`, `wp_ite`, `wp_dite`, `wp_uniformSample`, `wp_map`, `wp_simulateQ_eq`, `wp_liftComp`) |
| `wp_seq n` | Repeats `wp_step` for `n` layers |


### Probability Equality Control

All probability-equality control now lives under `qvcgen_step`.

| Tactic | What it does |
|--------|--------------|
| `qvcgen_step` | Heuristic dispatcher for common `Pr[...] = Pr[...]` steps: swap, congruence, and small bounded compositions |
| `qvcgen_step rw` | Rewrites one top-level bind swap without trying to close the goal |
| `qvcgen_step rw under n` | Rewrites one bind swap under `n` shared outer bind prefixes on one side |
| `qvcgen_step rw congr` | Reduces `Pr[... \| mx >>= f₁] = Pr[... \| mx >>= f₂]` to a pointwise goal, auto-introducing `x` and `hx : x ∈ support mx` |
| `qvcgen_step rw congr'` | Same, but without the support restriction, auto-introducing only `x` |

### Automation

| Tactic | What it does |
|--------|--------------|
| `rvcgen` | Exhaustive relational VCGen over all open goals, with automatic lowering from `GameEquiv` / `evalDist` equality |
| `rel_dist` | Turns `RelTriple oa ob (EqRel α)` into `evalDist oa = evalDist ob` |

## Probability Equality Guide

### What plain `qvcgen_step` handles

On `Pr[...] = Pr[...]` goals, plain `qvcgen_step` already tries the common
`probEvent_bind_bind_swap` / bind-congruence patterns:

1. **Direct `probOutput` equalities**: `Pr[= x | mx >>= ... >>= ...] = Pr[= x | my >>= ... >>= ...]`
2. **Singly-nested under tsum**: automatically peels one layer via `probOutput_bind_eq_tsum` + `tsum_congr` + `congr 1`

### When to use the explicit `rw` subcommands

- **Need to keep going after a swap**: use `qvcgen_step rw`
- **Need to swap below shared outer binds**: use `qvcgen_step rw under n`
- **Need to expose one common outer bind with support information**: use `qvcgen_step rw congr`
- **Need the support-free congruence variant**: use `qvcgen_step rw congr'`
- **Need a deeper swap than the current bounded automation knows**: peel outer layers manually, then use `qvcgen_step rw`

### Key insight: `probOutput` vs `probEvent`

The underlying bind-swap lemma `probEvent_bind_bind_swap` works with `probEvent`.
Most crypto proofs use `probOutput`. The `qvcgen_step` probability-equality machinery
bridges between them with `probEvent_eq_eq_probOutput` when needed.

### Patterns

**Standalone swap**:
```lean
qvcgen_step
```

**Rewrite one swap and continue**:
```lean
qvcgen_step rw
```

**Rewrite under one shared bind**:
```lean
qvcgen_step rw under 1
```

**Expose one common bind with support information**:
```lean
qvcgen_step rw congr
exact h _ ‹_›
```

**Expose one common bind without support information**:
```lean
qvcgen_step rw congr'
rename_i x
```

## Relational Infrastructure

### RelTriple (pRHL coupling)

```lean
abbrev RelPost (α β : Type) := α → β → Prop
def EqRel (α : Type) : RelPost α α := fun x y => x = y

-- ⟪oa ~ ob | R⟫
abbrev RelTriple (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β)
    (R : RelPost α β) : Prop
```

Key rules:

| Rule | Use |
|------|-----|
| `relTriple_pure_pure` | Both sides are `pure`, prove `R a b` |
| `relTriple_bind` | Decompose bind on both sides |
| `relTriple_refl` | Same computation → `EqRel` |
| `relTriple_eqRel_of_eq` | Definitionally equal → `EqRel` |
| `relTriple_eqRel_of_evalDist_eq` | Same distribution → `EqRel` |
| `relTriple_query` | Same query → `EqRel` on response |
| `relTriple_query_bij` | Same query with bijection `f` → `fun a b => f a = b` |
| `relTriple_uniformSample_bij` | Uniform sampling with bijection |
| `relTriple_if` | Synchronized conditional |
| `relTriple_post_mono` | Weaken postcondition |
| `evalDist_eq_of_relTriple_eqRel` | Extract `evalDist` equality from `EqRel` triple |

### Relational simulateQ

For oracle simulation with state invariants:

```lean
relTriple_simulateQ_run :
  (∀ t s₁ s₂, R_state s₁ s₂ → RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂)
    (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2)) →
  R_state s₁ s₂ →
  RelTriple ((simulateQ impl₁ oa).run s₁) ((simulateQ impl₂ oa).run s₂)
    (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2)
```

### Identical Until Bad

```lean
tvDist_simulateQ_le_probEvent_bad :
  (¬bad s₀) →
  (∀ t s, ¬bad s → (impl₁ t).run s = (impl₂ t).run s) →
  (bad monotone for impl₁ and impl₂) →
  tvDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀)
    ≤ Pr[bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₀].toReal
```

### eRHL (quantitative relational logic)

```lean
-- ⦃f⦄ c₁ ≈ₑ c₂ ⦃g⦄
def eRelTriple (pre : ℝ≥0∞) (oa ob : ...) (post : α → β → ℝ≥0∞) : Prop :=
  pre ≤ eRelWP oa ob post

-- ⟪c₁ ≈[ε] c₂ | R⟫
def ApproxRelTriple (ε : ℝ≥0∞) (oa ob : ...) (R : RelPost α β) : Prop :=
  eRelTriple (1 - ε) oa ob (RelPost.indicator R)
```

pRHL is the special case where `ε = 0` (exact coupling).

### Design target

eRHL is the design target for relational program logic in this repo. When extending the
logic, build the quantitative `ℝ≥0∞` foundation first, then recover pRHL and apRHL as
special cases via indicator postconditions. Do not add a pRHL-only layer that bypasses
the quantitative foundation.

The current tactic UX is still pRHL-flavored because the interactive proof shell is
`RelTriple`. That is intentional: exact coupling is the most ergonomic step-through mode
today, even though the semantic design target remains eRHL-first.

Before changing the eRHL / pRHL / apRHL design, consult
*A Quantitative Probabilistic Relational Hoare Logic* ([ERHL25](../../REFERENCES.md#erhl25)).
Treat the published paper as the authoritative source for the intended relational WP
design. For the historical pRHL lineage behind exact coupling, see
[PRHL14](../../REFERENCES.md#prhl14).

## Game-Hopping Proof Skeleton

```lean
theorem my_security : g₁ ≡ₚ gₙ := by
  game_trans g₂
  · by_equiv            -- g₁ ≡ₚ g₂ via coupling
    rvcgen_step using R
    · rvcgen_step using f
      · exact hf
      · intro x
        exact hR x
    · intro a b hab
      rvcgen
  · game_trans g₃       -- g₂ ≡ₚ gₙ
    · ...
    · ...
```

## Common Pitfalls

1. **Plain `qvcgen_step` may close or progress a probability equality goal**: use
   `qvcgen_step rw` / `qvcgen_step rw under n` when you specifically want a rewrite and
   intend to continue.

2. **Import `VCVio.ProgramLogic.Tactics`**: tactics are defined there. If a file only imports `VCVio.ProgramLogic.Notation`, add/change the import.

3. **`game_rule` simp set**: many tactics use `simp only [game_rule]` internally. Ensure relevant `@[simp]` lemmas are in scope.

4. **`rvcgen_step using R`**: when Lean can't infer the witness for the current relational shape
   (bind cut, bijection, traversal input relation, or simulation invariant), provide it explicitly.

5. **`StdDoBridge` is deliberately narrow**: use it for unary almost-sure `.pure` `Std.Do` experiments, not as the default path for quantitative or relational proofs.
