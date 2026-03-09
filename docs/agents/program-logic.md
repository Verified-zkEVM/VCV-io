# Program Logic Tactics and Relational Reasoning

## Current Module Boundary

- Import `VCVio.ProgramLogic.Tactics` for normal proof work. This is the canonical user-facing proof mode.
- `VCVio.ProgramLogic.Notation` provides notation, convenience predicates, and coarse compatibility macros:
  `game_wp`, `game_rel`, `coupling`, `game_hop`.
- Prefer the step-through tactics from `Tactics.lean` over the coarse macros for new proofs.
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
| `by_hoare` | `Pr[p \| oa] = ...` | Enters quantitative WP reasoning |

`by_equiv` enters the coupling-based `RelTriple` shell, not `RelTriple'`, so that
`rel_step`, `rel_rnd`, `rel_skip`, and the other interactive tactics compose cleanly.

### Relational (pRHL) Tactics

| Tactic | Goal shape | What it does |
|--------|-----------|--------------|
| `rel_step` | `⟪oa >>= fa ~ ob >>= fb \| S⟫` | Decomposes one bind layer |
| `rel_seq n` | nested bind chains | Repeats `rel_step` for `n` layers |
| `rel_rnd` | `⟪query i ~ query i \| R⟫` | Couples identical queries/sampling |
| `rel_skip` | `⟪oa ~ oa \| EqRel α⟫` | Closes identical computations |
| `rel_pure` | `⟪pure a ~ pure b \| R⟫` | Closes pure return goals |
| `rel_cond` | `⟪if c then a₁ else a₂ ~ if c then b₁ else b₂ \| R⟫` | Splits on condition |
| `rel_conseq` | `⟪oa ~ ob \| R'⟫` | Weakens/strengthens postcondition |
| `rel_inline foo` | `⟪... ~ ... \| R⟫` | Unfolds definitions, simplifies |
| `rel_sim` | Simulated computation goals | Chooses `relTriple_simulateQ_run` or `relTriple_simulateQ_run'` |

### Optional arguments

- `rel_step using R` — provide explicit intermediate relation
- `rel_seq n using R` — use `rel_step using R` first, then keep stepping with plain `rel_step`
- `rel_rnd using f` — provide explicit bijection for coupling
- `rel_conseq with R` — provide explicit weaker postcondition

### Unary WP

| Tactic | What it does |
|--------|--------------|
| `hoare_step` | One quantitative `Triple` decomposition step, falling back to `wp_step` |
| `hoare_seq n` | Repeats `hoare_step` for `n` layers |
| `wp_step` | One WP decomposition (wp_bind, wp_pure, wp_query, wp_ite, wp_uniformSample, wp_map) |
| `wp_seq n` | Repeats `wp_step` for `n` layers |

### Bind Reordering

| Tactic | What it does |
|--------|--------------|
| `prob_swap` | Swaps two independent sampling operations in a `Pr[...]` goal |
| `prob_swap_at n` | Applies `prob_swap` up to `n` times |
| `prob_swap_rw` | Rewrites one bind-swap without closing the goal |
| `prob_congr` | Reduces `Pr[... \| mx >>= f₁] = Pr[... \| mx >>= f₂]` to pointwise equality |
| `prob_congr'` | Same as `prob_congr` but without support restriction |

### Automation

| Tactic | What it does |
|--------|--------------|
| `game_rel'` | Exhaustive relational prover (rel_step + rel_rnd + rel_skip + rel_pure + ...) |
| `game_wp` | Compatibility macro: repeatedly applies WP rules |
| `game_rel` / `coupling` | Compatibility macros: coarse relational decomposition through bind/query |
| `game_hop` | Compatibility macro: tries to close a game-hopping step |
| `rel_dist` | Turns `RelTriple oa ob (EqRel α)` into `evalDist oa = evalDist ob` |

## `prob_swap` Detailed Guide

### What it handles

`prob_swap` automates `probEvent_bind_bind_swap`, which proves that independent monadic binds can be reordered:

1. **Direct `probOutput` equalities**: `Pr[= x | mx >>= ... >>= ...] = Pr[= x | my >>= ... >>= ...]`
2. **Singly-nested under tsum**: automatically peels one layer via `probOutput_bind_eq_tsum` + `tsum_congr` + `congr 1`

### What it does NOT handle

- **Rewriting a subexpression**: use `prob_swap_rw` or `rw [probEvent_bind_bind_swap]` directly
- **Deeply nested swaps** (2+ layers deep): manually peel outer layers first, then use `prob_swap` for the inner swap
- **`rw`-style usage**: `prob_swap` closes goals; if you need to continue, use the manual pattern

### Key insight: `probOutput` vs `probEvent`

The underlying lemma `probEvent_bind_bind_swap` works with `probEvent`. Most crypto proofs use `probOutput`. `prob_swap` automatically bridges via `probEvent_eq_eq_probOutput`.

### Patterns

**Standalone swap** (replaces 10-15 lines):
```lean
-- Before: simpa [bind_assoc] using (probEvent_bind_bind_swap (mx := ...) ...)
-- After:
prob_swap
```

**Singly-nested swap** (replaces 15-20 lines):
```lean
-- Before: rw [probOutput_bind_eq_tsum, ...]; refine tsum_congr ...; simpa [bind_assoc] using ...
-- After:
prob_swap
```

**Doubly-nested** (first layer manual, inner automated):
```lean
rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
refine tsum_congr fun x => ?_
congr 1
prob_swap
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
    rel_step
    · rel_rnd
    · intro a b hab
      rel_step
      · rel_skip
      · intro ...
        rel_pure
  · game_trans g₃       -- g₂ ≡ₚ gₙ
    · ...
    · ...
```

## Common Pitfalls

1. **`prob_swap` closes goals, it doesn't rewrite**: use `prob_swap_rw` or manual `rw [probEvent_bind_bind_swap]` when you need to continue.

2. **Import `VCVio.ProgramLogic.Tactics`**: tactics are defined there. If a file only imports `VCVio.ProgramLogic.Notation`, add/change the import.

3. **`game_rule` simp set**: many tactics use `simp only [game_rule]` internally. Ensure relevant `@[simp]` lemmas are in scope.

4. **`rel_step using R`**: when Lean can't infer the intermediate relation, provide it explicitly.

5. **`StdDoBridge` is deliberately narrow**: use it for unary almost-sure `.pure` `Std.Do` experiments, not as the default path for quantitative or relational proofs.
