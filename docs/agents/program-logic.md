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
| `by_hoare` | `Pr[p \| oa] = ...` | Enters quantitative WP reasoning (legacy; prefer `vcstep` which lowers probability goals automatically) |

`by_equiv` enters the coupling-based `RelTriple` shell, not `RelTriple'`, so that
`rvcstep` / `rvcgen` can keep decomposing the relational goal.

`by_dist ε` is the explicit variant that fixes the TV-distance contribution to `ε`
before generating the remaining subgoals.

### Relational (pRHL) Tactics

| Tactic | Goal shape | What it does |
|--------|-----------|--------------|
| `rvcstep` | `g₁ ≡ₚ g₂`, `evalDist g₁ = evalDist g₂`, `⟪oa ~ ob \| R⟫`, or `⦃f⦄ oa ≈ₑ ob ⦃g⦄` | Lowers into relational mode if needed, then applies one obvious relational step |
| `rvcstep using t` | same | Supplies the explicit witness needed by the current shape (bind cut relation, bijection, traversal input relation, or simulation state relation) |
| `rvcstep with thm` | same | Force one explicit relational theorem/assumption step |
| `rvcstep?` | same | Performs one relational step and emits a `Try this` script, usually surfacing a needed `using` hint, `with theorem`, or `as ⟨...⟩` clause |
| `rvcgen` | same | Repeats relational VCGen across all current goals until stuck |
| `rvcgen using t` | same | Uses `t` for the first step on the main goal, then continues with ordinary `rvcgen` |
| `rvcgen with thm` | same | Uses `thm` for the first step on the main goal, then continues with ordinary `rvcgen` |
| `rvcgen?` | same | Runs `rvcgen` and emits the corresponding explicit script |
| `rel_conseq` | `⟪oa ~ ob \| R'⟫` | Weakens/strengthens postcondition |
| `rel_inline foo` | `⟪... ~ ... \| R⟫` | Unfolds definitions, simplifies |
| `rel_dist` | `⟪oa ~ ob \| EqRel α⟫` | Exits relational mode back to `evalDist oa = evalDist ob` |

### Optional arguments

- `rvcstep using R` — on bind goals, provide the intermediate relation explicitly
- `rvcstep using f` — on random/query goals, provide the coupling bijection explicitly
- `rvcstep using Rin` — on `List.mapM` / `List.foldlM` goals, provide the input relation
- `rvcstep using R_state` — on `simulateQ` goals, provide the state invariant relation
- `rvcstep with thm` — force one explicit registered/local relational theorem
- `rvcstep as ⟨x₁, x₂, h⟩` — explicitly name the binders introduced by the current step
- `rvcgen using t` / `rvcgen with thm` — use one explicit first hint/theorem, then keep stepping automatically
- `rel_conseq with R` — provide explicit weaker postcondition

### Quantitative VCGen (`vcgen`)

`vcgen` is the primary unary tactic for new proofs. It accepts both `Triple` goals and
probability goals, automatically lowering `Pr[...]` into the quantitative engine.

| Tactic | What it does |
|--------|--------------|
| `vcgen` | Exhaustively decomposes a `Triple` or probability goal with spec-aware stepping, loop invariant auto-detection, and support/indicator leaf closure |
| `vcstep` | One step: probability lowering → bind → conditional → match → loop → leaf |
| `vcstep?` | Performs one step and emits the corresponding explicit script, often surfacing `as ⟨...⟩`, `using cut`, `inv I`, or `with theorem` |
| `vcgen?` | Runs `vcgen` and emits the planned step replay across each pass |
| `vcstep using cut` | Explicit intermediate postcondition for a bind step |
| `vcstep with thm` | Force one explicit unary theorem/assumption step |
| `vcstep as ⟨x, hx⟩` | Explicit names for binders introduced by the current step |
| `vcstep inv I` | Explicit loop invariant for `replicate`/`foldlM`/`mapM` |
| `vcstep rw` | One explicit top-level bind-swap rewrite on a `Pr[...] = Pr[...]` goal |
| `vcstep rw under n` | One bind-swap rewrite under `n` shared outer bind prefixes |
| `vcstep rw congr` | Expose one or more shared binds plus their support hypotheses |
| `vcstep rw congr'` | Expose one or more shared binds without support hypotheses |
| `exp_norm` | Normalize indicator (`propInd`) and expectation (`wp`) arithmetic |

**Probability-goal handling**: `vcgen` and `vcstep` automatically handle four
classes of probability goals:

1. **`Pr[...] = 1` lowering** → rewrites into `Triple` form for structural decomposition:
   - `Pr[p | oa] = 1` → `Triple 1 oa (fun x => ⌜p x⌝)`
   - `Pr[= x | oa] = 1` → `Triple 1 oa (fun y => if y = x then 1 else 0)`

2. **Lower-bound event/output goals** → stay inside unary VCGen by reusing the same `Triple`
   shell:
   - `r ≤ Pr[p | oa]` / `Pr[p | oa] ≥ r` → `Triple r oa (fun x => ⌜p x⌝)`
   - `r ≤ Pr[= x | oa]` / `Pr[= x | oa] ≥ r` → `Triple r oa (fun y => if y = x then 1 else 0)`

3. **`Pr[...] = Pr[...]` equality**:
   - Plain `vcstep` first normalizes common `map`/`bind` surface syntax (`map_eq_bind_pure_comp`,
     `bind_assoc`), then preview-selects the best bounded swap/congruence plan from the fast path
   - `vcstep rw` performs exactly one top-level bind-swap rewrite
   - `vcstep rw under n` rewrites one swap beneath `n` shared outer bind prefixes
   - `vcstep rw congr` / `vcstep rw congr'` expose one or more shared binds explicitly

4. **Other general `Pr[...]` goals** → rewrite to raw `wp` form and keep stepping structurally
   when a `wp` rule applies. On an already-lowered raw-`wp` goal, `vcstep?` / `vcgen?`
   will explicitly note that they are continuing in raw `wp` mode.

**Loop invariants**: `vcgen` auto-detects `replicate`, `List.foldlM`, and `List.mapM`
in `Triple` goals and applies matching invariant hypotheses from context.
Use `vcstep inv I` to provide an explicit invariant.

**Support-sensitive leaf closure**: `vcgen` final pass tries `triple_support`,
`triple_propInd_of_support`, `triple_probEvent_eq_one`, and `triple_probOutput_eq_one`
in addition to the standard `triple_pure`, `triple_zero`, and consequence search.

**Naming and suggestions**: plain `vcstep` / `rvcstep` keep the stable execution path.
The `?` variants run a planner-backed version of the same next move and emit a concrete
`Try this` script, typically surfacing an explicit `using ...` hint, `inv I`, `with theorem`,
or `as ⟨...⟩` clause that you can paste back into the proof. On probability-equality goals the
planner may emit a grouped multi-step replay when the best explanation is an explicit rewrite chain.

**Opt-in unary lookup**: mark a unary `Triple` or raw `wp` theorem with `@[vcspec]` to register it for
bounded head-symbol lookup. This is intentionally narrow: after the built-in structural step and
explicit hint opportunities, `vcstep` / `vcgen` consult only `@[vcspec]` theorems whose
computation head matches the current goal. Use `vcstep with myLemma` when you want to force
one specific theorem/assumption step manually.

**Opt-in relational lookup**: mark a relational `RelTriple`, `RelWP`, or `eRelTriple` theorem
with `@[vcspec]` to register it for the analogous bounded head-pair lookup on the relational side.
This is especially useful for automation-oriented `simulateQ` transport lemmas whose outer
computation heads are stable but whose inner invariants or projection arguments still come from
the local context.

**Pass budget**: exhaustive `vcgen` / `rvcgen` runs are bounded by
`set_option vcvio.vcgen.maxPasses <n>`. The default is conservative so large proofs stay
predictable; if you intentionally want a longer exhaustive run, raise the option locally around
that proof.

**Trace output**: set `set_option vcvio.vcgen.traceSteps true` to log the chosen planned step,
goal delta, and any planner alternatives that were previewed while debugging tactic choice.

### Raw WP Tactics

Raw `wp` goals (`_ ≤ wp _ _`) now use the same unary entrypoints rather than a separate tactic
family. `vcstep` performs one decomposition step and `vcgen` keeps stepping exhaustively.


### Probability Equality Control

All probability-equality control now lives under `vcstep`.

| Tactic | What it does |
|--------|--------------|
| `vcstep` | Fast dispatcher for common `Pr[...] = Pr[...]` steps: syntax normalization, swap, congruence, and bounded compositions chosen by preview |
| `vcstep rw` | Rewrites one top-level bind swap without trying to close the goal |
| `vcstep rw under n` | Rewrites one bind swap under `n` shared outer bind prefixes on one side |
| `vcstep rw congr` | Reduces `Pr[... \| mx >>= f₁] = Pr[... \| mx >>= f₂]` to a pointwise goal, auto-introducing `x` and `hx : x ∈ support mx`; the explicit `as ⟨...⟩` form can peel multiple shared binds at once |
| `vcstep rw congr'` | Same, but without the support restriction; the explicit `as ⟨...⟩` form can peel multiple shared binds at once |

### Automation

| Tactic | What it does |
|--------|--------------|
| `rvcgen` | Exhaustive relational VCGen over all open goals, with automatic lowering from `GameEquiv` / `evalDist` equality |
| `rel_dist` | Turns `RelTriple oa ob (EqRel α)` into `evalDist oa = evalDist ob` |

## Probability Equality Guide

### What plain `vcstep` handles

On `Pr[...] = Pr[...]` goals, plain `vcstep` already tries the common
`probEvent_bind_bind_swap` / bind-congruence patterns:

1. **Direct `probOutput` equalities**: `Pr[= x | mx >>= ... >>= ...] = Pr[= x | my >>= ... >>= ...]`
2. **Nested bounded rewrites**: automatically peels small shared-bind prefixes and prefers a
   closing swap/congruence plan when one is available
3. **Surface `map` wrappers**: normalizes the common `map_eq_bind_pure_comp` / `bind_assoc` shape
   before searching for swaps or congruence

### When to use the explicit `rw` subcommands

- **Need to keep going after a swap**: use `vcstep rw`
- **Need to swap below shared outer binds**: use `vcstep rw under n`
- **Need to expose one or more common outer binds with support information**: use `vcstep rw congr`
- **Need the support-free congruence variant**: use `vcstep rw congr'`
- **Need the full explicit replay for a bounded nested swap**: use `vcstep?`
- **Need a deeper swap than the current bounded automation knows**: peel outer layers manually, or
  use `vcstep?` to see the best bounded replay the planner found before finishing the rest by hand

### Key insight: `probOutput` vs `probEvent`

The underlying bind-swap lemma `probEvent_bind_bind_swap` works with `probEvent`.
Most crypto proofs use `probOutput`. The `vcstep` probability-equality machinery
bridges between them with `probEvent_eq_eq_probOutput` when needed.

### Patterns

**Standalone swap**:
```lean
vcstep
```

**Rewrite one swap and continue**:
```lean
vcstep rw
```

**Rewrite under one shared bind**:
```lean
vcstep rw under 1
```

**Expose one common bind with support information**:
```lean
vcstep rw congr
exact h _ ‹_›
```

**Expose one common bind without support information**:
```lean
vcstep rw congr'
rename_i x
```

**Expose two shared binds explicitly at once**:
```lean
vcstep rw congr' as ⟨x, y⟩
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

### Handler `@[spec]` catalog (`Unary/HandlerSpecs.lean`)

Per-call `Std.Do.Triple` specs, all tagged `@[spec]` so `mvcgen` can
compose them automatically through multi-query handler programs:

| Handler | Spec | Postcondition |
|---------|------|---------------|
| `cachingOracle` | `cachingOracle_triple` | `cache₀ ≤ cache' ∧ cache' t = some v` (shared live-query + cache-monotonicity) |
| `seededOracle` | `seededOracle_triple` | branch on `seed t`: `nil → no-op`, `cons u us → pop head` |
| `loggingOracle` | `loggingOracle_triple` | `log' = log₀ ++ [⟨t, v⟩]` (always extend the log) |
| `countingOracle` | `countingOracle_triple` | `qc' = qc₀ + QueryCount.single t` (monoid variant of `WriterT` bridge) |
| `costOracle` | `costOracle_triple` | `s' = s₀ * costFn t` for arbitrary `[Monoid ω]` |

The `WriterT`-based handlers come in both `Append`-parameterized
(`loggingOracle`) and `Monoid`-parameterized (`countingOracle`,
`costOracle`) flavors; the corresponding bridge lemmas
`triple_writerT_iff_forall_support` and
`triple_writerT_iff_forall_support_monoid` live in `Unary/StdDoBridge.lean`.

### Whole-program invariant preservation (`SimSemantics/PreservesInv.lean`)

Support-based invariant-preservation over `simulateQ`, for both the
state-transformer and writer-transformer models:

| Definition | Shape | Meaning |
|------------|-------|---------|
| `QueryImpl.PreservesInv` | `σ → Prop` | every `(impl t).run σ₀` keeps the state invariant |
| `QueryImpl.WriterPreservesInv` | `ω → Prop` under `[Monoid ω]` | every `(impl t).run` step keeps `s₀ * w` satisfying `Inv` |
| `OracleComp.simulateQ_run_preservesInv` | — | lift per-query `PreservesInv` to whole simulation |
| `OracleComp.simulateQ_run_writerPreservesInv` | — | writer analogue |

`WriterPreservesInv` is the canonical invariant-preservation API for
writer-based handlers like `countingOracle`/`costOracle`. Typical use:
pick `Inv s := s ≤ B` (cost-budget) or `Inv s := s ∈ Submonoid.S` (stays
in a submonoid).

### Unary-to-relational handler lift (`Relational/HandlerFromUnary.lean`)

If each handler has a `Std.Do.Triple` spec (produced by `mvcgen` or a
`@[spec]` lemma), you do not have to assemble per-call `RelTriple`s by
hand. The lift converts unary handler specs plus a synchronization
condition into a whole-program `RelTriple`:

```lean
relTriple_simulateQ_run_of_triples :
  (∀ t s, Triple (impl₁ t) ⌜· = s⌝ (⇓a s' => ⌜Q₁ t s a s'⌝)) →
  (∀ t s, Triple (impl₂ t) ⌜· = s⌝ (⇓a s' => ⌜Q₂ t s a s'⌝)) →
  (hsync : Q₁ ∧ Q₂ ⇒ output equality + R_state preservation) →
  R_state s₁ s₂ →
  RelTriple ((simulateQ impl₁ oa).run s₁) ((simulateQ impl₂ oa).run s₂)
    (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2)
```

Projection and bridge variants:

| Variant | Use when |
|---------|----------|
| `relTriple_simulateQ_run_of_triples` | Full `(value, state)` postcondition (`StateT`) |
| `relTriple_simulateQ_run'_of_triples` | Only `EqRel α` on projected outputs (`StateT`) |
| `relTriple_simulateQ_run_of_impl_eq_triple` | Two handlers agreeing on `Inv`; preservation spec is a `Std.Do.Triple`; conclude `EqRel (α × σ)` |
| `relTriple_simulateQ_run_writerT` | Whole-program `WriterT` coupling from per-query `RelTriple`s plus a monoid-congruence hypothesis on the accumulated writers |
| `relTriple_simulateQ_run_writerT'` | Output-projection of `relTriple_simulateQ_run_writerT` (drops the writer component, yielding `EqRel α` on outputs) |
| `relTriple_simulateQ_run_writerT_of_triples` | `WriterT` handler-level whole-program lift from unary triples (monoid variant) |
| `relTriple_simulateQ_run_writerT'_of_triples` | Output-projection of `relTriple_simulateQ_run_writerT_of_triples` |
| `relTriple_run_of_triple` | Per-call product coupling for `StateT` |
| `relTriple_run_writerT_of_triple` | Per-call product coupling for `WriterT` (`Append` variant, e.g. `loggingOracle`) |
| `relTriple_run_writerT_of_triple_monoid` | Per-call product coupling for `WriterT` (`Monoid` variant, e.g. `countingOracle`, `costOracle`) |
| `support_preservesInv_of_triple` | Convert `Std.Do.Triple` preservation into `support`-based preservation consumed by `SimulateQ.lean` |

Whenever the handler's invariant-preservation proof already lives as a
`Std.Do.Triple`, prefer `relTriple_simulateQ_run_of_impl_eq_triple` over
the raw `relTriple_simulateQ_run_of_impl_eq_preservesInv` — the bridge
saves you from re-expressing the preservation as a `support`-based
quantifier.

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
    rvcstep using R
    · rvcstep using f
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

1. **Plain `vcstep` may close or progress a probability equality goal**: use
   `vcstep rw` / `vcstep rw under n` when you specifically want a rewrite and
   intend to continue.

2. **Import `VCVio.ProgramLogic.Tactics`**: tactics are defined there. If a file only imports `VCVio.ProgramLogic.Notation`, add/change the import.

3. **`game_rule` simp set**: many tactics use `simp only [game_rule]` internally. Ensure relevant `@[simp]` lemmas are in scope.

4. **`rvcstep using R`**: when Lean can't infer the witness for the current relational shape
   (bind cut, bijection, traversal input relation, or simulation invariant), provide it explicitly.

5. **`StdDoBridge` is deliberately narrow**: use it for unary almost-sure `.pure` `Std.Do` experiments, not as the default path for quantitative or relational proofs.
