# VCGen-Style Automation for Probabilistic Program Logic

**Date**: March 7, 2026
**Repo**: `VCV-io`
**Branch**: `quang/more-program-logic`

## Status note

This document is still the right design note for the custom-automation direction, but parts
of it were written before the current `VCVio/ProgramLogic` surface had landed. In particular,
`VCVio/ProgramLogic/Tactics.lean`, the current notation layer, the unary `.pure` `Std.Do`
bridge, bounded-iteration rules for `replicate` / `List.mapM` / `List.foldlM`, `relTriple_if`,
`prob_swap`, and several real-proof validations now exist in tree.

Read this together with `docs/agents/program-logic.md`, which is the live handbook for the
current tactic and notation surface.

## 1. Current State

### What we have

| Layer | File(s) | Status |
|-------|---------|--------|
| **Monad algebra** | `ToMathlib/Control/Monad/Algebra.lean` | ✅ `MAlgOrdered m L` with `wp`, `Triple` |
| **Relational algebra** | `ToMathlib/Control/Monad/RelationalAlgebra.lean` | ✅ `MAlgRelOrdered m₁ m₂ L` with `rwp`, `Triple` |
| **Unary quantitative WP** | `VCVio/ProgramLogic/Unary/HoareTriple.lean` | ✅ `wp`, `Triple`, probability bridge lemmas, `@[game_rule]` support |
| **Unary oracle rules** | `VCVio/ProgramLogic/Unary/SimulateQ.lean` | ✅ `simulateQ` / lifting rules for the quantitative layer |
| **Std.Do bridge** | `VCVio/ProgramLogic/Unary/StdDoBridge.lean` | ✅ Narrow `.pure` bridge for almost-sure unary correctness only |
| **Exact pRHL** | `VCVio/ProgramLogic/Relational/Basic.lean` | ✅ `RelTriple` via coupling plus structural rules |
| **Quantitative eRHL / apRHL** | `VCVio/ProgramLogic/Relational/Quantitative.lean` | ✅ `eRelTriple`, `ApproxRelTriple`, TV-distance bridges |
| **Relational simulateQ** | `VCVio/ProgramLogic/Relational/SimulateQ.lean` | ✅ identical-until-bad and simulation rules |
| **Notation + coarse compatibility macros** | `VCVio/ProgramLogic/Notation.lean` | ✅ notation, convenience predicates, `game_wp`, `game_rel`, `coupling`, `game_hop` |
| **Canonical step-through tactics** | `VCVio/ProgramLogic/Tactics.lean` | ✅ EasyCrypt-inspired interactive proof mode |
| **Validation/examples** | `VCVio/ProgramLogic/TacticsExamples.lean`, `Examples/OneTimePad.lean`, `Examples/HHS_Elgamal.lean` | ✅ tactics are used in real proofs, not just demos |

### Key rules available

**Unary quantitative core:**
- `wp_pure`, `wp_bind`, `wp_query`, `wp_ite`, `wp_uniformSample`
- `wp_map`, `wp_simulateQ_eq`, `wp_liftComp`, `wp_simulateQ_run'_eq`
- `wp_replicate_zero`, `wp_replicate_succ`
- `wp_list_mapM_nil`, `wp_list_mapM_cons`
- `wp_list_foldlM_nil`, `wp_list_foldlM_cons`

**Relational exact coupling core:**
- `relTriple_refl`, `relTriple_bind`, `relTriple_pure_pure`
- `relTriple_query`, `relTriple_query_bij`, `relTriple_uniformSample_bij`
- `relTriple_map`, `relTriple_if`, `relTriple_post_mono`
- `relTriple_eqRel_of_eq`, `relTriple_eqRel_of_evalDist_eq`
- `relTriple_replicate`, `relTriple_list_mapM`, `relTriple_list_foldlM`
- `relTriple_simulateQ_run`, `relTriple_simulateQ_run'`

**Current user-facing tactic surface:**
- `wp_step`, `wp_seq`, `hoare_step`, `hoare_seq`, `game_hoare`
- `rel_step`, `rel_seq`, `rel_rnd`, `rel_skip`, `rel_pure`, `rel_cond`, `rel_conseq`
- `rel_inline`, `rel_sim`, `rel_sim_dist`, `rel_replicate`, `rel_mapM`, `rel_foldlM`
- `by_equiv`, `rel_dist`, `game_trans`, `by_dist`, `by_upto`, `by_hoare`
- `prob_swap`, `prob_swap_rw`, `prob_congr`, `prob_congr'`, `game_rel'`

**Still genuinely missing:**
- stronger `rel_sim` / relational simulation automation
- a broader structural VCGen for quantitative goals beyond the current step/sequence layer
- a more automatic relational simulation / identical-until-bad proof mode over real security proofs
- broader bounded-iteration coverage beyond `replicate` / `List.mapM` / `List.foldlM`
- validation of the bounded-iteration tactics on flagship crypto proofs

### Pain points from real proofs (HHS_Elgamal, FiatShamir)

1. **Bind reordering is still only partially automated**: `prob_swap` and `prob_swap_rw` cover the common cases, but deeper nested swaps still need manual peeling.
2. **Elaborator coverage is still partial**: core tactics now have goal-directed diagnostics, but higher-level automation is still mostly macro-based.
3. **The `Std.Do` bridge is intentionally narrow**: it helps for unary almost-sure correctness, but it is not the engine for quantitative or relational VCGen.
4. **Higher-level proof automation is still missing**: bounded loop invariants now exist for the
   `List.foldlM` fragment, but stronger `rel_sim`, broader unary structural VCGen, and
   proof automation over larger security developments remain future work.

## 2. Why Not Extend `Std.Do`/`mvcgen` Directly

The `Std.Do` framework is **fundamentally Prop-based**:

- `PostShape` → `Assertion` → `SPred` → all `Prop`-valued
- `PredTrans.apply : PostCond α ps → Assertion ps` lives in `Prop`
- VCGen pattern-matches on `PredTrans.apply` as the goal head
- `@[spec]` attribute expects `Triple prog P Q` in the Std.Do sense
- `dischargePostEntails` uses `PostCond.entails` (Prop entailment)

For quantitative WP (`pre ≤ wp oa post` with `ℝ≥0∞`), we'd need:
- A new `PostCond` type (`α → ℝ≥0∞` instead of `α → Assertion ps`)
- A new `PredTrans` type (`(α → ℝ≥0∞) → ℝ≥0∞` with monotonicity)
- New entailment (`≤` on `ℝ≥0∞` instead of `⊢ₛ`)
- New VCGen pattern matching

For relational triples (`RelTriple oa ob R` with two programs), we'd additionally need:
- Two-program goal structure
- Lockstep traversal of two `do` blocks

**Decision**: Build a custom tactic layer that directly targets our goal shapes, rather than trying to extend `Std.Do`.

## 3. Design: Two Tactic Families

### 3.1 Unary Quantitative WP Tactics

**Goal shape**: `pre ≤ wp oa post` or `wp oa post = expr`

#### `wp_step` — Single-step WP decomposition

Applies exactly one WP rule and stops, exposing the intermediate postcondition.

```
wp_step        -- apply one rule (wp_bind, wp_pure, wp_query, ...)
game_wp        -- exhaustive (existing, enhanced with more rules)
```

**Rules tried in order:**
1. `wp_bind` — decomposes `wp (oa >>= ob) post`
2. `wp_pure` — closes `wp (pure x) post = post x`
3. `wp_replicate_*` — decomposes bounded repetition
4. `wp_list_mapM_*` — decomposes finite traversals
5. `wp_list_foldlM_*` — decomposes bounded invariant-carrying folds
6. `wp_query` — expands `wp (query t) post` to uniform sum
7. `wp_ite` — splits `wp (if c then a else b) post`
8. `wp_uniformSample` — expands sampling
9. `wp_map` — handles `wp (f <$> oa) post`
10. `wp_simulateQ_eq` — passes through oracle simulation
11. `wp_liftComp` — passes through spec lifting

**Status**: `wp_step` has landed in `VCVio/ProgramLogic/Tactics.lean`.

#### `game_wp_simp` — Arithmetic simplification after WP decomposition

After stepping, goals become arithmetic over `ℝ≥0∞`. This tactic handles:
- Pulling constants out of sums: `∑' x, c * f x = c * ∑' x, f x`
- Simplifying uniform probabilities: `Pr[= x | $ᵗ T] = 1 / card T`
- Standard `ℝ≥0∞` arithmetic

**Status**: still future work. Today this is handled ad hoc with `simp`, `rw`, `grind`,
and ordinary arithmetic lemmas after `wp_step`.

### 3.2 Relational Step-Through Tactics (EasyCrypt-inspired)

**Goal shape**: `RelTriple oa ob R` or `RelTriple' oa ob R`

| Tactic | EasyCrypt analogue | What it does | Underlying rule |
|--------|--------------------|-------------|-----------------|
| `rel_step` | `seq` / `wp` | Decompose one `>>=` on each side, ask for intermediate relation | `relTriple_bind` |
| `rel_rnd` | `rnd` | Apply coupling for random oracle query or uniform sampling | `relTriple_query` / `relTriple_query_bij` / `relTriple_uniformSample_bij` |
| `rel_skip` | `skip` | Close trivial exact-coupling goals | `relTriple_refl` / `relTriple_eqRel_of_eq` |
| `rel_pure` | `skip` on `pure` | Close `pure`/`pure` goals directly | `relTriple_pure_pure` |
| `rel_cond` | `if` / `cond` | Split synchronized conditionals | `relTriple_if` |
| `rel_conseq` | `conseq` | Weaken/strengthen postconditions | `relTriple_post_mono` |
| `rel_inline` | `inline` | Unfold a definition and retry | `unfold` + `simp only [game_rule]` |
| `rel_sim` | `call` with invariant | Apply relational simulation rules | `relTriple_simulateQ_run` / `relTriple_simulateQ_run'` |
| `rel_sim_dist` | exact `call` | Apply exact per-query `evalDist` equality plus state equality | `relTriple_simulateQ_run'_of_impl_evalDist_eq` |
| `rel_replicate` | bounded `while` analogue | Lift per-iteration coupling through `replicate` | `relTriple_replicate` |
| `rel_mapM` | bounded traversal | Lift pointwise coupling through finite traversals | `relTriple_list_mapM` |
| `rel_foldlM` | bounded loop invariant | Use the goal postcondition as a fold invariant | `relTriple_list_foldlM` |

#### `rel_step` in detail

When the goal is `RelTriple (oa >>= fa) (ob >>= fb) S`:

1. Apply `relTriple_bind` to get two subgoals:
   - `RelTriple oa ob ?R` (user provides `R` or it's inferred)
   - `∀ a b, ?R a b → RelTriple (fa a) (fb b) S`
2. Introduce `a`, `b`, `hab` in the continuation goal.

**Interactive variant**: `rel_step using R` to specify the intermediate relation.

#### `rel_rnd` in detail

When both sides are `query t` or `$ᵗ T`:

1. Try `relTriple_query` (identity coupling) first
2. If that fails, try `relTriple_query_bij` and leave a bijection goal
3. For `$ᵗ T`, try `relTriple_uniformSample_bij`

**Interactive variant**: `rel_rnd using f` to specify the bijection.

### 3.3 Notation (Std.Do-inspired + EasyCrypt-inspired)

Activated via `open scoped OracleComp.ProgramLogic`.

| Notation | Expands to | Unicode input |
|----------|-----------|---------------|
| `⌜P⌝` | `propInd P` (1 if true, 0 if false) | `\ulc` `\urc` |
| `wp⟦c⟧` | `wp c` (partial apply) | `\[[` `\]]` |
| `⦃P⦄ c ⦃Q⦄` | `Triple P c Q` | `\{{` `\}}` |
| `g₁ ≡ₚ g₂` | `GameEquiv g₁ g₂` | `\equiv` + `\p` |
| `⟪c₁ ~ c₂ \| R⟫` | `RelTriple c₁ c₂ R` | `\<<` `\>>` |
| `⟪c₁ ≈[ε] c₂ \| R⟫` | `ApproxRelTriple ε c₁ c₂ R` | `\<<` `\approx` `\>>` |
| `⦃f⦄ c₁ ≈ₑ c₂ ⦃g⦄` | `eRelTriple f c₁ c₂ g` | `\{{` `\approx` `\e` `\}}` |

**Design notes:**
- `⦃⦄` notation uses `syntax` + `macro_rules` (not `notation`) because `⦃⦄`
  overlaps with Lean's strict-implicit binder syntax. Same approach as Std.Do.
- `⟪⟫` brackets for relational triples avoid ambiguity with `⟨⟩` (constructors).
- The `|` separator inside `⟪⟫` is unambiguous since the brackets delimit the expression.

### 3.4 Proof Mode Entry Tactics

| Tactic | What it does |
|--------|-------------|
| `by_equiv` | Transform `GameEquiv g₁ g₂` or `evalDist g₁ = evalDist g₂` into `RelTriple g₁ g₂ (EqRel α)` |
| `rel_dist` | Go back from exact coupling to distributional equality |
| `game_trans g₂` | Split a game hop through an intermediate game |
| `by_dist` / `by_dist ε` | Transform an advantage-bound goal into a TV-distance subgoal |
| `by_hoare` | Transform a probability goal into a quantitative WP goal |

`by_equiv` intentionally enters the coupling-based `RelTriple` shell, not `RelTriple'`, so
that the step-through tactics compose smoothly.

### 3.5 Bind Reordering Tactics

**Problem**: Swapping independent sampling operations is the #1 source of boilerplate in ElGamal (20+ instances).

**Pattern being automated:**
```lean
rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
refine tsum_congr fun x => ?_
congr 1
simpa [bind_assoc] using
  (probEvent_bind_bind_swap mx my f q)
```

**Tactics**:
- `prob_swap` — best-effort automation for the common bind-swap goal shapes; usually closes the goal.
- `prob_swap_rw` — rewrite-only variant for larger proofs that need to continue after the swap.
- `prob_congr` / `prob_congr'` — bind-congruence helpers for equality proofs under a shared outer bind.

## 4. Status And Remaining Plan

### What has already landed

1. **Semantic core**:
   - unary quantitative `wp` / `Triple`
   - coupling-based `RelTriple`
   - quantitative relational `eRelTriple` / `ApproxRelTriple`
2. **Notation and convenience layer**:
   - `⌜P⌝`, `wp⟦c⟧`, `⦃P⦄ c ⦃Q⦄`, `g₁ ≡ₚ g₂`, `⟪...⟫`
3. **Interactive tactic surface** in `VCVio/ProgramLogic/Tactics.lean`
4. **Coarse compatibility automation** in `VCVio/ProgramLogic/Notation.lean`
5. **Limited unary `Std.Do` bridge** in `VCVio/ProgramLogic/Unary/StdDoBridge.lean`
6. **Bounded-iteration tactic layer** for `replicate`, `List.mapM`, and `List.foldlM`
7. **Validation in real proofs**, especially `Examples/OneTimePad.lean` and `Examples/HHS_Elgamal.lean`

### Remaining work (recommended order)

1. **Consolidate documentation and module boundaries**
   - keep `Notation.lean` for notation, convenience predicates, and coarse compatibility macros
   - keep `Tactics.lean` as the canonical step-through proof mode
   - keep `StdDoBridge.lean` explicitly narrow and unary-only
2. **Add metaprogramming infrastructure**
   - goal-shape detection
   - controlled normalization / `whnf`
   - better diagnostics than `first` / `repeat` backtracking
3. **Upgrade the highest-value tactics**
   - stronger `rel_sim`
4. **Prototype unary structural VCGen**
   - extend beyond the current `hoare_step` / `hoare_seq` layer
   - continue broadening the new exhaustive `game_hoare` driver
   - target quantitative goals directly (`pre ≤ wp oa post`, `⦃P⦄ c ⦃Q⦄`)
   - use the current `Std.Do` bridge only as inspiration, not as the core engine
5. **Evaluate relational structural VCGen later**
   - only after the unary prototype and diagnostics exist
6. **Broaden bounded iteration further only if needed by examples**
   - `Fin.foldlM`, `Vector.mapM`, `Array.mapM`, and other thin wrappers
   - prioritize only the combinators that actually appear in EasyCrypt-style examples

## 5. Architecture

### File layout

```
VCVio/ProgramLogic/
  Unary/
    HoareTriple.lean    -- quantitative unary WP
    SimulateQ.lean      -- unary oracle-specific rules
    StdDoBridge.lean    -- narrow `.pure` Std.Do bridge
  Relational/
    Basic.lean          -- exact coupling pRHL shell
    Quantitative.lean   -- eRHL / apRHL layer
    SimulateQ.lean      -- relational oracle simulation
  Notation.lean         -- notation, convenience predicates, coarse compatibility macros
  Tactics.lean          -- canonical step-through proof mode
  TacticsExamples.lean  -- executable inventory of supported tactics
```

### Dependency order

```
Unary/{HoareTriple,SimulateQ} ┐
Relational/{Basic,Quantitative,SimulateQ} ──> Notation ──> Tactics
Unary/StdDoBridge ────────────────────────────────────────┘
```

If the tactic surface eventually grows past `Tactics.lean`, the natural split is to move
diagnostics and `elab_rules` helpers into submodules while keeping `Tactics.lean` as the
single user-facing import.

## 6. Comparison with EasyCrypt

We are no longer targeting a literal syntax-level compatibility layer. The current claim is
that VCV-io should match EasyCrypt's proof power on the terminating / bounded fragment, using
our own native tactic names and bounded combinators.

| EasyCrypt | VCV-io (current) | Notes |
|-----------|-------------------|-------|
| `proc` | `by_equiv` + `rel_inline` | Enter proof mode, then unfold as needed |
| `inline` | `rel_inline` | Same |
| `wp` | `rel_step` / `wp_step` | Step backward through program |
| `rnd` | `rel_rnd` | Random sampling coupling |
| `call` | `rel_sim` / `rel_sim_dist` | Use `rel_sim` for invariant-preserving simulation, `rel_sim_dist` for exact per-query oracle equivalence |
| `skip` | `rel_skip` / `rel_pure` | Trivial exact-coupling step |
| `swap` | `prob_swap` / `prob_swap_rw` | Reorder independent operations |
| `seq n : {R}` | `rel_step using R` | Split with intermediate relation |
| `if` | `rel_cond` | Synchronized branching |
| bounded `while {I}` patterns | `rel_replicate`, `rel_mapM`, `rel_foldlM` | Terminating/bounded fragment only; `rel_foldlM` uses the goal postcondition as the invariant |
| `sp` | (future) | Forward reasoning not yet available |
| `byequiv` | `by_equiv` | Enter coupling-based proof mode |
| `byphoare` | `by_hoare` | Enter quantitative proof mode |
| `auto` | `simp [game_rule]` / `grind` | Discharge side conditions |

### What Lean 4 enables that EasyCrypt cannot

1. **Dependent types**: State invariants can be type-level, not just assertions
2. **`do` notation**: Programs are written in familiar monadic syntax
3. **Custom elaborators**: Can build domain-specific proof automation
4. **Mathlib integration**: Full access to algebraic/analytic machinery
5. **`MAlgOrdered` generics**: Tactics work across transformer stacks automatically

## 7. Example: What a proof would look like

### Current (ElGamal, ~50 lines for one swap)
```lean
have hswap₁ :
    Pr[= true | stepDDH_realBranchGame ...] =
    Pr[= true | do ...] := by
  unfold stepDDH_realBranchGame stepDDH_realBranchCore
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun x => ?_
  congr 1
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  refine tsum_congr fun g₁ => ?_
  congr 1
  simpa [bind_assoc] using
    (probEvent_bind_bind_swap ...)
```

### Proposed (~3 lines)
```lean
have hswap₁ :
    Pr[= true | stepDDH_realBranchGame ...] =
    Pr[= true | do ...] := by
  unfold stepDDH_realBranchGame stepDDH_realBranchCore
  prob_swap ($ᵗ G) ($ᵗ Bool)
```

### Current (relational coupling, ~10 lines)
```lean
example : RelTriple (oa >>= fa) (ob >>= fb) S := by
  apply relTriple_bind _ (fun a b hab => _)
  · exact relTriple_query t
  · intro a b hab
    exact relTriple_eqRel_of_evalDist_eq (by ...)
```

### Proposed (~3 lines)
```lean
example : RelTriple (oa >>= fa) (ob >>= fb) S := by
  rel_step
  · rel_rnd
  · intro a b hab; rel_skip
```
