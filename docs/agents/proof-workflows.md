# Proof Workflows

## Proof Strategy Decision Tree

**What are you trying to prove?**

1. **Two games have the same distribution** (`g₁ ≡ₚ g₂`):
   → `by_equiv` to enter relational mode, then use `rel_step` / `rel_rnd` / `rel_skip` / `rel_pure`
   → For simple cases: `game_rel'` (exhaustive automated prover)

2. **Advantage is bounded** (`advantage ≤ ε`):
   → `by_dist` to enter TV distance reasoning
   → For identical-until-bad: use `tvDist_simulateQ_le_probEvent_bad`

3. **Probability equals a specific value** (`Pr[= x | oa] = ...`):
   → Start with `probOutput_bind_eq_tsum` to decompose binds
   → Use `simp` with project simp lemmas
   → Use `prob_swap` to reorder independent binds

4. **Multi-hop security proof** (`g₁ ≡ₚ gₙ`):
   → `game_trans g₂` to split into two goals, repeat

5. **Need to swap sampling order**:
   → `prob_swap` (or `prob_swap_at n` for multiple swaps)

## Game-Hopping Recipe

### Step 1: State the security theorem

```lean
theorem myScheme_secure :
    advantage (myExp adversary) ≤ q * ddhAdvantage (myReduction adversary) := by
```

### Step 2: Define intermediate games (hybrids)

```lean
def hybridGame (adversary : ...) (k : ℕ) : ProbComp Bool := do
  -- first k queries use real, rest use random
  ...
```

### Step 3: Telescope via `game_trans`

```lean
  game_trans (hybridGame adversary 1)
  · -- prove hybridGame 0 ≡ₚ hybridGame 1
    by_equiv
    ...
  · game_trans (hybridGame adversary 2)
    · ...
```

### Step 4: Per-hop reduction

For each hop, build a reduction adversary that embeds the DDH challenge at position k:

```lean
def stepReduction (adversary : ...) (k : ℕ) : DDHAdversary F G :=
  fun x x₁ x₂ x₃ => do
    -- use (x, x₁) as public key
    -- at query k, return (x₂, msg * x₃) instead of encrypting
    ...
```

### Step 5: Prove per-hop equivalence

Show that DDH-real corresponds to hybrid k and DDH-random corresponds to hybrid k+1.

## Worked Example: OneTimePad Privacy

From `Examples/OneTimePad.lean` — the canonical complete proof.

**Setup**: OTP encrypts by XOR with a random key.

```lean
def OTP_keyGen : ProbComp (Fin n → Bool) := $ᵗ (Fin n → Bool)
def OTP_encrypt (k m : Fin n → Bool) : ProbComp (Fin n → Bool) := pure (k + m)
```

**Privacy proof sketch**:
1. The ciphertext `c = k + m` where `k` is uniform
2. By group theory, `k + m` is uniform for any fixed `m`
3. So `Pr[= c | encrypt k m₁] = Pr[= c | encrypt k m₂]` for all `c`

**Key technique**: `probOutput_map_injective` — if the encryption map is injective (which XOR is), the probability is preserved.

## Worked Example: ElGamal IND-CPA

From `Examples/ElGamal.lean` — multi-query security via DDH.

**Key patterns used**:
- Hybrid argument indexed by query count `k`
- `StateT` for oracle implementations that track query counter + cache
- `prob_swap` to reorder independent sampling (13 instances)
- `probOutput_bind_congr` to factor out common prefixes
- Telescope bound: `IND_CPA_advantage ≤ q * 2ε`

## Annotated Tactic Usage

### `by_equiv` + relational decomposition

```lean
-- Goal: g₁ ≡ₚ g₂
by_equiv                    -- now: ⟪g₁ ~ g₂ | EqRel α⟫
rel_step                    -- decomposes the outermost bind
· rel_rnd                   -- couples the sampling step
· intro a b hab             -- hab : a = b (from EqRel)
  subst hab
  rel_step
  · rel_skip                -- identical sub-computations
  · intro x y hxy
    rel_pure                -- both return pure values
```

### `prob_swap` in context

```lean
-- Goal: Pr[= true | do let x ← $ᵗ P; let b ← $ᵗ Bool; f x b]
--     = Pr[= true | do let b ← $ᵗ Bool; let x ← $ᵗ P; f x b]
prob_swap                   -- closes the goal automatically
```

### `by_dist` for advantage bounds

```lean
-- Goal: AdvBound game ε
by_dist                     -- enters TV distance mode
-- now need to show tvDist ... ≤ ε
```

## Parallel Agent Workflow

When parallelizing proof work across multiple agents, use one `git worktree` per task so
each agent gets an isolated checkout:

```bash
git worktree add ../vcv-task-a HEAD
git worktree add ../vcv-task-b HEAD
```

Guidelines:

- Keep same-file follow-up tasks sequential rather than parallel.
- Merge the first wave before dispatching dependent follow-up tasks.
- Prefer one prompt or one proof chunk per worktree to reduce conflicts.
- Keep committed prompt files available to all worktrees if downstream agents need them.

This pattern is especially useful for sorry-filling and multi-file proof searches.

## Reference-First Workflow

For relational logic work, consult
*A Quantitative Probabilistic Relational Hoare Logic* ([ERHL25](../../REFERENCES.md#erhl25))
before changing definitions or tactics for eRHL, pRHL, or apRHL.

## Debugging Common Stuck States

### "typeclass instance problem ... Monad (OracleQuery spec)"
You wrote `evalDist (query t)` but `query t : OracleQuery`, not `OracleComp`. Fix: `evalDist (liftM (query t) : OracleComp spec _)`.

### "failed to synthesize ... spec.Fintype"
Add `[spec.Fintype]` and `[spec.Inhabited]` to your hypotheses. These are required for all probability reasoning.

### Universe mismatch around `SubSpec`
`OracleComp` has 3 universe parameters, `SubSpec` has 6. Use `{ι : Type*}` instead of `{ι : Type u}` to let universes resolve independently.

### `simp` makes no progress on `probOutput`
`probOutput_bind_eq_tsum` is `@[grind =]` but not `@[simp]`. Use `rw [probOutput_bind_eq_tsum]` or `grind` instead of `simp`.

### Aggressive unfolding of `OracleComp`
Core types are `@[reducible]`. Lean may unfold `OracleComp` to `PFunctor.FreeM`. Use `OracleComp.inductionOn` as the canonical eliminator, not pattern matching on `PFunctor.FreeM.pure`/`roll`.
