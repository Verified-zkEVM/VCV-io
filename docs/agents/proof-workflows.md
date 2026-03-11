# Proof Workflows

## Proof Strategy Decision Tree

**What are you trying to prove?**

1. **Two games have the same distribution** (`g₁ ≡ₚ g₂`):
   → `by_equiv` to enter relational mode, then use `rvcgen_step` / `rvcgen`
   → Add `using ...` when the current relational step needs an explicit witness

2. **Advantage is bounded** (`advantage ≤ ε`):
   → `by_dist` to enter TV distance reasoning
   → Use `by_dist ε₂` when you want to pin the TV-distance contribution explicitly
   → For identical-until-bad: use `tvDist_simulateQ_le_probEvent_bad`

3. **Probability equals a specific value** (`Pr[= x | oa] = ...`):
   → Start with `qvcgen_step` if the goal should lower or decompose automatically
  → Use `qvcgen_step?` when you want the explicit script, binder names, rewrite form, or an
    explicit `using` / `inv` / `with` step surfaced
   → Otherwise use `probOutput_bind_eq_tsum` to decompose binds manually
   → Use `simp` with project simp lemmas
   → Use `qvcgen_step`, `qvcgen_step rw`, or `qvcgen_step rw congr'` for probability equalities

4. **Multi-hop security proof** (`g₁ ≡ₚ gₙ`):
   → `game_trans g₂` to split into two goals, repeat

5. **Need to swap sampling order**:
   → Use `qvcgen_step` if the swap should close the goal
   → Use `qvcgen_step rw` (or `qvcgen_step rw under n`) if you need to continue after rewriting

## Game-Hopping Recipe

### Step 1: State the security theorem

```lean
theorem myScheme_secure :
    advantage (myExp adversary) ≤ q * ddhGuessAdvantage (myReduction adversary) := by
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
- `qvcgen_step` to close common probability-equality swaps
- `qvcgen_step rw congr'` to expose common random-sampling prefixes without support noise
- Telescope bound: `IND_CPA_advantage ≤ q * 2ε`

## Annotated Tactic Usage

### `by_equiv` + relational decomposition

```lean
-- Goal: g₁ ≡ₚ g₂
by_equiv                    -- now: ⟪g₁ ~ g₂ | EqRel α⟫
rvcgen_step using R         -- if needed, provide the bind cut relation
· rvcgen_step using f       -- couples the sampling step with a bijection
  · exact hf
  · intro x
    exact hR x
· intro a b hab
  subst hab
  rvcgen                    -- keep taking obvious relational steps
```

When there is exactly one viable local hypothesis that works as a `using` hint,
plain `rvcgen_step` and `rvcgen` will auto-consume it — no explicit `using` needed:

```lean
-- hf : ∀ a₁ a₂, S a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | R⟫ is the only viable hint
rvcgen                      -- auto-selects hf as the bind-cut relation
```

If there are 0 or ≥ 2 viable hints, the tactic keeps ambiguity explicit and
falls back to `EqRel`. Use `using` to disambiguate.

The relational finish pass also handles postcondition weakening automatically:

```lean
-- Goal: ⟪oa ~ ob | R'⟫ with h : ⟪oa ~ ob | R⟫ and hpost : ∀ x y, R x y → R' x y
rvcgen                      -- closes via relTriple_post_mono + assumption
```

```lean
-- Same workflow, but ask the tactic to surface the explicit script:
rvcgen_step?
```

On bind goals, the replay can now surface the full tuple naming form:

```lean
rvcgen_step using S as ⟨a1, a2, hrel⟩
```

### `qvcgen_step` on probability equalities

```lean
-- Goal: Pr[= true | do let x ← $ᵗ P; let b ← $ᵗ Bool; f x b]
--     = Pr[= true | do let b ← $ᵗ Bool; let x ← $ᵗ P; f x b]
qvcgen_step                -- closes the goal automatically
```

```lean
-- Same shape, but keep going after one rewrite:
qvcgen_step rw
```

### Naming and suggestion modes

```lean
-- Ask for the explicit next script and binder names:
qvcgen_step?
```

The surfaced script may now include:

```lean
qvcgen_step using cut
qvcgen_step inv I
qvcgen_step with triple_wrappedTrue
```

```lean
-- Keep the step, but force stable names for the new binders:
qvcgen_step as ⟨x⟩
```

```lean
-- Same idea on the relational side:
rvcgen_step using S as ⟨a₁, a₂, hrel⟩
```

### `qvcgen` driver variants

Use `qvcgen using cut` to perform one explicit bind step with an intermediate
postcondition, then continue with exhaustive decomposition:

```lean
-- Goal: ⦃1⦄ (do let x ← oa; let y ← f x; g y) ⦃post⦄
-- with hoa : ⦃1⦄ oa ⦃cut⦄ in context
qvcgen using cut            -- splits at first bind with `cut`, then auto-decomposes
```

Use `qvcgen inv I` to apply an explicit loop invariant to the first
`replicate`/`foldlM`/`mapM` goal, then continue:

```lean
-- Goal: ⦃pre⦄ oa.replicate n ⦃post⦄
-- with hstep : ⦃I⦄ oa ⦃fun _ => I⦄ in context
qvcgen inv I                -- applies invariant I, then auto-decomposes
```

### Support-cut synthesis

When decomposing a bind `oa >>= f`, if no explicit spec is available in context,
`qvcgen_step` and `qvcgen` will automatically try a support-based intermediate
postcondition. This applies `triple_bind` with `triple_support` as the spec for `oa`,
unifying the cut to `fun x => ⌜x ∈ support oa⌝`:

```lean
-- Goal: ⦃1⦄ (do let x ← oa; f x) ⦃post⦄
-- No spec for oa, but h : ∀ x ∈ support oa, ⦃...⦄ f x ⦃post⦄
qvcgen                      -- auto-inserts support cut, then decomposes f
```

### Opt-in unary theorem lookup

When a computation head is user-defined and not one of the built-in structural cases, register a
unary `Triple` lemma explicitly:

```lean
@[irreducible] def wrappedTrue : OracleComp spec Bool := pure true

@[vcgen] theorem triple_wrappedTrue :
    ⦃1⦄ wrappedTrue (spec := spec) ⦃fun y => if y = true then 1 else 0⦄ := by
  simpa [wrappedTrue] using
    (triple_pure (spec := spec) true (fun y => if y = true then 1 else 0))
```

After that, `qvcgen_step` can use the theorem when the goal head symbol is `wrappedTrue`.
The lookup is step-level and bounded: it runs after the built-in structural rules and only over
registered head-matching theorems.

You can also force a specific theorem or local assumption explicitly:

```lean
qvcgen_step with triple_wrappedTrue
```

If an exhaustive `qvcgen` / `rvcgen` run stops too early, raise the local pass budget with:

```lean
set_option vcvio.vcgen.maxPasses 128 in
  qvcgen
```

For tactic-choice debugging, enable the planned-step trace locally:

```lean
set_option vcvio.vcgen.traceSteps true in
  qvcgen_step
```

### `by_dist` for advantage bounds

```lean
-- Goal: AdvBound game ε
by_dist                     -- enters TV distance mode
-- now need to show tvDist ... ≤ ε
```

```lean
-- Same shape, but fix the TV-distance contribution first:
by_dist ε₂
```

## Asymptotic Security Reductions

For proofs involving asymptotic security (negligible advantage), use the lemmas in
`VCVio/CryptoFoundations/Asymptotics/Security.lean`.

### Tight reduction

```lean
exact secureAgainst_of_reduction hreduce hbound hsecure
```

where `hbound : ∀ A n, g.advantage A n ≤ g'.advantage (reduce A) n`.

### Polynomial-loss reduction

```lean
exact secureAgainst_of_poly_reduction hreduce hbound hsecure
```

where `hbound : ∀ A n, g.advantage A n ≤ ↑(loss.eval n) * g'.advantage (reduce A) n`.
Uses `negligible_polynomial_mul` under the hood.

### Game hop (absorb negligible difference)

```lean
exact secureAgainst_of_close hε hclose hsecure
```

where `hclose : ∀ A, isPPT A → ∀ n, g₁.advantage A n ≤ g₂.advantage A n + ε n`.

### Hybrid argument

```lean
exact secureAgainst_of_hybrid hε hconsec hsecure
```

Takes a chain of `k+1` games where consecutive games differ by at most `ε(n)`.
Proves by induction, applying `secureAgainst_of_close` at each step.

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
