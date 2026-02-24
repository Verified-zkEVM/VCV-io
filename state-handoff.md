# State Handoff

- **Handoff reason:** context limit
- **Summary:** Implementing the "EvalDist API Completion" plan — porting commented-out `OracleComp`-specific probability lemmas to generic `[HasEvalSPMF m]` typeclass. Stream 1 (core identities) is complete. Stream 2 (bind congr/mono) and Stream 4a/4b (Bool/Prod specializations) are written but have build errors in `Monad/Basic.lean` that block everything downstream.
- **Goal and scope:** Complete all streams in the plan at `/Users/quang.dao/.cursor/plans/evaldist_api_completion_f319311f.plan.md`. Port all commented-out `OracleComp` lemmas to generic monad `[HasEvalSPMF m]`.

## Current state: **broken** (5 build errors in `Monad/Basic.lean`)

## Work completed

### Stream 1 — DONE, builds clean
- `VCVio/EvalDist/Defs/Basic.lean:638-720` — Added `probEvent_mono`, `probEvent_mono'`, `probEvent_compl`, `probEvent_eq_one_iff`, `one_eq_probEvent_iff`, plus `finSupport` variants. All build successfully.

### Stream 2 — Written, 5 build errors
- `VCVio/EvalDist/Monad/Basic.lean:323-471` — Added `mul_le_probEvent_bind`, `probFailure_bind_congr`/`'`, `probOutput_bind_congr`/`'`, `probOutput_bind_mono`, `probOutput_bind_congr_div_const`, `_eq_add`, `_le_add`, `_add_le`, `_le_sub`, `_sub_le`.
- The following lemmas build clean: `probFailure_bind_congr`, `probOutput_bind_congr`, `probOutput_bind_mono`, `probOutput_bind_congr_eq_add`, `probOutput_bind_congr_le_add`, `probOutput_bind_congr_add_le`, `probOutput_bind_congr_sub_le`.

### Stream 4a (Bool) — Written, not independently tested
- `VCVio/EvalDist/Bool.lean` — 6 lemmas. Imports `Monad/Map` which doesn't depend on `Monad/Basic`, so it *might* build independently, but `lake build` pulls in `Monad/Basic` errors transitively.

### Stream 4b (Prod) — Written, not independently tested
- `VCVio/EvalDist/Prod.lean` — 9 lemmas replacing old commented-out code. Same transitive error issue.

## Files modified (relative to `HEAD~1`)

| File | Changes |
|---|---|
| `VCVio/EvalDist/Defs/Basic.lean` | Replaced ~65 lines of commented-out code with ~85 lines of working proofs (section `probEvent_mono_compl`) |
| `VCVio/EvalDist/Monad/Basic.lean` | Replaced ~103 lines of commented-out code with ~152 lines (section `congr_mono`), 5 errors remain |
| `VCVio/EvalDist/Bool.lean` | Replaced 2 commented-out lemmas with 6 new generic lemmas |
| `VCVio/EvalDist/Prod.lean` | Replaced ~122 lines of commented-out code with 76 lines of ported lemmas |

## Context files (not modified, important to read)

- `VCVio/EvalDist/Defs/Basic.lean` — all the core definitions (`probOutput`, `probEvent`, `probFailure`, `support`, `finSupport`) and their basic properties
- `VCVio/EvalDist/Monad/Map.lean` — `probOutput_map_eq_tsum_ite`, `probOutput_map_injective` (used by Bool/Prod)
- `VCVio/EvalDist/Instances/OptionT.lean` — pattern for how monad transformer instances are done (needed for Stream 3a ExceptT)
- `VCVio/EvalDist/Monad/Seq.lean` — Stream 3b target (all commented out)
- `VCVio/EvalDist/Monad/Alternative.lean` — Stream 3c target (all commented out)
- `VCVio/EvalDist/Instances/ErrorT.lean` — Stream 3a target (all commented out)
- `VCVio/EvalDist/List.lean` — Stream 4e target
- `/Users/quang.dao/.cursor/plans/evaldist_api_completion_f319311f.plan.md` — the full plan

## Blockers / Errors

**5 errors in `VCVio/EvalDist/Monad/Basic.lean`**, all in the `congr_mono` section:

### Error 1: `mul_le_probEvent_bind` (line 334)
```
mul_le_mul_left h
has type: ∀ (a : ℝ≥0∞), r * a ≤ Pr[p | mx] * a
expected: r * r' ≤ Pr[p | mx] * r'
```
**Fix:** `mul_le_mul_left h` produces a function, not a term at the right type. Use `mul_le_mul_right' h r'` instead, or apply it as `(mul_le_mul_left h) r'`.

### Error 2: `mul_le_probEvent_bind` (line 343)
```
zero_le ?m.214
has type: 0 ≤ ?m.214
expected: 0 * r' ≤ Pr[=x | mx] * Pr[q | my x]
```
**Fix:** `zero_le` doesn't unify because `0 * r'` isn't reduced to `0`. Use `by simp` or `by rw [zero_mul]; exact zero_le _`.

### Error 3: `probOutput_bind_congr_div_const` (line 391)
```
Unknown constant `ENNReal.tsum_div`
```
**Fix:** This constant doesn't exist in Mathlib. The correct approach is to rewrite `_ / r` as `_ * r⁻¹`, use `ENNReal.tsum_mul_right`, and then convert back. Alternatively, use `div_eq_mul_inv` and `tsum_mul_right`.

### Error 4: `probOutput_bind_congr_div_const` (line 389)
```
unsolved goals (related to Error 3)
```

### Error 5: `probOutput_bind_congr_le_sub` (line 455)
```
Unknown constant `ENNReal.tsum_sub_le_of_le`
```
**Fix:** This constant doesn't exist in Mathlib. The correct approach needs investigation. Options:
- Look for `ENNReal.tsum_sub` or similar in Mathlib (search for `tsum.*sub` in the `ENNReal` namespace)
- Use `ENNReal.le_sub_of_add_le` and restructure the proof
- Use `sorry` temporarily and come back to it

## Deleted code that was NOT replaced

### From `Prod.lean` — deleted and NOT ported:
These were in a `section seq_map_mk` block and depend on `Seq` lemmas (Stream 3b) which haven't been ported yet:
- `probOutput_seq_map_prod_mk_eq_mul` (independence for seq)
- `probOutput_seq_map_prod_mk_eq_mul'` (swap variant)
- `probOutput_seq_map_vec_push_eq_mul` (vector variant)
- `probEvent_seq_map_prod_mk_eq_mul` (event version)
- `probEvent_seq_map_prod_mk_eq_mul'` (swap variant)

And a `section mk_subsingleton`:
- `fst_map_prod_mk_of_subsingleton`
- `snd_map_prod_mk_of_subsingleton`

**These should be added back** after Stream 3b (Seq lemmas) is ported, or added as commented-out TODOs.

### From `Bool.lean` — deleted, replaced with better equivalents:
- `probOutput_true_eq_probOutput_false_not` — replaced by `probOutput_not_map` (more general)
- `probOutput_false_eq_probOutput_true_not` — replaced by `probOutput_not_map'` (more general)

### From `Defs/Basic.lean` — deleted, already existed elsewhere:
- `mem_support_iff_probOutput_ne_zero` — equivalent to existing `probOutput_eq_zero_iff` (line 95)
- `mem_support_iff_probOutput_pos` — equivalent to existing `probOutput_pos_iff` (line 115)
- `not_mem_support_iff_probOutput_eq_zero` — equivalent to existing `probOutput_eq_zero_iff` (line 95)
- `function_support_probOutput` — not ported (trivial simp lemma about Function.support)
- `mem_support_iff_of_evalDist_eq` — not ported (OracleComp-specific, compares two different `spec`)
- `mem_finSupport_iff_of_evalDist_eq` — not ported (same reason)

## Key decisions and rationale

1. **Generic `[HasEvalSPMF m]` over `OracleComp`**: All ported lemmas use the generic typeclass instead of `OracleComp spec α`, as per the overall API design direction.
2. **`Classical.decPred p`**: Used for `probEvent_eq_tsum_ite` which requires decidability. The old proofs used `Set.indicator` but the new API uses `if-then-else` in tsums.
3. **`probOutput_eq_zero_of_not_mem_support`**: Used instead of `probOutput_eq_zero` pattern for the support case split (cleaner than `simp [probOutput_eq_zero_iff, ...]`).

## Open questions / Risks

1. **`ENNReal.tsum_div`**: Need to find the correct Mathlib lemma for distributing division into a tsum. Might not exist — may need `div_eq_mul_inv` + `tsum_mul_right`.
2. **`ENNReal.tsum_sub_le_of_le`**: Need the right lemma for `∑(aᵢ - bᵢ) ≤ ∑aᵢ - ∑bᵢ` (or the reverse). This is a delicate `ENNReal` inequality. Search Mathlib for `tsum_sub`.
3. **Bool.lean and Prod.lean proofs**: Written but never successfully built — may have additional errors once `Monad/Basic.lean` is fixed.
4. **Deleted `Prod.lean` seq lemmas**: These need to be added back after Stream 3b, or at least restored as comments with a TODO.

## Cleanup needed

- No debug prints or temporary hacks, but 2 broken proofs need fixing (Errors 3 and 5 above)
- The deleted `Prod.lean` seq lemmas should be restored as comments with `-- TODO: port after Seq lemmas (Stream 3b)` or ported once Seq is done

## Tests and commands run

| Command | Result |
|---|---|
| `lake build VCVio.EvalDist.Defs.Basic` | PASS |
| `lake build VCVio.EvalDist.Monad.Basic` | FAIL (5 errors) |
| `lake build VCVio.EvalDist.Bool` | FAIL (transitive from Monad/Basic) |
| `lake build VCVio.EvalDist.Prod` | FAIL (transitive from Monad/Basic) |

## Next steps

1. **Fix the 5 errors in `Monad/Basic.lean`** (see fixes above — Errors 1-2 are straightforward, Errors 3-5 need Mathlib API investigation)
2. **Build `Bool.lean` and `Prod.lean`** and fix any independent errors
3. **Restore deleted `Prod.lean` seq lemmas as comments** with TODO for Stream 3b
4. **Implement Stream 3a**: ExceptT `HasEvalSPMF` instance (follow `OptionT.lean` pattern)
5. **Implement Stream 3b**: Seq probability lemmas
6. **Implement Stream 3c**: Alternative lemmas
7. **Implement Stream 4e**: List NeverFails lemmas
8. **Final cleanup pass**: Remove dead code, verify full `lake build`

## How to resume

1. Read `VCVio/EvalDist/Monad/Basic.lean:327-470` to see the broken proofs
2. Fix `mul_le_probEvent_bind` (lines 334, 343) — apply `mul_le_mul_right'` and fix `zero_le` pattern
3. For `probOutput_bind_congr_div_const` (line 391), search Mathlib: try `div_eq_mul_inv` + `ENNReal.tsum_mul_right`
4. For `probOutput_bind_congr_le_sub` (line 455), search for `ENNReal.tsum_sub` or restructure proof

## Branch

```
quang/evaldist-api-completion (tracking origin/quang/evaldist-api-completion)
```

1 commit ahead, 0 behind. No stashes. No untracked files.
