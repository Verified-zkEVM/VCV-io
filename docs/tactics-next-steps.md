# Program Logic Tactics Next Steps

This note records the next tactical improvements after the systematic planner-performance pass on
`quang/tactics-systematic-perf`.

## Immediate Work

1. Add opt-in timing for the VCVio tactic planner.
   Track structural stepping, `@[wpStep]` dispatch, probability-equality planning, local-hint probing,
   registered theorem probing, close passes, and whole-pass time.

2. Use the timing data to pick the next implementation target.
   The first sweep shows relational hint/proof-search work is the next bottleneck, not unary
   probability-equality planning.

3. Productionize the unified backward-rule spike.
   `VCVio/ProgramLogic/Tactics/Experimental/UnifiedLSpecBackward.lean` already demonstrates
   matching and applying unified entries.
   The next step is to add a cached backward-rule path, modeled on Loom2's
   `mkBackwardRuleFromSpecCached`, and wire it side by side for a narrow rule class.

4. Replace probability-equality plan enumeration with a bind-spine planner.
   Instead of previewing many bounded rewrite/congruence sequences, classify the
   `probEvent`/`probOutput` bind spine directly, compute shared prefixes and the required adjacent
   swaps, then emit the same explicit replay text.

5. Move toward a pass-local worklist state.
   Loom2's `mvcgen'` keeps tactic state, caches, and worklist traversal together.
   VCVio should port that architectural shape without making `Std.Do`/`mvcgen` the main engine.

6. Factor a shared computation-spine classifier.
   Unary and relational VCGen currently duplicate head checks for binds, iteration combinators,
   `simulateQ`, maps, and conditionals.
   A shared spine would improve diagnostics, `simulateQ` automation, and candidate ranking.

## Constraints

- Keep `qvcgen`/`rvcgen` as the primary engine for VCVio's quantitative and relational goals.
- Keep `Std.Do` integration as an optional side path until the upstream tooling makes it cheap.
- Prefer measured planner changes over further speculative probing reductions.

## First Timing Sweep

Collected with `lake env lean -Dvcvio.vcgen.time=true ...` after the timing hooks landed.

- Unary examples are cheap: `Examples/ProgramLogic/UnaryTriple.lean` spent about `32ms` total in
  pass loops across 11 `vcgen` runs, and `Examples/ProgramLogic/Probability.lean` spent only
  about `3ms` in probability planning.
- Relational local-hint scanning dominates several small examples:
  `Examples/ProgramLogic/RelationalStep.lean` spent about `434ms` in local hints for one `rvcgen`,
  `VCVio/ProgramLogic/Relational/Examples.lean` spent about `291ms`, and
  `Examples/ProgramLogic/ProofMode.lean` spent about `125ms`.
- Relational registered-theorem probing dominates `Examples/ProgramLogic/RelationalDerived.lean`:
  about `434ms` in registered probing, `196ms` in local hints, and `233ms` in the final consequence
  close pass.
- Larger crypto examples with `rvcgen`, including `Examples/OneTimePad/LeakageFree.lean` and
  `Examples/Schnorr.lean`, were cheap under these hooks, around `5ms` per `rvcgen`.

## Measured Next Targets

1. Try relational close/consequence before registered-theorem probing.
   `RelationalDerived.lean` shows a consequence-close goal paying for a registered theorem scan before
   the finish pass closes it.
   A cheap `tryCloseRelGoalConseq` attempt before `@[vcspec]` fallback should remove that cost.

2. Move automatic relational local-hint scanning after the structural attempt, or gate it more tightly.
   Several plain `rvcgen` examples pay hundreds of milliseconds scanning local hypotheses even when
   structural rules or leaf closers can solve the goal.
   Explicit `rvcgen using ...` can remain the eager path for user-provided hints.

3. Add cheap shape/type prefilters for relational `using` candidates.
   The current scan tests candidate terms by replaying `runRVCGenCoreUsing` under saved state.
   A prefilter keyed by goal shape should avoid trying continuation proofs as bind-cut relations and
   avoid trying non-bijections on random/query goals.

4. Then revisit registered-theorem application through the unified backward-rule spike.
   Once the avoidable scans are gone, cached backward rules from
   `Experimental/UnifiedLSpecBackward.lean` become the right next target.

5. Keep the probability bind-spine planner on the backlog.
   The first sweep did not show it as the current bottleneck, but it remains valuable for proof
   ergonomics and larger probability-equality proofs.

## Implemented Follow-Up

The first measured pass above has now been turned into two focused relational changes.

- `rvcgen` now tries the cheap relational consequence closer before falling back to registered
  `@[vcspec]` theorem probing.
  The follow-up timing run on `Examples/ProgramLogic/RelationalDerived.lean` shows `registered=0ms`
  on the previously expensive consequence-close path.
- Automatic local-hint discovery now first reuses postconditions from already-proven top-level local
  relational triples, such as `hoa : ⟪oa₁ ~ oa₂ | S⟫`, before falling back to the older saved-state
  replay validation.
  This preserves the existing ambiguity checks while avoiding replay for the common bind-cut pattern.
- The second timing run on `Examples/ProgramLogic/RelationalStep.lean` reduced the main local-hint
  hotspot from about `460ms` to `0ms`.
  One proof-mode example still reports about `139ms` in local hints, so the next measured target is a
  stricter goal-shape/type filter for fallback hint candidates rather than another broad planner pass.
