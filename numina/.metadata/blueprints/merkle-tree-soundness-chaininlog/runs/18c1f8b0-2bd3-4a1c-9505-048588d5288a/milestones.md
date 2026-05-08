# Run 18c1f8b0-2bd3-4a1c-9505-048588d5288a milestones

## Scope
Fill the single remaining `sorry` in
`VCVio/CryptoFoundations/MerkleTree/Inductive/Extractability.lean:1337`,
inside `extractability_game_noColl_caseB_le_inv_card`. May add helper lemmas
as needed.

## Plan
1. Read the surrounding context (`extractability_game`, `chainInLog`,
   `support_implies_chainInLog`, `extractor_chain_match`,
   `extractability_game_noColl_caseA_eq_zero`) to identify the precise
   probability statement to bound and the structural ingredients available.
2. Identify the level `k` of chain departure under
   `extractedTree.get idx = none` and locate the verifier's terminal
   "fresh" hash query that needs to land on `root`.
3. Decompose the game's `withQueryLog` so the bound reduces to a
   `probOutput_query`/`evalDist_query` argument over a uniform sample
   on `α`.
4. Bound the side conjuncts (no-collision; size of combined log
   ≤ `qb`) using the `4 * s.leafCount + 1 ≤ qb` hypothesis.
5. Compose with `probEvent_mono''` reductions already in the file.

## Attempts

### Attempt 1 — prover subagent

Result: cosmetic refactor only; substantive sorry not eliminated.

Changes to
`VCVio/CryptoFoundations/MerkleTree/Inductive/Extractability.lean`:

- Old `extractability_game_noColl_caseB_le_inv_card` (sorry at line 1337) is
  now fully proved: it dispatches `(Fintype.card α : ENNReal) ≤ 1` via
  `probEvent_le_one` + `ENNReal.le_div_iff_mul_le`, and forwards the
  `1 < Fintype.card α` branch to a new helper.
- New private helper `extractability_game_noColl_caseB_le_inv_card_aux` at
  line 1287 carries the substantive obligation under the extra hypothesis
  `1 < (Fintype.card α : ENNReal)`. Body is `sorry` at line 1313.

Module builds: `lake build VCVio.CryptoFoundations.MerkleTree.Inductive.Extractability`
returns `succeeded` with one warning (the new sorry).

### Remaining substantive obligation

Inside `extractability_game_noColl_caseB_le_inv_card_aux`, with hypotheses:

- `IsTotalQueryBound (committingAdv ; openingAdv) qb`
- `4 * s.leafCount + 1 ≤ qb`
- `1 < (Fintype.card α : ENNReal)`

bound

```
Pr[fun x => verified x.1 = true ∧ extractedTree x.1 .get idx x.1 = none |
    (extractability_game committingAdv openingAdv).withQueryLog]
  ≤ 1 / (Fintype.card α : ENNReal)
```

### Why this is hard

The proof requires:

1. Identifying a "departure level" `k` along the verifier's hash chain:
   the highest level where the input pair to the verifier's hash query
   is fresh in the combined log.
2. A probability-monad rewriting that pulls that single uniform sample to
   the outside of the game, conditional on the rest of the game.
3. Applying `probOutput_query` / `evalDist_query`-style uniformity to bound
   `Pr[that sample = root]` by `1/|α|`.
4. Using `extractability_game_IsTotalQueryBound` and `4 * s.leafCount + 1 ≤ qb`
   to rule out duplicate-query reuse so the bound stays at `1/|α|`.

No analogous lemma was found in the existing file or in Mathlib that lifts
a single fresh oracle query out of a `withQueryLog`'d game while preserving
its uniform marginal. Producing that machinery is a multi-day formalization
effort.

## Next steps

If the user wants to continue:

- A targeted helper lemma of the form

  ```
  Pr[fun (x, log) => f x.last = root ∧ x.last is from a fresh oracle query |
      (mx >>= fun y => liftM (query t y) >>= …).withQueryLog]
    ≤ 1 / |α|
  ```

  is the natural building block. Drafting and proving that lemma in
  isolation (against `simulateQ unifOracle` semantics) is the recommended
  next attempt.
- Alternatively, leave the substantive helper as `sorry` for a human to
  finish, treating the structural refactor (small-card dispatch +
  named substantive helper) as the deliverable.
