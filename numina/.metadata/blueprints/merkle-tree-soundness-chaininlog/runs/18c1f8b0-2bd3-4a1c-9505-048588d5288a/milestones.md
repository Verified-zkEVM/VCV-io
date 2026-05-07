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
(to be filled by subagent runs)
