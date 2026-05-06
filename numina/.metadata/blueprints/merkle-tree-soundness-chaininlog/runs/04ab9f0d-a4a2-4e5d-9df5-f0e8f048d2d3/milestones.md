# Milestones

## extractability_game_no_coll_match (proved 2026-05-06)

File: `VCVio/CryptoFoundations/MerkleTree/Inductive/Extractability.lean`
Theorem now at line 1045.

The two internal `sorry`s on `h_extracted_tree_eq` and `h_extracted_proof_eq`
were closed by refactoring the proof body to use `log_c` (the committingAdv's
log) directly with `extractor_chain_match`, instead of trying to bridge
`extractor s log_c root = extractor s log root` (which is false off-path).

The signature of `extractability_game_no_coll_match` is unchanged.

### New helpers added

- `populate_down_none_get_eq_none` (private, line 754)
- `extractorChildren` (private def, line 776)
- `extractor_eq_populate` (private, line 790)
- `extractorChildren_some` (private, line 795)
- `chainInLog_restrict` (line 807): chain restriction from full log to the
  committing prefix, under no-collision and intactness of the extractor path.
- `withQueryLog_self_log_eq` (line 957): bridges inner/outer logs of a
  doubly-applied `withQueryLog`.

### Build verification

`mcp__build-tools__build_module VCVio.CryptoFoundations.MerkleTree.Inductive.Extractability`
returns `succeeded` with 1 warning (the remaining unrelated Case B sorry on line 1337).

## Remaining sorry

- `extractability_game_noColl_caseB_le_inv_card` (line 1337) — out of scope for this run.
