# Milestones

## support_implies_chainInLog (proved 2026-05-06)

File: `VCVio/CryptoFoundations/MerkleTree/Inductive/Extractability.lean` (line 682)

Strategy used: unfold `extractability_game`, peel off three nested binds with
`OracleComp.withQueryLog_bind` + `mem_support_bind_iff` + `support_map`, finish
the inner `pure` with `OracleComp.withQueryLog_pure` + `mem_support_pure_iff`,
chain the resulting equalities `h_eq_co1 ↔ h_eq_v1 ↔ h_eq_p1 ↔ h_p1` to get a
single product equality, and break it via `Prod.mk.injEq` and `Sigma.mk.inj`
(needs `heq_eq_eq` after `subst h_idx_eq` to collapse the dependent leaf/proof
heqs into ordinary equalities). Then `verifyProof_run_support_chain` gives a
chain in `log_v`, lifted to the full log via `chainInLog_mono` and three
`List.mem_append_right` invocations.

Verification: `lake build VCVio.CryptoFoundations.MerkleTree.Inductive.Extractability` succeeds; only 2 pre-existing warnings, no new sorries.

Remaining sorries in this file (out of scope for this run): in
`extractability_game_no_coll_match` (lines 755, 758) and
`extractability_game_noColl_caseB_le_inv_card` (line 969).
