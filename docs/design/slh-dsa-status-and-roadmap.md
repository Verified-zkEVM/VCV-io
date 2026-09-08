# SLH-DSA formalization: status and roadmap

Status: implementation-status report and forward roadmap, established 2026-09-06. It complements
the plan in [`slh-dsa-fips205-generalization.md`](slh-dsa-fips205-generalization.md), which fixes
the target architecture, milestone definitions, acceptance gates, and merge protocol established
on 2026-08-30. This document records what has merged since, what is open, where the plan's snapshot
statements are now stale, and the ordered slices that remain. For the `main` snapshot identified in
the milestone ledger below, use this document rather than the plan's older status statements.

A capability is listed as DONE only when its source and validation are on `main`. Open pull
requests are named as such. No item below should be read as an SLH-DSA security theorem: no
SLH-DSA unforgeability theorem of any kind exists on `main` at the recorded snapshot.

## Where the work lives

| Area | Modules | Validation |
|---|---|---|
| Parameters, positions, addresses, primitive interfaces | `HashSig/SLHDSA/Params.lean`, `FipsParams.lean`, `Position.lean`, `Address.lean`, `Encoding.lean`, `EncodingLemmas.lean`, `Primitives.lean` | `HashSigTest/SLHDSA/Params.lean`, `Position.lean` |
| Components (WOTS+, XMSS, FORS) | `Wots.lean`, `WotsChecksum.lean`, `WotsEncoding.lean`, `Xmss.lean`, `Fors.lean`, `*Conformance.lean`, `Concrete/{Wots,Xmss,Fors,Hypertree}.lean` (checked SHA-2 address domains) | `slhdsa_wots_tests`, `slhdsa_xmss_tests`, `slhdsa_fors_tests`, `HashSigTest/SLHDSA/{Wots,WotsEncoding,Xmss,Fors}.lean` |
| General hypertree and scheme | `HypertreeGeneral.lean` (+ `QueryBound.lean`), `GeneralScheme.lean`, `GeneralSchemeQueryBound.lean`, `DepthOneCompatibility.lean` | `slhdsa_hypertree_tests`, `HashSigTest/SLHDSA/HypertreeGeneral.lean`, `GeneralScheme.lean` |
| Depth-one compatibility scheme | `Hypertree.lean`, `Scheme.lean`, `RandomOracle.lean`, `Oracle.lean` | `HashSigTest/SLHDSA/Hypertree.lean`, `Oracle.lean`, `Scheme.lean` |
| Wire codecs | `Codec.lean`, `Concrete/Codec.lean` | `slhdsa_data_codec_tests` |
| Concrete primitives (12 FIPS sets) | `Concrete/Sha2.lean`, `Concrete/Keccak.lean`, `Concrete/FIPS.lean`, `Concrete/Instance.lean`, `Concrete/Prehash.lean` | `slhdsa_primitive_tests` (+ `PrimitiveVectors/`), `slhdsa_kat` |
| C13 variant (WOTS+C/FORS+C, keccak256, `d = 2`) | `C13/{Params,Primitives,WotsC,ForsC,Xmss,Hypertree,Scheme,Concrete}.lean` | `slhdsa_c13_kat` |
| External interfaces (Alg. 21–25) | `External.lean` | `slhdsa_external_tests` |
| Security packaging | `Security.lean` (primitive families as `TweakableHash`/`PRFScheme`), `MerkleExtractor.lean` | — |
| Security lane, slices 1–4 (on `main`) | `Security/TargetCounts.lean`, `Security/ReachableTargets.lean` (#630); `Security/EncodedTargets.lean` (#631); `WotsInjectivity.lean` (#665); `Security/TraceTargets.lean` (#666) | `slhdsa_target_ledger_tests`, `slhdsa_encoded_ledger_tests`, `slhdsa_trace_target_tests` |
| Security lane, slices 5–6 (branches only, not on `main`) | `Security/ComponentTraces.lean` on `feat/slhdsa-d1a-component-traces-20260907`; `Security/CanonicalGames.lean` on `feat/slhdsa-d1a-canonical-games-20260907` | `slhdsa_component_trace_tests`, `slhdsa_canonical_game_tests` (on those branches) |
| Generic hash games consumed | `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/*.lean`, `KeyedHash/ITSR.lean`, `VCVio/CryptoFoundations/SignatureAlg.lean` | `VCVioTest/SMDT*.lean` |

Every SLH-DSA test executable runs in `.github/workflows/build.yml`, and the test modules that
have no executable are compiled by its `lake build HashSigTest` step; `linting.yml` runs
`lake exe lint-style` over `HashSig` and a list of test modules (issue #629 item 4 records that
the workflow lints the imports of the listed modules rather than the named modules themselves);
`scripts/check-expose-boundary.sh` caps the number of broadly exposed files per library (new
modules use a plain `public section` with per-declaration `@[expose]`);
`lake exe axiomsweep --check` guards the axiom and `sorry` footprint against
`scripts/axiom_baseline.json`.

## Milestone status ledger

Verified against `origin/main` at `41ead835` (2026-09-08).

| Milestone | Status | Landed in | Realized by | Gap against the plan's wording |
|---|---|---|---|---|
| G1 valid parameters, all FIPS sets | DONE | #593 | `Params`, `Params.Valid`, `ValidatedParams`, `FipsParameterSet` (12), `LimitedParameterSet`, `FipsParams` | none |
| G2 digest and layer-index calculus | DONE | #595 | `DigestParts`, `splitDigest`, `LayerPosition` (`initial`, `next`, `atLayer`, `toAdrs`), `forsAdrs` | layer is a field of `LayerPosition`, not an index; an allowed normalization |
| G3 intrinsic signature shapes | DONE | #602 | `ForsTreeSigCore`, `ForsSigCore`, `XmssSigCore`, `HtSigCore`, `SignatureCore` | none |
| G4 general hypertree | DONE | #603 | `GeneralHypertree.signM/rootM/pkFromSigM/verifyM`, `verify_sign`, `HypertreeGeneral/QueryBound.lean` | none |
| G5 general internal scheme | DONE | #617 | `keygenInternalM/signInternalM/verifyInternalM`, `verifyInternal_signInternal`, `DepthOneCompatibility` | the depth-one bridge for signing, `signInternalM_toOneLayer_eq`, is not an equality with `slhSignInternalM`: the general signer's trace carries one additional, discarded XMSS recovery. Consumers must use that form |
| G6 exact wire codecs | DONE | #619 | `WireCodec`, `signatureCodec`, `WireLayout.*` slice theorems, `Concrete.approvedWireCodec`, legacy-decoder reconciliation | same-length tamper test at 128f only (issue #629 item 3) |
| G7 SHA2 and SHAKE suites | DONE | #626 | `sha2Primitives`, `shakePrimitives`, `approvedPrimitives`, `Sha2Address`, `sha2AdrsKey_injective_of_domain`, `compressSha2_injective_of_fits` | several primitives, among them SHA-384, SHA-512/224, SHA-512/256, and both MGF1 variants, are regression-pinned rather than covered by independent NIST vectors (`PrimitiveVectors/NOTICE.md`); abstract `F`/`T₁` identification at arity 1 (#629 item 1) |
| FORS and hypertree conformance ports | DONE | #627, #628 | `ForsConformance.lean`, `HypertreeConformance.lean`, typed trajectory traces, concrete address bounds | none |
| G8 external interfaces and prehash | DONE | #611 | `External.lean` (`requireContext`, `signPure*`, `verifyPure*`, prehash variants), `Concrete/Prehash.lean` (12 ACVP names, OIDs), pinned `opt_rand = PK.seed` | "ACVP uses supplied randomness exactly when requested" is untestable until G10 |
| G9 efficient refinement-linked execution | NOT MERGED | frozen branch `feat/slhdsa-g9-efficient-execution-20260831`, tip `0529cefa` (still hosted) | branch-only `HashSig/SLHDSA/Execution.lean` with the full `*_eq_spec` refinement chain | the branch base is 53 commits behind the recorded `main` and carries stale pre-merge copies of the G4–G8 files; re-slice it instead of rebasing the whole branch (see below) |
| G10 ACVP and KAT coverage | NOT MERGED | frozen branch `feat/slhdsa-g10-acvp-kat-20260831`, tip `f14a9a5e` (still hosted) | branch-only ACVP schema, strict JSON parser, lossless corpus pinned to ACVP-Server `975de31e`, provenance scripts | the branch parses vectors but executes none; on `main` the only whole-scheme KATs are `Sha2KAT.lean` (one SHA2-128-24 vector) and `C13KAT.lean` |
| CF1 final-validity games | DONE | #594, #622, #624 | `TweakableHash/FinalValidity.lean`, `SMDTTCRFinalValidity`, `SMDTPREFinalValidity`, `ToFinalValidity.lean` | none |
| CF2 DSPR, OpenPRE, UD, ITSR | DONE | #596, #623, #625 | `SMDTDSPRFinalValidity`, `SMDTOpenPREFinalValidity`, `SMDTUDFinalValidity` (message-subspace parameter), `KeyedHash/ITSR.lean`, `OpenPREFromTCRDSPR.lean` (`toTCR`, `toDSPR`, `CountingInterface`) | the OpenPRE probability coupling remains an explicit interface, as the plan allows |
| CF3 generic SUF surface | DONE | #601 | `SignatureAlg.strongUnforgeableAdv`, `sameMessageAdvantage`, `advantage_eq_euf_add_sameMessage` | SLH-DSA must use the per-adversary partition, not `SameMessageBinding` (#629 item 2b) |
| D1A target and address ledger | PARTIAL: slices 1–4 DONE | #630 (`a19548d2`), #631 (`b7d06dff`), #665 (`81a75e90`), #666 (`67b3a6d9`), merged 2026-09-07/08 | slices 1–4 of the security lane below; slices 5 and 6 are implemented on branches with their PRs pending | `Params.IsD1` unclaimed; the FORS/XMSS/hypertree/scheme trace provenance and the canonical game instances are not on `main` |
| D1B witness translations | NOT STARTED | — | only `SLHDSA.xmssPkFromSig_binding` exists on `main` as a deterministic hook | the #585 lemmas are stated against the pre-G3 depth-one scheme |
| Rewritten #585 (conditional quantitative theorem) | NOT STARTED | — | — | #585 is an archived donor, see below |
| Merkle integration, general-`d` security | NOT STARTED | Merkle PRs #574, #575, #577–#579, #586–#591 merged | `MerkleExtractor.lean` is a log projection only; nothing under `HashSig/` imports `MultiExtractability` | all five integration bullets of the plan are absent |

### Gate status

- **General formalization gate (G1–G5): met.** Arbitrary validated `d`, intrinsic shapes, complete
  digest and layer recurrence, composing oracle-parametric and deterministic interpretations,
  general-`d` perfect completeness (`GeneralScheme.verifyInternal_signInternal`), explicit
  depth-one specialization. The random-oracle `PerfectlyComplete` packaging exists only for
  `d = 1` (`SLHDSA.slhdsaAlg_perfectlyComplete` in `RandomOracle.lean`); no general-`d`
  `SignatureAlg` packaging exists.
- **FIPS conformance gate (G6–G10): not met.** Twelve sets instantiated, formulas executable,
  codecs strict, interfaces match Algorithms 18–25, and 128f runs end to end through the
  specification path. Missing: the pinned ACVP corpus is not executed anywhere, no
  refinement-linked optimized path is on `main`, and no benchmark record exists for the six
  numerical shapes.
- **`d = 1` security gate: not met, in progress.** #630, #631, #665, and #666 are on `main`; they
  use the general scheme without a duplicate implementation and disclaim security content, and
  the WOTS encoding injectivity theorem is on `main`. Missing on `main`: trace provenance for the
  FORS, XMSS, hypertree, and scheme programs and the canonical game instances (slices 5 and 6,
  implemented on branches, PRs pending), a profile-specific statement for SHA2-128-24 beyond the
  encoded-ledger conditions, and everything from D1B onward.
- **General-`d` security gate: not started**, and correctly claimed nowhere.

## Security lane: slices, status, and source correspondence

The lane follows the plan's D1A → D1B → conditional theorem order, stated for arbitrary `d` with
`d = 1` as corollaries, and mirrors the structure of the EasyCrypt proof of SPHINCS+ (Barbosa,
Dupressoir, Hülsing, Meijers, Strub; `SPHINCS_PLUS.ec`, `WOTS_TW_ES.ec`, `FORS_ES.ec`,
`FL_SL_XMSS_MT_ES.ec`). Slices 1–4 are on `main`: the stack #630 → #631 → #666 and the
independent WOTS encoding proof #665; later reduction slices consume both lines. Each slice is its
own pull request, stacked on the previous one where it depends on it, opened as a draft,
adversarially reviewed on every commit by an independent read-only reviewer, and taken out of
draft only when a review round reports nothing to fix. The recurring defect class across every
review round so far has been prose claiming more than the lemmas prove; reviewers check each
docstring sentence against the lemma it describes.

| # | Slice | Content | Status | EasyCrypt counterpart |
|---|---|---|---|---|
| 1 | Target roles, counts, structural ledgers | `TargetRole` (8), `targetCount`, `xmssTreeCount`, `wotsInstanceCount`; executable `List Adrs` ledgers per role with exact `length` (or honest upper bound for the WOTS+ TCR and PRE roles), `Nodup`, `mem_*` completeness, pairwise disjointness; `EncodedTargetLedgerConditions` | merged 2026-09-07 (#630, `a19548d2`) | clone parameters `t_smdtud = t_smdtpre = c·len`, `t_smdttcr = c·len·w` (`WOTS_TW_ES.ec`), `d·k·t`, `d·k·(t−1)`, `d` (`FORS_ES.ec`, with `d = 2^h` under the `SPHINCS_PLUS.ec` instantiation), the two hypertree sums (`FL_SL_XMSS_MT_ES.ec`); `c = wotsInstanceCount` |
| 2 | Encoded ledgers | SHA-2 compressed-address domain (`CanonicalAddressBounds`, `ApprovedAddressBounds`, `Sha2Domain`), per-ledger membership, `approvedEncodedTargetLedgerConditions` for all twelve sets and both encoders, `limitedEncodedTargetLedgerConditions`; counterexample profile pinned as `deep_sha2_conditions_false` | merged 2026-09-07 (#631, `b7d06dff`); was stacked on #630 | type-tag distinctness side conditions (`dist_adrstypes`, `get_typeidx … <> chtype` preconditions) |
| 3 | WOTS message-encoding injectivity | `Function.Injective` of the full-width `wotsMsgDigitsCore` under `p.Valid` (which supplies `lgw ∣ 8n`) and `core.ByteLaws`, from `WotsChecksum.fromBaseW_digitsOfBaseW_of_lt`; lifts `wots_fullDigits_incomparable` to `core.Y` | merged 2026-09-07 (#665, `81a75e90`); independent of the stack | axiom `two_encodings` (`WOTS_TW_ES.ec`), the only encoding fact the source assumes |
| 4 | Trace provenance (WOTS+) | `constructionAddresses` union ledger with `Nodup`, `QueriesWithinConstructionTargets` pathwise `IsQueryBound` over `publicHashSpec`, theorems for `chainM`, `wotsPkGenM`, `wotsSignM`, `wotsPkFromSigM`, the logged-execution bridge for any `QueryImpl (publicHashSpec core) Id` | merged 2026-09-08 (#666, `67b3a6d9`); was stacked on #631; port of the archived donor with the enumeration-completeness section replaced by slice 1's `mem_*` lemmas | the `hoare` address-discipline lemmas on the WOTS-TW oracles |
| 5 | Trace provenance (FORS, XMSS, hypertree, scheme) | predicate-tracking Merkle lemmas added to VCVio (`PerfectMerkleTree.merkleRootM_pred_of_subtree`, `intrinsicAuthPathM_pred_of_tree`, `climbM_pred_of_ancestors`), instantiated as `QueriesWithinConstructionTargets.merkleRootM/intrinsicAuthPathM/climbM`; `*_queriesWithinConstructionTargets` for `forsRootM`, `forsPkGenM`, `forsSignM`, `forsPkFromSigM`, `xmssNodeM`, `xmssRootM`, `xmssSignM`, `xmssPkFromSigM`, `GeneralHypertree.signM/pkFromSigM/verifyM/rootM`, `keygenInternalM`, `signInternalM`, `verifyInternalM`; `*_traceContract` pairing each with its total query bound (upper bounds at the hypertree and scheme levels) | implemented on branch `feat/slhdsa-d1a-component-traces-20260907` (`Security/ComponentTraces.lean`, `HashSigTest/SLHDSA/ComponentTraces.lean`, `slhdsa_component_trace_tests`), branched from #666's pre-merge head; PR pending after a rebase onto `main`; derived, no donor | the corresponding FORS/XMSS/hypertree oracle lemmas |
| 6 | Canonical game instances | final-validity `Problem`s: standalone OpenPRE, DSPR, and TCR for FORS `F`, the latter two shown equal to `.toDSPR`/`.toTCR` of the OpenPRE problem (`forsFDsprProblem_eq_toDSPR`, `forsFTcrProblem_eq_toTCR`); collection TCR for FORS `H`, FORS `T_ℓ`, WOTS `F`, WOTS `T_ℓ`, XMSS `H`; collection UD and PRE for WOTS `F` with subspace `M' = Y` and identity embedding; ITSR for `H_msg` indexed by `splitDigest` and `forsIdx`, with `PK.seed` and `PK.root` in the hashed input as in FIPS 205 Algorithm 19; `numTargets := targetCount` bridges; no reductions and no inequalities | implemented on branch `feat/slhdsa-d1a-canonical-games-20260907` (`Security/CanonicalGames.lean`, `HashSigTest/SLHDSA/CanonicalGames.lean`, `slhdsa_canonical_game_tests`), branched from #666's pre-merge head alongside slice 5, not stacked on it; PR pending after a rebase onto `main`; port of the archived donor `CanonicalGames.lean` retargeted to the game modules of #623–#625 | `FP_DSPR`, `FP_TCR`, `TRHC_TCR`, `TRCOC_TCR`, `FC_UD`, `FC_PRE`, `FC_TCR`, `PKCOC_TCR`, `MCO_ITSR` clones (the source's `MCO` hashes the message alone) |
| 7 | D1B witness translations | deterministic FORS/WOTS/XMSS forgery-to-witness translations over `GeneralScheme` and intrinsic vectors, each labeled deterministic inclusion or transcript transport | planned; the #585 lemmas are the idea source only | the `valid_TCRTRH` and chain-consistency case analyses |
| 8 | Composition and conditional theorem | composition certificate, exact conditional EUF-CMA expression (twelve summands with the `3·` and `(w−2)·` coefficients), SUF residual via the per-adversary partition, SHA2-128-24 corollary; program-equivalence hops and the OpenPRE coupling as named hypotheses | planned; replaces #585 | `EUFCMA_SPHINCS_PLUS` (`SPHINCS_PLUS.ec`) |

Hypotheses the conditional theorem is expected to carry explicitly, each corresponding to an
undischarged or program-level step in the source proof:

- the two PRF hops (`SKG`, `MKG`) against `skPrfScheme`/`msgPrfScheme`, with no NPRF scheme
  variant yet on `main`;
- the FORS public-key recomputation-versus-recovery program equivalence over `signInternalM`
  (`SLHDSA.forsPkFromSig_forsSign` supplies the deterministic identity over `Primitives`; the
  monadic lift over `signInternalM` is the hypothesis);
- the `(w − 2)` UD hybrid and the OpenPRE-from-TCR/DSPR probability coupling
  (`SM_DT_OpenPRE_SourceFinalValidity.CountingInterface`);
- uniform full-digest distribution for the FORS inputs (`Problem.HasUniformInputs`);
- structural adversary query bounds.

Reduction traps recorded in issue #629 apply to every slice from 6 onward: the zero fallbacks of
`sha2AdrsKey` and `checkedNodeOrZero` alias reachable values, so every statement carries the
checked-domain hypotheses of `sha2AdrsKey_injective_of_domain`; and `SameMessageBinding` is
unbounded, so the SUF residual uses `advantage_eq_euf_add_sameMessage`.

### Design decisions settled during review

- Two bounds records rather than one: `CanonicalAddressBounds` (what SHAKE needs) and
  `ApprovedAddressBounds extends` it (two compressed widths for SHA-2). A single record with a
  docstring excusing the too-strong SHAKE hypothesis was rejected; the separating profile is a
  regression test.
- Ledger completeness lemmas are named `mem_<ledgerName>`.
- Per-role ledgers mirror the source's separate clones; games that share a hash function
  (arity-1: WOTS `F` and FORS `F`; arity-2: XMSS `H` and FORS `H`; `T_ℓ`: WOTS public key and FORS
  roots) rely on the pairwise disjointness lemmas of slice 1 when a union target list is needed.
- Final-validity games are instantiated, as in the source; `ToFinalValidity.lean` bridges the
  reject-on-arrival problems that `Security.lean` packages today (`thashTcrProblem`,
  `thashPreProblem`).

## Frozen branches: G9 and G10

The G9 and G10 branches, `feat/slhdsa-g9-efficient-execution-20260831` (tip `0529cefa`) and
`feat/slhdsa-g10-acvp-kat-20260831` (tip `f14a9a5e`), are still hosted but frozen: both tips
predate the merged G4–G8 and carry stale pre-merge copies of those files, so neither can be
rebased. Use the tip commits as idea sources and re-slice only the owned changes:

- **G9**: a single PR carrying `HashSig/SLHDSA/Execution.lean` (the `treeHash`,
  `authenticationPath`, and `*_eq_spec` refinement theorems restated against the merged
  `GeneralScheme`, `Codec`, and `External` APIs) plus `HashSigTest/SLHDSA/Execution.lean` and a
  benchmark record for the six numerical shapes.
- **G10**: first a corpus-import PR (schema, strict JSON parser, lossless corpus, manifest pinned
  to ACVP-Server `975de31e`, provenance check script), then a runner PR that executes
  `keygenWithSeeds`, `signPure*`, and `verifyPure*` on every group of the corpus, with CI running
  the smoke subset and the full corpus on a schedule.

These are maintainer-owned lanes; the security lane does not depend on them.

## Disposition of PR #585

#585 stays open as a draft on the merged base `repair/multitarget-collection-20260828` with the
pre-G3 depth-one scheme. Nothing in the live security lane reuses its branch. Its
`Security/ReductionBound.lean`, `Concrete/Security.lean`, and witness lemmas in `Security.lean`
are idea sources for slices 7 and 8, which will be new pull requests. The plan's statement that
#585 "retains its number" should be read as: the rewritten theorem replaces it, and #585 is closed
with a cross-reference when slice 8 opens.

## Corrections to the plan document

Statements in `slh-dsa-fips205-generalization.md` that are snapshots of 2026-08-30 and are no
longer true on `main`:

- "Planning baseline" and the "reduced-profile boundaries" list (`h = d·hp` unenforced, digest
  split without the tree index, one-XMSS `HtSigCore`, 3,856-byte decoder, empty-context wrapper):
  every bullet is resolved by G1–G8.
- "The Merkle stack runs from #574 through #591 … not a prerequisite": the Merkle PRs in that
  range (#574, #575, #577–#579, #586–#591) all merged 2026-09-01; the current Merkle work is
  #618 and #621.
- The pull-request stack table names no PR numbers. For the record: G5–G8 landed on `main` through
  #617, #619, #626, and #611. Of the original stacked PRs, #604–#606 were closed and #607 was
  squash-merged into the stacked G7 branch by mistake and reverted there (its content reached
  `main` through #611); #627 and #628 carried the FORS and hypertree conformance ports in place of
  #608 and #609.
- "D1A: d1 target/address ledger": #630 states the ledgers for arbitrary `d`; the depth-one values
  are corollaries.
- `Params.IsD1` is named as a D1A deliverable but does not exist; `main` threads `p.d = 1`
  hypotheses directly (`DepthOneCompatibility` and `Security.xmssTreeCount_of_d_eq_one`, both on
  `main`). Either the predicate is added in slice 8 where a named profile is needed, or the plan
  is amended.
- The plan does not mention the archived donor at commit `88314278` (closed #597; still hosted
  as the remote branch `archive/slhdsa-pr597-final-88314278`), whose
  `Security/{CanonicalGames,TraceTargets,Architecture}.lean` were the inputs of slices 4 and 6,
  both now consumed, nor the follow-up issue #629.

## Follow-ups outside the security lane

- Issue #629: abstract `F`/`T₁` identification, reduction-checklist items, all-profile
  same-length wire-tamper test, two doc nits.
- `HashSigTest/SLHDSA/GeneralScheme.lean` says no executable `d > 1` primitive instance exists;
  `DataCodecTests`, `External`, and `HypertreeConformanceTests` now execute SHA2-128f (`d = 22`).
- The depth-one compatibility signer (`slhSignInternalM`) and the general signer coexist, related
  by `signInternalM_toOneLayer_eq`. The plan forbids keeping both indefinitely; the compatibility
  scheme should be retired once slice 7 consumes `GeneralScheme` directly.
- Independent NIST vectors for the regression-pinned primitives listed in
  `HashSigTest/SLHDSA/PrimitiveVectors/NOTICE.md`.
- Deferred cleanup ledger from the stack reviews: the `XmssSig` alias of `XmssSigCore`, the dead
  `pk` parameter of `recoverFromPositionWith`, the unused `FipsParameterSet.category`, and the
  smaller items recorded in the review threads of #605–#611.

## Working protocol for the lane

- Branch from the previous slice's head, `feat/slhdsa-<slice>-YYYYMMDD`; open as a draft PR
  immediately; push regular commits.
- Per slice, in order: `lake build HashSig HashSigTest`; the slice's executables;
  `lake exe lint-style <module names>`; `lake exe mk_all --lib HashSig --module --check`;
  `python3 scripts/check-agent-docs.py`; `scripts/check-pmf-boundary.sh`;
  `scripts/check-expose-boundary.sh`; `git diff --check`; the full non-test build; and
  `lake exe axiomsweep --check`.
- Every commit gets an independent read-only adversarial review that cross-checks against FIPS 205,
  the EasyCrypt artifact, and the reference implementation; findings are validated, fixed, and the
  dispositions posted on the PR. Docstring changes are re-read sentence by sentence against the
  lemma they describe before pushing.
- Author-owned PRs need a second maintainer's approval; a stacked PR is added to the GitHub merge
  queue only after its predecessor has merged and GitHub has retargeted it to `main`.

## References

- NIST FIPS 205, *Stateless Hash-Based Digital Signature Standard*, August 2024. Section map
  used by the lane: §4.1 hash functions and PRFs, §4.2 addresses, §5 WOTS+ (Algorithms 5–8),
  §6 XMSS (9–11), §7 hypertree (12–13), §8 FORS (14–17), §9 internal functions (18–20),
  §10 external functions (21–25), §11 parameter sets (§11.2 compressed address `ADRSc`,
  Figure 18, Table 3).
- M. Barbosa, F. Dupressoir, A. Hülsing, M. Meijers, P.-Y. Strub, *A Tight Security Proof for
  SPHINCS+, Formally Verified*, ASIACRYPT 2023; EasyCrypt development `FV-SPHINCSPLUS-EC`.
- D. J. Bernstein, A. Hülsing, S. Kölbl, R. Niederhagen, J. Rijneveld, P. Schwabe, *The SPHINCS+
  Signature Framework*, CCS 2019; SPHINCS+ round-3.1 specification (2022) and NIST submission
  package (reference implementation).
- A. Hülsing, J. Rijneveld, F. Song, *Mitigating Multi-Target Attacks in Hash-Based Signatures*,
  PKC 2016.
- NIST ACVP-Server SLH-DSA vectors, commit `975de31e`.
