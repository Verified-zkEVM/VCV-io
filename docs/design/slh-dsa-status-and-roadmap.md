# SLH-DSA formalization: status and roadmap

Status: implementation-status report and forward roadmap, established 2026-09-06. It complements
the plan in [`slh-dsa-fips205-generalization.md`](slh-dsa-fips205-generalization.md), which fixes
the target architecture, milestone definitions, acceptance gates, and merge protocol. The plan has
not changed since 2026-08-30; this document records what has merged since, what is open, where the
plan's snapshot statements are now stale, and the ordered slices that remain. Where the two
disagree about *what is on `main`*, this document is right and the plan is a snapshot.

A capability is listed as DONE only when its source and validation are on `main`. Open pull
requests are named as such. Nothing in this document is a security claim: no SLH-DSA
unforgeability theorem of any kind exists on `main` today.

## Where the work lives

| Area | Modules | Validation |
|---|---|---|
| Parameters, positions, addresses | `HashSig/SLHDSA/Params.lean`, `FipsParams.lean`, `Position.lean`, `Address.lean`, `Encoding.lean`, `EncodingLemmas.lean` | `HashSigTest/SLHDSA/Params.lean`, `Position.lean` |
| Components (WOTS+, XMSS, FORS) | `Wots.lean`, `WotsChecksum.lean`, `WotsEncoding.lean`, `Xmss.lean`, `Fors.lean`, `*Conformance.lean` | `slhdsa_wots_tests`, `slhdsa_xmss_tests`, `slhdsa_fors_tests` |
| General hypertree and scheme | `HypertreeGeneral.lean` (+ `QueryBound.lean`), `GeneralScheme.lean`, `GeneralSchemeQueryBound.lean`, `DepthOneCompatibility.lean` | `slhdsa_hypertree_tests`, `HashSigTest/SLHDSA/GeneralScheme.lean` |
| Depth-one compatibility scheme | `Hypertree.lean`, `Scheme.lean`, `RandomOracle.lean`, `Oracle.lean` | `HashSigTest/SLHDSA/Scheme.lean` |
| Wire codecs | `Codec.lean`, `Concrete/Codec.lean` | `slhdsa_data_codec_tests` |
| Concrete primitives (12 FIPS sets) | `Concrete/Sha2.lean`, `Concrete/Keccak.lean`, `Concrete/FIPS.lean`, `Concrete/Instance.lean`, `Concrete/Prehash.lean` | `slhdsa_primitive_tests` (+ `PrimitiveVectors/`), `slhdsa_kat`, `slhdsa_c13_kat` |
| External interfaces (Alg. 21–25) | `External.lean` | `slhdsa_external_tests` |
| Security packaging | `Security.lean` (primitive families as `TweakableHash`/`PRFScheme`), `MerkleExtractor.lean` | — |
| Security lane (open PRs) | `Security/TargetCounts.lean`, `Security/ReachableTargets.lean` (#630); `Security/EncodedTargets.lean` (#631) | `slhdsa_target_ledger_tests`, `slhdsa_encoded_ledger_tests` |
| Generic hash games consumed | `VCVio/CryptoFoundations/HardnessAssumptions/TweakableHash/*.lean`, `KeyedHash/ITSR.lean`, `VCVio/CryptoFoundations/SignatureAlg.lean` | `VCVioTest/SMDT*.lean` |

Every SLH-DSA test executable runs in `.github/workflows/build.yml`; `linting.yml` style-lints `HashSig`
and the listed test modules; `scripts/check-expose-boundary.sh` caps the number of broadly exposed files per
library (new modules use a plain `public section` with per-declaration `@[expose]`);
`lake exe axiomsweep --check` guards the axiom and `sorry` footprint against
`scripts/axiom_baseline.json`.

## Milestone status ledger

Verified against `origin/main` at `4c48fed3` (2026-09-06).

| Milestone | Status | Landed in | Realized by | Gap against the plan's wording |
|---|---|---|---|---|
| G1 valid parameters, all FIPS sets | DONE | #593 | `Params`, `Params.Valid`, `ValidatedParams`, `FipsParameterSet` (12), `LimitedParameterSet`, `FipsParams` | none |
| G2 digest and layer-index calculus | DONE | #595 | `DigestParts`, `splitDigest`, `LayerPosition` (`initial`, `next`, `atLayer`, `toAdrs`, `forsAdrs`) | layer is a field of `LayerPosition`, not an index; an allowed normalization |
| G3 intrinsic signature shapes | DONE | #602 | `ForsTreeSigCore`, `ForsSigCore`, `XmssSigCore`, `HtSigCore`, `SignatureCore` | none |
| G4 general hypertree | DONE | #603 | `GeneralHypertree.signM/rootM/pkFromSigM/verifyM`, `verify_sign`, `HypertreeGeneral/QueryBound.lean` | none |
| G5 general internal scheme | DONE | #617 | `keygenInternalM/signInternalM/verifyInternalM`, `verifyInternal_signInternal`, `DepthOneCompatibility` | the depth-one bridge for signing, `signInternalM_toOneLayer_eq`, is not an equality with `slhSignInternalM`: the general signer's trace carries one additional, discarded XMSS recovery. Consumers must use that form |
| G6 exact wire codecs | DONE | #619 | `WireCodec`, `signatureCodec`, `WireLayout.*` slice theorems, `Concrete.approvedWireCodec`, legacy-decoder reconciliation | same-length tamper test at 128f only (issue #629 item 3) |
| G7 SHA2 and SHAKE suites | DONE | #626 | `sha2Primitives`, `shakePrimitives`, `approvedPrimitives`, `Sha2Address`, `sha2AdrsKey_injective_of_domain`, `compressSha2_injective_of_fits` | several primitives, among them SHA-384, SHA-512/224, SHA-512/256, and both MGF1 variants, are regression-pinned rather than covered by independent NIST vectors (`PrimitiveVectors/NOTICE.md`); abstract `F`/`T₁` identification at arity 1 (#629 item 1) |
| FORS and hypertree conformance ports | DONE | #627, #628 | `ForsConformance.lean`, `HypertreeConformance.lean`, typed trajectory traces, concrete address bounds | none |
| G8 external interfaces and prehash | DONE | #611 | `External.lean` (`requireContext`, `signPure*`, `verifyPure*`, prehash variants), `Concrete/Prehash.lean` (12 ACVP names, OIDs), pinned `opt_rand = PK.seed` | "ACVP uses supplied randomness exactly when requested" is untestable until G10 |
| G9 efficient refinement-linked execution | NOT MERGED | frozen branch `feat/slhdsa-g9-efficient-execution-20260831` | branch-only `HashSig/SLHDSA/Execution.lean` with the full `*_eq_spec` refinement chain | base is 37 commits behind `main` and carries stale pre-merge copies of the G4–G8 files; must be re-sliced, not rebased (see below) |
| G10 ACVP and KAT coverage | NOT MERGED | frozen branch `feat/slhdsa-g10-acvp-kat-20260831` | branch-only ACVP schema, strict JSON parser, lossless corpus pinned to ACVP-Server `975de31e`, provenance scripts | the branch parses vectors but executes none; on `main` the only whole-scheme KATs are `Sha2KAT.lean` (one SHA2-128-24 vector) and `C13KAT.lean` |
| CF1 final-validity games | DONE | #594, #622, #624 | `TweakableHash/FinalValidity.lean`, `SMDTTCRFinalValidity`, `SMDTPREFinalValidity`, `ToFinalValidity.lean` | none |
| CF2 DSPR, OpenPRE, UD, ITSR | DONE | #596, #623, #625 | `SMDTDSPRFinalValidity`, `SMDTOpenPREFinalValidity`, `SMDTUDFinalValidity` (message-subspace parameter), `KeyedHash/ITSR.lean`, `OpenPREFromTCRDSPR.lean` (`toTCR`, `toDSPR`, `CountingInterface`) | the OpenPRE probability coupling remains an explicit interface, as the plan allows |
| CF3 generic SUF surface | DONE | #601 | `SignatureAlg.strongUnforgeableAdv`, `sameMessageAdvantage`, `advantage_eq_euf_add_sameMessage` | SLH-DSA must use the per-adversary partition, not `SameMessageBinding` (#629 item 2b) |
| D1A target and address ledger | IN REVIEW | #630, #631 (open) | see the security lane below | `Params.IsD1` and WOTS message-encoding injectivity unclaimed |
| D1B witness translations | NOT STARTED | — | only `SLHDSA.xmssPkFromSig_binding` exists on `main` as a deterministic hook | the #585 lemmas are stated against the pre-G3 depth-one scheme |
| Rewritten #585 (conditional quantitative theorem) | NOT STARTED | — | — | #585 is an archived donor, see below |
| Merkle integration, general-`d` security | NOT STARTED | Merkle PRs #574, #575, #577–#579, #586–#591 merged | `MerkleExtractor.lean` is a log projection only; nothing under `HashSig/` imports `MultiExtractability` | all five integration bullets of the plan are absent |

### Gate status

- **General formalization gate (G1–G5): met.** Arbitrary validated `d`, intrinsic shapes, complete
  digest and layer recurrence, composing oracle-parametric and deterministic interpretations,
  general-`d` perfect completeness (`GeneralScheme.verifyInternal_signInternal`), explicit
  depth-one specialization. The random-oracle `PerfectlyComplete` packaging exists only for `d = 1`
  (`SLHDSA.slhdsaAlg_perfectlyComplete` in `RandomOracle.lean`); no general-`d` `SignatureAlg` packaging exists.
- **FIPS conformance gate (G6–G10): not met.** Twelve sets instantiated, formulas executable,
  codecs strict, interfaces match Algorithms 18–25, and 128f runs end to end through the
  specification path. Missing: the pinned ACVP corpus is not executed anywhere, no
  refinement-linked optimized path is on `main`, and no benchmark record exists for the six
  numerical shapes.
- **`d = 1` security gate: not met, in progress.** #630 and #631 use the general scheme without a
  duplicate implementation and disclaim security content. Missing: WOTS encoding injectivity, a
  profile-specific statement for SHA2-128-24 beyond the encoded-ledger conditions, and everything
  from D1B onward.
- **General-`d` security gate: not started**, and correctly claimed nowhere.

## Security lane: slices, status, and source correspondence

The lane follows the plan's D1A → D1B → conditional theorem order, stated for arbitrary `d` with
`d = 1` as corollaries, and mirrors the structure of the EasyCrypt proof of SPHINCS+ (Barbosa,
Dupressoir, Hülsing, Meijers, Strub; `SPHINCS_PLUS.ec`, `WOTS_TW_ES.ec`, `FORS_ES.ec`,
`FL_SL_XMSS_MT_ES.ec`). Each slice is its own pull request, stacked on the previous one, opened as
a draft, adversarially reviewed on every commit by an independent read-only reviewer, and taken out
of draft only when a review round reports nothing to fix. The recurring defect class across every
review round so far has been prose claiming more than the lemmas prove; reviewers check each
docstring sentence against the lemma it describes.

| # | Slice | Content | Status | EasyCrypt counterpart |
|---|---|---|---|---|
| 1 | Target roles, counts, structural ledgers | `TargetRole` (8), `targetCount`, `xmssTreeCount`, `wotsInstanceCount`; executable `List Adrs` ledgers per role with exact `length` (or honest upper bound for the WOTS+ TCR and PRE roles), `Nodup`, `mem_*` completeness, pairwise disjointness; `EncodedTargetLedgerConditions` | PR #630, in review | clone parameters `t_smdtud = t_smdtpre = c·len`, `t_smdttcr = c·len·w` (`WOTS_TW_ES.ec`), `d·k·t`, `d·k·(t−1)`, `d` (`FORS_ES.ec`, with `d = 2^h` under the `SPHINCS_PLUS.ec` instantiation), the two hypertree sums (`FL_SL_XMSS_MT_ES.ec`); `c = wotsInstanceCount` |
| 2 | Encoded ledgers | SHA-2 compressed-address domain (`CanonicalAddressBounds`, `ApprovedAddressBounds`, `Sha2Domain`), per-ledger membership, `approvedEncodedTargetLedgerConditions` for all twelve sets and both encoders, `limitedEncodedTargetLedgerConditions`; counterexample profile pinned as `deep_sha2_conditions_false` | PR #631, in review, stacked on #630 | type-tag distinctness side conditions (`dist_adrstypes`, `get_typeidx … <> chtype` preconditions) |
| 3 | WOTS message-encoding injectivity | `Function.Injective` of the full-width `wotsMsgDigitsCore` for `lgw ∣ 8n` from `WotsChecksum.fromBaseW_digitsOfBaseW_of_lt`; lifts `wots_fullDigits_incomparable` to `core.Y` | planned; independent of the stack, may target `main` directly | axiom `two_encodings` (`WOTS_TW_ES.ec`), the only encoding fact the source assumes |
| 4 | Trace provenance (WOTS+) | `constructionAddresses` union ledger with `Nodup`, `QueriesWithinConstructionTargets` pathwise `IsQueryBound` over `publicHashSpec`, instances for `chainM`, `wotsPkGenM`, `wotsSignM`, `wotsPkFromSigM`, the logged-execution bridge for any `QueryImpl (publicHashSpec core) Id` | planned; port of the archived donor with the enumeration-completeness section replaced by slice 1's `mem_*` lemmas | the `hoare` address-discipline lemmas on the WOTS-TW oracles |
| 5 | Trace provenance (FORS, XMSS, hypertree, scheme) | index-bounded pathwise analogues of `isTotalQueryBound_merkleRootM`/`intrinsicAuthPathM`/`climbM`, then `forsSignM`, `forsPkFromSigM`, `xmssSignM`, `xmssPkFromSigM`, `GeneralHypertree.signM/pkFromSigM`, `signInternalM`, `verifyInternalM`, `keygenInternalM` | planned; must be derived, no donor | the corresponding FORS/XMSS/hypertree oracle lemmas |
| 6 | Canonical game instances | final-validity `Problem`s: standalone DSPR and TCR for FORS `F` derived from an OpenPRE problem via `OpenPREFromTCRDSPR.toDSPR/.toTCR`; collection TCR for FORS `H`, FORS `T_ℓ`, WOTS `F`, WOTS `T_ℓ`, XMSS `H`; collection UD and PRE for WOTS `F` with subspace `M' = Y` and identity embedding; ITSR for `H_msg` indexed by `splitDigest` and `forsIdx`; `numTargets := targetCount` bridges | planned; donor `CanonicalGames.lean` retargeted to the renamed game modules of #623–#625 | `FP_DSPR`, `FP_TCR`, `TRHC_TCR`, `TRCOC_TCR`, `FC_UD`, `FC_PRE`, `FC_TCR`, `PKCOC_TCR`, `MCO_ITSR` clones |
| 7 | D1B witness translations | deterministic FORS/WOTS/XMSS forgery-to-witness translations over `GeneralScheme` and intrinsic vectors, each labeled deterministic inclusion or transcript transport | planned; the #585 lemmas are the idea source only | the `valid_TCRTRH` and chain-consistency case analyses |
| 8 | Composition and conditional theorem | composition certificate, exact conditional EUF-CMA expression (twelve summands with the `3·` and `(w−2)·` coefficients), SUF residual via the per-adversary partition, SHA2-128-24 corollary; program-equivalence hops and the OpenPRE coupling as named hypotheses | planned; replaces #585 | `EUFCMA_SPHINCS_PLUS` (`SPHINCS_PLUS.ec`) |

Hypotheses the conditional theorem is expected to carry explicitly, each corresponding to an
undischarged or program-level step in the source proof:

- the two PRF hops (`SKG`, `MKG`) against `skPrfScheme`/`msgPrfScheme`, with no NPRF scheme
  variant yet on `main`;
- the FORS public-key recomputation-versus-recovery program equivalence over `signInternalM`
  (`SLHDSA.forsPkFromSig_forsSign` supplies the identity);
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

## Frozen lanes: G9 and G10

Both branches predate the merged G4–G8 and carry stale pre-merge copies of their files, so they
cannot be rebased. Re-slicing:

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
- "The Merkle stack runs from #574 through #591 … not a prerequisite": the Merkle PRs in that range
  (#574, #575, #577–#579, #586–#591) all merged 2026-09-01; the current Merkle work is #618 and
  #621.
- The pull-request stack table names no PR numbers. For the record: G5–G8 landed through #617,
  #619, #626, #611 after the original stacked PRs #604–#607 were closed, and #627 and #628
  carried the FORS and hypertree conformance ports in place of #608 and #609.
- "D1A: d1 target/address ledger": #630 states the ledgers for arbitrary `d`; the depth-one values
  are corollaries.
- `Params.IsD1` is named as a D1A deliverable but does not exist; `main` threads `p.d = 1`
  hypotheses directly (`DepthOneCompatibility` on `main`, `Security.xmssTreeCount_of_d_eq_one` in
  #630). Either
  the predicate is added in slice 8 where a named profile is needed, or the plan is amended.
- The plan does not mention the archived donor `origin/archive/slhdsa-pr597-final-88314278`
  (closed #597), whose `Security/{CanonicalGames,TraceTargets,Architecture}.lean` are the inputs
  of slices 4 and 6, nor the follow-up issue #629.

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
