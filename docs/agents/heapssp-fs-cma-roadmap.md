# HeapSSP FS-CMA Proof Infrastructure Roadmap

This note tracks the local infrastructure work needed to finish the Fiat-Shamir
EUF-CMA theorem chain without accumulating large bespoke proofs.

The guiding principle is:

- do not close the remaining FS-CMA sorries by hand-rolling hundreds of lines
  of one-off cache, logging, and event-splitting proofs;
- build the reusable HeapSSP, query-tracking, and replay-fork infrastructure
  first;
- cut over existing proven hybrids to the same infrastructure instead of
  leaving parallel proof styles in the tree.

## Current State

The HeapSSP FS-CMA skeleton is in place under
`VCVio/CryptoFoundations/FiatShamir/Sigma/HeapSSP/`.

Progress started:

- Public TV bind/bad-event lemmas have been added to
  `VCVio/EvalDist/TVDist.lean`.
- A first HeapSSP invariant-gated identical-until-bad wrapper has been added
  to `VCVio/HeapSSP/IdenticalUntilBad.lean`.
- The FS-CMA wrapper query-bound transport now derives the signing/hash bounds
  for the HeapSSP adversary wrappers from the source adversary bound.
- The top-level HeapSSP CMA-to-fork theorem no longer has the verifier `+1` in
  the H3 beta term: `signedFreshAdv` is factored into candidate production plus
  `verifyFreshComp`, and H3 uses a custom expected-cost bound showing that the
  verifier suffix has zero signing-replacement cost.

The important remaining proof obligations are:

- H2: relate the public CMA unforgeability experiment to the HeapSSP
  `cmaReal` package running the freshness-aware adversary.
- H3: prove the real-to-sim signing hop from HVZK plus random-oracle
  programming collision probability.
- H5: bound the shifted NMA/freshness event by the fork advantage plus the
  verify-challenge miss term.

The current proofs are hard because the framework exposes too much low-level
state: heap cells, random-oracle caches, query logs, adversary wrappers,
Boolean postprocessors, and final-state events are all handled separately.

## Missing Infrastructure

### 1. Invariant-aware identical-until-bad for HeapSSP

Current HeapSSP identical-until-bad obligations are pointwise over arbitrary
heap states. FS-CMA needs obligations only over reachable states satisfying the
CMA key/cache/log invariant.

TODO:

- Add an invariant-indexed HeapSSP identical-until-bad theorem.
- The theorem should take `Inv init`, preservation for the real package, and a
  per-step TV bound only under `Inv s`.
- Use this to remove invalid-state fallback artifacts from H3-style proofs.
- Prefer an API that works for both Boolean advantages and stateful events.

Target files:

- `VCVio/HeapSSP/IdenticalUntilBad.lean`
- `VCVio/HeapSSP/Advantage.lean`

### 2. Event-level package advantages

`Package.advantage` is Boolean-output oriented, but CMA freshness is naturally a
predicate over output plus final heap/log state.

TODO:

- Add a package theorem for probabilities of predicates over `(output,
  finalState)`.
- Provide Boolean-output advantage as a specialization, not the only public
  interface.
- Rework `signedFreshAdv` so freshness does not need to be encoded by synthetic
  local logging unless the event theorem still needs it internally.

Target files:

- `VCVio/HeapSSP/Package.lean`
- `VCVio/HeapSSP/Advantage.lean`
- `VCVio/CryptoFoundations/FiatShamir/Sigma/HeapSSP/Bridge.lean`

### 3. TV bind plus bad-event lemmas

H3 needs a reusable theorem saying that a bind is close when the base
distributions are close and the continuations agree except on a bad event.

TODO:

- Add public PMF/TV lemmas for bind plus event decomposition.
- State them in the `ENNReal` form used by the rest of the HeapSSP chain.
- Avoid keeping these as private helpers inside expected-cost or program-logic
  files.

Target files:

- `VCVio/ProgramLogic/Relational/TVDist.lean`
- possibly a new small probability helper file if layering requires it

### 4. Query-bound transport through reductions

The FS-CMA theorem still carries query-bound assumptions for wrapped
adversaries. Those should be derived compositionally.

TODO:

- Generalize the FS-specific `cmaSignHashQueryBound_bind`,
  `cmaSignHashQueryBound_mono`, and logging-wrapper lemmas into reusable
  `OracleComp.IsQueryBound` infrastructure.
- Prove query-bound preservation for package shifts and adversary projections.
- Add small simp/automation support for `OracleComp.IsQueryBound` goals.
- Use this to remove direct `hQB` and `hQBH` assumptions from high-level
  FS-CMA theorem statements when they are derivable from the original
  adversary bound.

Target files:

- `VCVio/OracleComp/QueryTracking/Structures.lean`
- `VCVio/OracleComp/QueryTracking/Enforcement.lean`
- `VCVio/CryptoFoundations/FiatShamir/Sigma/HeapSSP/Chain.lean`

### 5. Logging equivalence between runtime and HeapSSP state

H2 is mostly structural, but today it must compare public security experiments,
WriterT logs, runtime caches, and HeapSSP heap cells manually.

TODO:

- Publicize or generalize the existing logging/runtime equivalence lemmas used
  in the legacy Sigma security proof.
- Add a theorem connecting WriterT query logging to StateT/heap append logging.
- Add a theorem that the HeapSSP CMA package implements the public
  `SignatureAlg.unforgeableExp` runtime under the projected final event.

Target files:

- `VCVio/OracleComp/QueryTracking/LoggingOracle.lean`
- `VCVio/CryptoFoundations/FiatShamir/Sigma/Security.lean`
- `VCVio/CryptoFoundations/FiatShamir/Sigma/HeapSSP/Bridge.lean`

### 6. Managed random-oracle fork theorem

H5 should be a reusable Fiat-Shamir managed-RO theorem, not a one-off proof.

TODO:

- Package the standard split: final verification success is bounded by
  forkable live-query success plus a fresh-challenge miss term.
- State the theorem against the managed-RO NMA shape used by the HeapSSP
  `shiftLeft` chain.
- Connect it to the existing replay fork machinery where ambient randomness is
  replayed rather than re-sampled.

Target files:

- `VCVio/CryptoFoundations/ReplayFork.lean`
- `VCVio/CryptoFoundations/FiatShamir/Sigma/Fork.lean`
- `VCVio/CryptoFoundations/FiatShamir/Sigma/HeapSSP/Chain.lean`
- `docs/agents/replay-fork.md`

### 7. Heap package frame lemmas and automation

FS-CMA package proofs repeatedly need frame facts: unrelated heap cells are
preserved, cache updates grow by at most one, and package handlers preserve
invariants.

TODO:

- Add reusable heap read/update/frame simp lemmas for common package proof
  patterns.
- Use the generic `QueryCache.cacheQuery` growth lemmas in new package proofs;
  add finite-cardinality specializations only if future call sites genuinely
  need `ncard` instead of `encard`.
- Add package-handler invariant preservation lemmas close to the package
  definitions.
- Consider a small `heap_frame` or `package_step` tactic only after the lemmas
  have stabilized.

Target files:

- `VCVio/HeapSSP/Heap.lean`
- `VCVio/HeapSSP/Package.lean`
- `VCVio/OracleComp/QueryTracking/Structures.lean`
- `VCVio/CryptoFoundations/FiatShamir/Sigma/HeapSSP/Hops.lean`

## Cutover Plan

### Phase A: Make the current FS-CMA chain honest

TODO:

- Keep the HeapSSP chain building.
- Preserve the current partial proofs and local invariants.
- Keep the verifier `+1` removal in place by routing H3 through
  `cmaReal_cmaSim_advantage_le_H3_bound_of_expectedSCost` and the
  candidate/verify split.
- Do not add more bespoke proof bulk unless it directly informs reusable
  infrastructure.

Recent concrete progress:

- Added `expectedSCost_bind_eq_of_right_zero` in
  `VCVio/ProgramLogic/Relational/SimulateQ.lean`.
- Added the factored adversary shape in
  `VCVio/CryptoFoundations/FiatShamir/Sigma/HeapSSP/Bridge.lean`:
  `candidateAdv`, `signedCandidateAdv`, and `verifyFreshComp`.
- Added `cmaSignEpsCore_expectedSCost_le` and
  `cmaReal_cmaSim_advantage_le_H3_bound_of_expectedSCost` in
  `VCVio/CryptoFoundations/FiatShamir/Sigma/HeapSSP/Hops.lean`.
- Updated `cma_advantage_le_fork_bound` so the beta term is
  `qS * (qS + qH) * β`, while the final verification query remains in the H5
  Boolean event.
- Moved `simulatedNmaAdv` and its query-bound theorem from
  `Sigma/Security.lean` to `Sigma/CmaToNma.lean`, then routed
  `Sigma/Security.lean`'s public `euf_cma_to_nma` theorem through the HeapSSP
  chain.
- Removed the obsolete legacy `hashAndSign_cma_to_nma_bound` sorry. The
  non-HeapSSP CMA-to-NMA theorem is no longer a parallel proof path.
- Removed the stale `simChalUniformGivenCommit` hypothesis from the public
  Sigma FS CMA bounds; the current HeapSSP chain consumes HVZK and simulator
  commit predictability directly.
- Added `Package.runStateProb`, output-event bridge lemmas, and
  `Package.run_bind` so H2/H5 proofs can reason over output plus final heap
  without unfolding package execution.
- Added `Package.shiftLeft_bind` and the FS-specific
  `cmaToNma_shiftLeft_signedFreshAdv_eq_bind` lemma, pinning H5 to the same
  candidate/verify split used by H3.
- Promoted the private FS-specific WriterT/StateT signed-message log bridge to
  the generic `QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog`
  theorem in `VCVio/OracleComp/QueryTracking/LoggingOracle.lean`, and removed
  the duplicate private proof from `Sigma/Security.lean`.
- Added generic `QueryCache.toSet_cacheQuery_subset_insert` and
  `QueryCache.toSet_encard_cacheQuery_le` lemmas so cache-growth reasoning is
  no longer proved inside the FS-CMA hop file.
- Promoted the query-log freshness bridge to
  `QueryLog.wasQueried_eq_decide_mem_map_fst`, removing another private
  Sigma-only helper.
- Added `withCacheOverlay_bind`, `withCacheOverlay_map`, and
  `withCacheOverlay_bind_pure` so runtime/cache proofs can decompose cached
  computations without unfolding the `StateT` implementation.

### Phase B: Build core reusable infrastructure

TODO:

- Add invariant-aware HeapSSP identical-until-bad.
- Extend the initial event-level package probability API into the H2/H5
  proofs.
- Add TV bind plus bad-event lemmas.
- Add query-bound transport lemmas.

This phase should make H3 and the expected-cost/signing-hop arguments short and
structural.

### Phase C: Cut over structural experiment equivalences

TODO:

- Prove H2 using public logging/runtime equivalence lemmas.
- Instantiate `QueryImpl.map_run_withLogging_inputs_eq_run_appendInputLog` for
  the public signing oracle and the HeapSSP signing-log state.
- Finish the remaining runtime/cache equivalence lemmas that identify the
  public `FiatShamir.runtime` random-oracle cache with the HeapSSP `roCache`
  cell through signing and final verification.
- Use the new `withCacheOverlay_*` API rather than unfolding `cachingOracle`
  directly, except at the single-query hit/miss boundary.
- Remove duplicate proof obligations between the legacy CMA-to-NMA file and the
  HeapSSP bridge.

### Phase D: Cut over the fork theorem

TODO:

- Finish the managed-RO H5 theorem as a reusable theorem over the NMA/fork
  interface.
- Align the theorem with replay-based forking so ambient randomness is handled
  explicitly.
- Keep the seed-based forking theorem intact, but make replay forking the path
  used by Fiat-Shamir when live ambient randomness is present.

### Phase E: Route public EUF-CMA through HeapSSP

Status: complete for the non-aborting Sigma FS-CMA path.

Completed:

- Replaced the public `euf_cma_to_nma` dependency on the legacy
  `hashAndSign_cma_to_nma_bound` proof path with the HeapSSP chain.
- Removed the legacy theorem because no caller needs the old parallel
  statement.
- Tightened the final `euf_cma_bound` theorem so it depends only on the shared
  HeapSSP and replay-fork infrastructure hypotheses it actually consumes.

### Phase F: Cut over existing proven hybrids

TODO:

- Inventory existing proven game-hopping/hybrid proofs that use older bespoke
  proof styles.
- Port representative examples to the new package/event/query-bound APIs.
- Keep the old proof style only when it is genuinely simpler; otherwise remove
  duplicated local lemmas after the cutover.
- Update `docs/agents/proof-workflows.md` once the new APIs are stable enough
  to be the recommended workflow.

## Exit Criteria

The infrastructure work is successful when:

- H2, H3, and H5 are short, mostly compositional proofs.
- High-level FS-CMA theorem statements do not expose internal query-bound
  assumptions for wrapper adversaries when those bounds are derivable.
- Freshness and final verification events can be stated over final package
  state instead of encoded through ad hoc Boolean wrappers.
- Replay forking is the canonical Fiat-Shamir path when ambient randomness must
  be replayed.
- Existing proven hybrids can be cut over without increasing proof size.
- Future Fiat-Shamir-style reductions reuse the same package, event, query, and
  replay-fork theorems rather than rebuilding the chain by hand.
