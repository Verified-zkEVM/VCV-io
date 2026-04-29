/-
Copyright (c) 2026 James Waters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Waters
-/
import Examples.CommitmentScheme.Common
import Examples.CommitmentScheme.Binding
import Examples.CommitmentScheme.Extractability
import Examples.CommitmentScheme.Hiding

/-!
# Random-oracle commitment scheme: an end-to-end ROM proof

End-to-end correctness, binding, extractability, and hiding bounds for the
textbook random-oracle commitment scheme

```
Commit(m) = (H(m, s), s),     s ←$ S,
Check(c, m, s) = (H(m, s) == c).
```

The scheme commits to a message `m : M` by sampling a uniform salt `s : S`
and outputting the random-oracle hash `H(m, s)` together with `s` as the
opening. Verification recomputes the hash and compares.

The example exercises the framework's random-oracle layer (`cachingOracle`,
`loggingOracle`), the identical-until-bad TVD bound, and the birthday bound
on cache collisions — all on a single concrete scheme.

## What's in this example

* `binding_bound` — Lemma cm-binding (tight). Bound:
  `(t·(t-1) + 2) / (2·|C|)`.
* `binding_bound_via_cr_chain` — binding via the standard-model CR chain.
  Bound: `(t+2)·(t+1) / (2·|C|)`.
* `extractability_bound` — Lemma cm-extractability (for `t ≥ 3`). Bound:
  `(t·(t-1) + 2) / (2·|C|)`.
* `hiding_bound_finite` — Lemma cm-hiding (averaged, packaged form).
  Bound: `t / |S|`.
* `hiding_bound_avg` — Lemma cm-hiding (averaged technical form). Bound:
  `t / |S|`.

`t` is the adversary's total query bound, `|C|` is the size of the commitment
space, and `|S|` is the size of the salt space.

## Reading order

1. **Shared ROM definitions:** `Examples/CommitmentScheme/Common.lean` defines
   the random oracle `CMOracle : (M × S) → C` and the scheme algorithms
   `CMCommit` and `CMCheck`, plus the basic single-fresh-query
   unpredictability bound `probEvent_from_fresh_query_le_inv` (`1/|C|`) that
   all three security proofs ultimately reduce to.
2. **Binding:** `Examples/CommitmentScheme/Binding.lean` proves both a tight
   bound (`binding_bound`) by direct case-split on cache collisions versus
   fresh verification queries, and a looser bound via the standard-model CR
   chain (`binding_bound_via_cr_chain`). The latter parallels the
   `bindingAdvantage_toCommitment_le_keyedCRAdvantage` →
   `romCRAdvantage_le_birthday` chain in `VCVio/CryptoFoundations/`.
3. **Extractability:** `Examples/CommitmentScheme/Extractability.lean`
   exhibits the explicit log-scanning extractor `CMExtract` and proves
   `extractability_bound` for `t ≥ 3` via the same collision + fresh-query
   decomposition.
4. **Hiding:** `Examples/CommitmentScheme/Hiding/` contains the
   identical-until-bad chain. The split is `Defs` (adversary, four oracle
   implementations including the simulator and the shared counted oracle),
   `CountBounds` (per-salt counter invariants), `LoggingBounds/{Average,
   QuerySalt}` (translation between per-salt and averaged experiments), and
   `Main` (the packaged theorems `hiding_bound_avg` and `hiding_bound_finite`).
   The bound is intrinsically *averaged* over the uniformly random salt: the
   per-salt bound is false (a trivial adversary always querying the
   challenge salt achieves `Pr[bad] = 1`).

## Framework machinery exercised

* `cachingOracle` (`VCVio/OracleComp/QueryTracking/CachingOracle.lean`):
  models the shared random oracle for both adversary and verifier.
* `loggingOracle` (`VCVio/OracleComp/QueryTracking/LoggingOracle.lean`):
  records the commit-phase query trace used by the extractor.
* `IsTotalQueryBound` (`VCVio/OracleComp/QueryTracking/QueryBound.lean`):
  the query budget bookkeeping plumbed through every reduction.
* Birthday bound `probEvent_cacheCollision_le_birthday_total_tight`
  (`VCVio/OracleComp/QueryTracking/Unpredictability.lean`): the
  `n·(n-1) / (2·|C|)` upper bound on cache collisions used by both the
  binding and extractability proofs.
* Identical-until-bad TVD bound `tvDist_simulateQ_le_probEvent_bad_dist`
  (`VCVio/EvalDist/TVDist.lean`): the per-salt distinguishing bound for the
  hiding proof.

## Relation to the generic framework

The generic, scheme-agnostic commitment-scheme structure
`CommitmentScheme PP M C D` lives in
`VCVio/CryptoFoundations/CommitmentScheme.lean`, with definitions for
perfect correctness, perfect hiding, and the computational hiding/binding
experiments. The standard-model `binding ≤ keyed-CR ≤ birthday` chain that
`binding_bound_via_cr_chain` here mirrors lives in
`VCVio/CryptoFoundations/HashCommitment.lean`. The example here is the
ROM-instantiated counterpart that exercises the random-oracle layer
directly rather than abstracting through `KeyedHashFamily`.
-/
