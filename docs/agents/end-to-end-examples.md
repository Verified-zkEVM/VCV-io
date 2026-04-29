# End-to-End Crypto Examples

This page collects compact examples that show how the cryptographic framework
layers compose on concrete schemes.

## Schnorr Signature EUF-CMA

An end-to-end EUF-CMA reduction for the Schnorr digital signature lives in
[`Examples/Signature.lean`](../../Examples/Signature.lean). It is a compact
illustration of how the main composition layers of the framework fit together
on a single concrete scheme. Reading order:

1. **Σ-protocol:** [`Examples/Schnorr.lean`](../../Examples/Schnorr.lean)
   defines `Schnorr.sigma` and proves perfect completeness, special soundness,
   and perfect HVZK, plus the two simulator-distribution facts the
   Fiat-Shamir reduction needs (`sigma_simCommitPredictability` and
   `sigma_simChalUniformGivenCommit`).
2. **Generic Fiat-Shamir transform:**
   [`VCVio/CryptoFoundations/FiatShamir/Sigma.lean`](../../VCVio/CryptoFoundations/FiatShamir/Sigma.lean)
   builds a signature scheme `FiatShamir σ hr M` from any Σ-protocol `σ` and
   generable relation `hr`, with a fresh random-oracle runtime
   `FiatShamir.runtime`.
3. **Reductions:**
   [`VCVio/CryptoFoundations/FiatShamir/Sigma/Security.lean`](../../VCVio/CryptoFoundations/FiatShamir/Sigma/Security.lean)
   exposes `euf_cma_to_nma` (CMA → managed-RO NMA via HVZK simulation) and
   `euf_nma_bound` (managed-RO NMA → witness extraction via the replay forking
   lemma and special soundness), composed in `euf_cma_bound`.
4. **Forking lemma:** the replay-based forking lemma lives in
   [`VCVio/CryptoFoundations/ReplayFork.lean`](../../VCVio/CryptoFoundations/ReplayFork.lean)
   and is specialized to Fiat-Shamir managed-RO traces in
   [`VCVio/CryptoFoundations/FiatShamir/Sigma/Fork.lean`](../../VCVio/CryptoFoundations/FiatShamir/Sigma/Fork.lean)
   as `Fork.replayForkingBound`.
5. **Hardness:** the discrete-log assumption and the generable relation lift
   live in
   [`VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean`](../../VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean).

The combined statement, `Schnorr.signature_euf_cma`, instantiates
`FiatShamir.euf_cma_bound` with the Schnorr Σ-protocol facts and delivers the
Pointcheval-Stern bound

```
ε' · ( ε' / (qH + 1)  -  1 / |F| )   ≤   Pr[ B succeeds in dlogExp g ],
ε' := ε  -  qS · (qS + qH) / |F|  -  δ_verify,
```

where `ε` is the EUF-CMA advantage of an adversary with `qS` signing-oracle
queries and `qH` random-oracle queries, and `δ_verify` is the verification
slack supplied by the caller via `SigmaProtocol.verifyChallengePredictability`.

## ROM Commitment Scheme

A second end-to-end example, exercising a different axis of the framework
(caching, logging, identical-until-bad, birthday bounds), lives in
[`Examples/CommitmentScheme.lean`](../../Examples/CommitmentScheme.lean). It
proves binding, extractability, and hiding bounds for the textbook ROM
commitment scheme

```
Commit(m) = (H(m, s), s),     s ←$ S,
Check(c, m, s) = (H(m, s) == c).
```

Reading order:

1. **Shared ROM definitions:**
   [`Examples/CommitmentScheme/Common.lean`](../../Examples/CommitmentScheme/Common.lean)
   defines the random oracle `CMOracle : (M × S) → C`, the scheme algorithms
   `CMCommit` and `CMCheck`, and the basic single-fresh-query unpredictability
   bound `probEvent_from_fresh_query_le_inv` (`1/|C|`) that all three security
   proofs reduce to.
2. **Binding:**
   [`Examples/CommitmentScheme/Binding.lean`](../../Examples/CommitmentScheme/Binding.lean)
   proves both a tight bound `binding_bound` (`(t·(t-1) + 2) / (2·|C|)`) by
   direct case-split on cache collisions versus fresh verification queries,
   and a looser standard-model-style bound `binding_bound_via_cr_chain`
   mirroring `bindingAdvantage_toCommitment_le_keyedCRAdvantage` from
   [`VCVio/CryptoFoundations/HashCommitment.lean`](../../VCVio/CryptoFoundations/HashCommitment.lean).
3. **Extractability:**
   [`Examples/CommitmentScheme/Extractability.lean`](../../Examples/CommitmentScheme/Extractability.lean)
   exhibits the explicit log-scanning extractor `CMExtract` and proves
   `extractability_bound` (`(t·(t-1) + 2) / (2·|C|)`, for `t ≥ 3`).
4. **Hiding:** the
   [`Examples/CommitmentScheme/Hiding/`](../../Examples/CommitmentScheme/Hiding/)
   subtree builds the identical-until-bad chain. The packaged theorem
   `hiding_bound_finite` in
   [`Examples/CommitmentScheme/Hiding/Main.lean`](../../Examples/CommitmentScheme/Hiding/Main.lean)
   delivers the bound

```
tvDist(hidingMixedReal A, hidingMixedSim A)  ≤  t / |S|,
```

where the salt is sampled inside the experiment and `t` is the adversary's
total query budget. The bound is intrinsically averaged over the salt: the
per-salt version is false.

The framework machinery exercised: `cachingOracle`, `loggingOracle`,
`IsTotalQueryBound`, the birthday bound
`probEvent_cacheCollision_le_birthday_total_tight`, and the identical-until-bad
TVD bound `tvDist_simulateQ_le_probEvent_bad_dist`.
