# Formally Verified Cryptography Proofs in Lean 4

This library aims to provide a foundational framework in Lean for reasoning about cryptographic protocols in the computational model. The core part of the framework provides:

* A monadic syntax for representing computations with oracle access (`OracleComp`), with probabilistic computations (`ProbComp`) as a special case of having uniform selection oracles.
* A denotational semantics (`evalDist`) for assigning probability distributions to probabilistic computations, and tools for reasoning about the probabilities of particular outputs or events (`probOutput`/`probEvent`/`probFailure`).
* An operational semantics (`simulateQ`) for implementing/simulating the behavior of a computation's oracles, including implementations of random oracles, query logging, reductions, etc.
* A program logic with relational (pRHL-style) and unary (Hoare-style) proof modes, with interactive tactics for stepping through game-based proofs.

It also provides definitions for cryptographic primitives such as symmetric/asymmetric encryption, signatures, $\Sigma$-protocols, and transforms like Fiat-Shamir and Fischlin.

On top of that generic framework, the repo now contains a dedicated `LatticeCrypto` library for
ML-DSA, ML-KEM, and Falcon, including both proof-level abstractions and executable concrete
implementations.

Assuming Lean 4 and lake are already installed, the project can be built by just running:

```
lake exe cache get && lake build
```

CI's timed build covers the non-test Lean libraries `ToMathlib`, `VCVio`, `FFI`,
`LatticeCrypto`, `Examples`, `VCVioWidgets`, and `Interop`.
The build timing report parses per-file timings for that same set.
Test libraries and test executables are intentionally outside the timed build; CI
only times the smoke module separately with `lake env lean VCVioTest/Smoke.lean`.

Mathematical foundations such as probability theory, computational complexity, and algebraic structures are based on or written to the Mathlib project (see [MATHLIB4](REFERENCES.md#mathlib4)), making all of that library usable in constructions and proofs.

Generally the project aims to enable proof complexity comparable to that found in Mathlib.
It's most well suited to proving concrete security bounds for reductions, and for establishing the security of individual cryptographic primitives.
It allows for fully foundational proofs of things like forking/rewinding adversaries and Fiat-Shamir style transforms, but has less support for composing a large number of primitives into complex protocols.
Asymptotic reasoning is also supported, but tooling and automation for this is currently limited.
Computational complexity is not considered.

## Repository Map

- `VCVio/` contains the oracle-computation framework, probability semantics, program logic, and generic crypto abstractions.
- `LatticeCrypto/` contains lattice algebra, hardness assumptions, ML-DSA, ML-KEM, Falcon, and their concrete implementations.
- `LatticeCryptoTest/` contains ACVP vectors, regression tests, and differential checks against native backends.
- `Examples/` contains compact framework proofs including OneTimePad, ElGamal, and Schnorr.
- `csrc/` contains C FFI bridges for the native ML-DSA, ML-KEM, and Falcon implementations used in tests.
- `third_party/` contains the vendored native backends used by the FFI layer.
- `ToMathlib/` contains supporting constructions that may eventually move to a separate project.

For agent-oriented repo guidance, see [`AGENTS.md`](AGENTS.md) and the focused docs in
[`docs/agents/`](docs/agents/), especially [`docs/agents/lattice.md`](docs/agents/lattice.md)
for lattice-specific entry points and workflows.

External papers and project references cited in this repo are centralized in
[`REFERENCES.md`](REFERENCES.md).

## End-to-end example: Schnorr signature EUF-CMA

An end-to-end EUF-CMA reduction for the Schnorr digital signature lives in
[`Examples/Signature.lean`](Examples/Signature.lean). It is a compact
illustration of how the main composition layers of the framework fit together
on a single concrete scheme. Reading order:

1. **Σ-protocol:** [`Examples/Schnorr.lean`](Examples/Schnorr.lean) defines
   `Schnorr.sigma` and proves perfect completeness, special soundness, and
   perfect HVZK, plus the two simulator-distribution facts the
   Fiat-Shamir reduction needs (`sigma_simCommitPredictability` and
   `sigma_simChalUniformGivenCommit`).
2. **Generic Fiat-Shamir transform:**
   [`VCVio/CryptoFoundations/FiatShamir/Sigma.lean`](VCVio/CryptoFoundations/FiatShamir/Sigma.lean)
   builds a signature scheme `FiatShamir σ hr M` from any Σ-protocol `σ` and
   generable relation `hr`, with a fresh random-oracle runtime
   `FiatShamir.runtime`.
3. **Reductions:**
   [`VCVio/CryptoFoundations/FiatShamir/Sigma/Security.lean`](VCVio/CryptoFoundations/FiatShamir/Sigma/Security.lean)
   exposes `euf_cma_to_nma` (CMA → managed-RO NMA via HVZK simulation) and
   `euf_nma_bound` (managed-RO NMA → witness extraction via the replay
   forking lemma and special soundness), composed in `euf_cma_bound`.
4. **Forking lemma:** the replay-based forking lemma lives in
   [`VCVio/CryptoFoundations/ReplayFork.lean`](VCVio/CryptoFoundations/ReplayFork.lean)
   and is specialized to Fiat-Shamir managed-RO traces in
   [`VCVio/CryptoFoundations/FiatShamir/Sigma/Fork.lean`](VCVio/CryptoFoundations/FiatShamir/Sigma/Fork.lean)
   as `Fork.replayForkingBound`.
5. **Hardness:** the discrete-log assumption and the generable relation lift
   live in
   [`VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean`](VCVio/CryptoFoundations/HardnessAssumptions/DiffieHellman.lean).

The combined statement, `Schnorr.signature_euf_cma`, instantiates
`FiatShamir.euf_cma_bound` with the Schnorr Σ-protocol facts and delivers
the Pointcheval-Stern bound

```
ε' · ( ε' / (qH + 1)  -  1 / |F| )   ≤   Pr[ B succeeds in dlogExp g ],
ε' := ε  -  qS · (qS + qH) / |F|  -  δ_verify,
```

where `ε` is the EUF-CMA advantage of an adversary with `qS` signing-oracle
queries and `qH` random-oracle queries, and `δ_verify` is the verification
slack supplied by the caller via `SigmaProtocol.verifyChallengePredictability`.

## End-to-end example: ROM commitment scheme

A second end-to-end example, exercising a different axis of the framework
(caching, logging, identical-until-bad, birthday bounds), lives in
[`Examples/CommitmentScheme.lean`](Examples/CommitmentScheme.lean). It
proves binding, extractability, and hiding bounds for the textbook ROM
commitment scheme

```
Commit(m) = (H(m, s), s),     s ←$ S,
Check(c, m, s) = (H(m, s) == c).
```

Reading order:

1. **Shared ROM definitions:**
   [`Examples/CommitmentScheme/Common.lean`](Examples/CommitmentScheme/Common.lean)
   defines the random oracle `CMOracle : (M × S) → C`, the scheme
   algorithms `CMCommit` and `CMCheck`, and the basic single-fresh-query
   unpredictability bound `probEvent_from_fresh_query_le_inv` (`1/|C|`)
   that all three security proofs reduce to.
2. **Binding:**
   [`Examples/CommitmentScheme/Binding.lean`](Examples/CommitmentScheme/Binding.lean)
   proves both a tight bound `binding_bound` (`(t·(t-1) + 2) / (2·|C|)`)
   by direct case-split on cache collisions versus fresh verification
   queries, and a looser standard-model-style bound
   `binding_bound_via_cr_chain` mirroring
   `bindingAdvantage_toCommitment_le_keyedCRAdvantage` from
   [`VCVio/CryptoFoundations/HashCommitment.lean`](VCVio/CryptoFoundations/HashCommitment.lean).
3. **Extractability:**
   [`Examples/CommitmentScheme/Extractability.lean`](Examples/CommitmentScheme/Extractability.lean)
   exhibits the explicit log-scanning extractor `CMExtract` and proves
   `extractability_bound` (`(t·(t-1) + 2) / (2·|C|)`, for `t ≥ 3`).
4. **Hiding:** the
   [`Examples/CommitmentScheme/Hiding/`](Examples/CommitmentScheme/Hiding/)
   subtree builds the identical-until-bad chain. The packaged theorem
   `hiding_bound_finite` in
   [`Examples/CommitmentScheme/Hiding/Main.lean`](Examples/CommitmentScheme/Hiding/Main.lean)
   delivers the bound

```
tvDist(hidingMixedReal A, hidingMixedSim A)  ≤  t / |S|,
```

   where the salt is sampled inside the experiment and `t` is the adversary's
   total query budget. The bound is intrinsically averaged over the salt:
   the per-salt version is false.

The framework machinery exercised: `cachingOracle`, `loggingOracle`,
`IsTotalQueryBound`, the birthday bound
`probEvent_cacheCollision_le_birthday_total_tight`, and the
identical-until-bad TVD bound `tvDist_simulateQ_le_probEvent_bad_dist`.

## Acknowledgments

Parts of the current program-logic refactor use an ordered monad-algebra perspective adapted from
the Loom project (see [LOOM-REPO](REFERENCES.md#loom-repo) and [LOOM26](REFERENCES.md#loom26)).

## Contributions

Contributions to the library are welcome via PR.
See [`CONTRIBUTING.md`](CONTRIBUTING.md) for contribution workflow and the repo's explicit
attribution / file-header policy.
See [LEANCRYPTO3-REPO](REFERENCES.md#leancrypto3-repo) for an outdated version of the library in Lean 3.

# Framework Overview

## Representing Computations

The main representation of computations with oracle access is a type `OracleComp spec α` where `spec : OracleSpec ι` specifies a set of oracles (indexed by type `ι`) and `α` is the final return type.
`OracleSpec ι` is a function `ι → Type v`: the index type `ι` serves as the domain (query inputs) and `spec t` is the range (response type for query `t`).
`OracleComp` is defined as a free monad over the polynomial functor associated to `spec`.

This results in a representation with two canonical forms (see `OracleComp.construct` and `OracleComp.inductionOn`):

* `pure x` — return a value
* `query t >>= f` — make an oracle query `t : spec.Domain` and continue with `f : spec.Range t → OracleComp spec α`

Failure (via `Alternative`) is available through `OptionT (OracleComp spec)`, with a separate eliminator `OracleComp.inductionOnOptional`.

`ProbComp α` is the special case where `spec` only allows for uniform random selection (`OracleComp unifSpec α`).
`OracleComp (T →ₒ U) α` has access to a single oracle with input type `T` and output type `U`.
`OracleComp (spec₁ + spec₂) α` has access to both sets of oracles, indexed by a sum type.

## Implementing and Simulating Oracles

The main semantics of `OracleComp` come from a function `simulateQ impl comp` that recursively substitutes oracle queries in the syntax tree of `comp` using `impl : QueryImpl spec m` (which is just a function `(x : spec.Domain) → m (spec.Range x)`).
This can also be seen as a way of providing event handlers for queries in the computation.
The embedding can be into any `Monad`.

This provides a mechanism to implement oracle behaviors, but can also be used to modify behaviors without fully implementing them (see `QueryImpl.withLogging`, `QueryImpl.withCaching`, `QueryImpl.withPregen`).

`runIO` can be used to embed into the `IO` monad to run a `ProbComp` computation using Lean's random number generation.

## Probabilities of Outputs and Events

Semantics for probability calculations come from using `simulateQ` to interpret the computation in another monad.
`support` can be used to embed in the `Set` monad to get the possible outputs of a computation.

`evalDist` embeds a computation into the `SPMF` monad (`OptionT PMF`) by using uniform distributions for each oracle's range.
For `ProbComp` (i.e. `OracleComp unifSpec`), `evalDist` is definitionally equal to `simulateQ` with uniform implementations.
We introduce notation:

* `Pr[= x | comp]` - probability of output `x`
* `Pr[p | comp]` - probability of event `p`
* `Pr[⊥ | comp]` - probability of the computation failing

The typeclass `NeverFail mx` asserts that `Pr[⊥ | mx] = 0`, and is used to propagate non-failure guarantees through monadic combinators.

## Automatic Coercions

Lean's `MonadLift` type-class allows computations to automatically lift to other monads when regular type-checking fails (the same mechanism Lean uses to lift along monad transformers).
We implement two main cases:

* `OracleQuery spec α` lifts to `OracleComp spec α`
* `OracleComp sub_spec α` lifts to `OracleComp super_spec α` whenever there is an instance of `sub_spec ⊂ₒ super_spec` available

The second case includes things like `spec₁ ⊂ₒ (spec₁ + spec₂)` and `spec₂ ⊂ₒ (spec₁ + spec₂)`, as well as many transitive cases. Generally lifting should be automatic if the left set of specs is an (ordered) sub-sequence of the right specs.

## Program Logic

The library includes a program logic (`VCVio.ProgramLogic`) inspired by pRHL and ordered monad-algebra approaches. It provides:

* **Relational proof mode** (`by_equiv`): Coupling-based reasoning via `RelTriple` for proving game equivalence or bounding advantage between two computations.
* **Unary proof mode** (`by_hoare`): Quantitative Hoare triples for bounding probabilities of events in a single computation.
* **Interactive tactics**: `rvcstep`, `rvcgen`, `vcstep`, `game_trans`, and explicit probability-equality controls such as `vcstep rw` / `vcstep rw congr'` for stepping through game-based proofs.

## Other Useful Definitions

Predicates and tools for computations:

* `allWhen`/`someWhen` - recursively check predicates on a computation's syntax tree given allowed query outputs
* `IsQueryBound` - bound the number of queries a computation makes (with per-index variant `IsPerIndexQueryBound`)
* `QueryImpl.withLogging`/`withCaching`/`withPregen` - modifiers that wrap a query implementation with logging, caching, or pre-generated answers

## Trivia

`VCV-io` is inspired by FCF (see [FCF-REPO](REFERENCES.md#fcf-repo) and [FCF14](REFERENCES.md#fcf14)), a foundational framework for verified cryptography in Coq. Similar to FCF, we formalize the notion of oracle computations as central to modeling cryptographic games, primitives, and protocols. In contrast to FCF, our handling of oracles is much more refined — we allow for an *indexed* family of oracles via polynomial functors, and build significant infrastructure for combining and simulation of oracles.

The name `VCV` is reverse of `FCF` under the involution `F <=> V` (same number of characters going from the beginning, versus the end, of the English alphabet). One backronym for the name is "Verified Cryptography via Indexed Oracles".
