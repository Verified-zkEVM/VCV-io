# Machine-Checked Cryptographic Proofs in Lean

VCVio is a Lean library for machine-checked proofs about cryptographic games, primitives,
protocols, and implementations. The core framework provides:

* A monadic syntax for representing computations with oracle access (`OracleComp`), with probabilistic computations (`ProbComp`) as a special case of having uniform selection oracles.
* A measure-valued denotational semantics (`evalDist` / `𝒟[…]`) for probabilistic computations,
  with an explicit finite adapter (`evalSPMF` / `𝒮[…]`) and scalar tools for output, event, and
  failure probabilities (`probOutput`/`probEvent`/`probFailure`).
* An operational semantics (`simulateQ`) for implementing/simulating the behavior of a computation's oracles, including implementations of random oracles, query logging, reductions, etc.
* A program logic with relational (pRHL-style) and unary (Hoare-style) proof modes, with interactive tactics for stepping through game-based proofs.

It also provides definitions for cryptographic primitives such as symmetric/asymmetric encryption,
signatures, $\Sigma$-protocols, and transforms like Fiat-Shamir and Fischlin.

On top of the generic framework, `LatticeCrypto` covers ML-DSA, ML-KEM, and Falcon, including
proof-level abstractions and executable concrete implementations. `HashSig` covers SLH-DSA
(SPHINCS+, FIPS 205), and the interaction layer supports computational interpretations of
interactive and UC-style systems.

Assuming Lean and Lake are already installed, the project can be built by just running:

```
lake exe cache get && lake build
```

`lake build` covers the seven proof libraries. `./scripts/validate.sh` runs the fast per-PR
checks locally; add `--lint`, `--test`, or `--axioms` for those CI passes. `lake test` builds the
test libraries and runs the test executables, and `lake lint` runs source-style and environment checks
(see `AGENTS.md`, *Building*).

CI's timed build covers the non-test Lean libraries `ToMathlib`, `VCVio`,
`LatticeCrypto`, `Extern`, `HashSig`, `Examples`, and `VCVioWidgets`.
The build timing report parses per-file timings for that same set.
Test libraries and test executables are intentionally outside the timed build; CI
only times the smoke module separately with `lake env lean VCVioTest/Smoke.lean`.

VCVio can also be used as a dependency in another Lake project via a
`[[require]]` on this repository, and that works out of the box. The native C
backends under `third_party/` live in git submodules, which Lake does not fetch
for dependencies, so the corresponding `extern_lib` targets fall back to empty
stub archives when those sources are absent. Downstream executables still link
unless they call VCVio's native FFI symbols; to enable the real backends, run
`git submodule update --init --recursive` inside `.lake/packages/VCVio` and
rebuild. (In this repository itself the same command at the repo root enables the
native test executables, which `lake test -- --ffi` then builds and runs.)

Mathematical foundations such as probability theory, computational complexity, and algebraic structures are based on or written to the Mathlib project (see [MATHLIB4](REFERENCES.md#mathlib4)), making all of that library usable in constructions and proofs.

The project aims to enable proof effort comparable to that found in Mathlib. It is particularly
well suited to concrete security bounds for reductions and to the security of individual
cryptographic primitives. It supports foundational arguments about forking and rewinding
adversaries, Fiat-Shamir-style transforms, interactive systems, and UC-style composition.
Asymptotic security and query-cost and expected-cost reasoning are also supported. Polynomial-time
infrastructure and some tooling and automation remain under active development.

## Repository Map

- `VCVio/` contains the oracle-computation framework, probability semantics, program logic, and generic crypto abstractions.
- `LatticeCrypto/` contains lattice algebra, hardness assumptions, ML-DSA, ML-KEM, Falcon, and their concrete implementations.
- `Extern/` contains the native FFI surface: the `@[extern]` bindings and the FFI-backed concrete instances. Its `extern_lib`s build as empty stubs when the `third_party/` submodules are absent.
- `HashSig/` contains hash-based signatures: proof-level specifications, component-level FIPS 205
  conformance results, and security-facing interfaces for SLH-DSA. Neither an unforgeability
  theorem nor a complete FIPS conformance result is proved yet; see
  `docs/design/slh-dsa-status-and-roadmap.md`.
- `LatticeCryptoTest/` contains ACVP vectors, regression tests, and differential checks against native backends.
- `HashSigTest/` contains hash-signature test and validation modules.
- `Examples/` contains compact framework proofs including OneTimePad, ElGamal, and Schnorr.
- `Interop/` contains experimental bridges to Rust verification frontends such as hax and Aeneas.
- `csrc/` contains C FFI bridges for the native ML-DSA, ML-KEM, and Falcon implementations used in tests.
- `third_party/` contains the native backends as git submodules, used by the `Extern` FFI layer and differential tests.
- `ToMathlib/` contains supporting constructions that may eventually move to a separate project.

For agent-oriented repo guidance, see [`AGENTS.md`](AGENTS.md) and the focused docs in
[`docs/agents/`](docs/agents/), especially [`docs/agents/lattice.md`](docs/agents/lattice.md)
for lattice-specific entry points and workflows.

External papers and project references cited in this repo are centralized in
[`REFERENCES.md`](REFERENCES.md).

## End-to-end examples

For compact examples showing how the framework layers compose on concrete
schemes, see [`docs/agents/end-to-end-examples.md`](docs/agents/end-to-end-examples.md).
It covers the Schnorr signature EUF-CMA reduction and the ROM commitment scheme
proofs of binding, extractability, and hiding.

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

`evalDist` exposes the successful-output law as a Mathlib `Measure`; missing mass represents
failure or nontermination. `evalSPMF` is the explicit `OptionT PMF` compatibility and executable
backend. For `ProbComp` (i.e. `OracleComp unifSpec`), `evalSPMF` is definitionally equal to
`simulateQ` with uniform implementations.
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

## Name

**VCVio** stands for **Verifying Cryptography via Interactions and Oracles**.

The initials **VCV** also admit the Latin motto *Veritas cryptographica vincit*
(“cryptographic truth prevails”). The **io** suffix reflects the interactions and oracles at the
heart of the library: interactions arise between protocol participants, between computations and
their oracle environments, and between specifications and implementations through simulation and
effect handlers; oracles provide a common abstraction for cryptographic games, reductions,
probabilistic semantics, and executable interpretations.

VCVio's framework is inspired by FCF (see [FCF-REPO](REFERENCES.md#fcf-repo) and
[FCF14](REFERENCES.md#fcf14)), the Foundational Cryptography Framework for Rocq (formerly Coq),
particularly its use of embedded probabilistic and oracle-aided computations with semantic models
and derived rules for game-based reasoning. Where FCF gives each computation a single oracle
interface, VCVio uses indexed oracle families represented by polynomial functors and provides
compositional infrastructure for combining, simulating, and interpreting them.
