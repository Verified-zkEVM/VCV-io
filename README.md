# Formally Verified Cryptography Proofs in Lean 4

This library aims to provide a foundational framework in Lean for reasoning about cryptographic protocols in the computational model. The core part of the framework provides:

* A monadic syntax for representing computations with oracle access (`OracleComp`), with probabilistic computations (`ProbComp`) as a special case of having uniform selection oracles.
* A denotational semantics (`evalDist`) for assigning probability distributions to probabilistic computations, and tools for reasoning about the probabilities of particular outputs or events (`probOutput`/`probEvent`/`probFailure`).
* An operational semantics (`simulateQ`) for implementing/simulating the behavior of a computation's oracles, including implementations of random oracles, query logging, reductions, etc.
* A program logic with relational (pRHL-style) and unary (Hoare-style) proof modes, with interactive tactics for stepping through game-based proofs.

It also provides definitions for cryptographic primitives such as symmetric/asymmetric encryption, signatures, $\Sigma$-protocols, and transforms like Fiat-Shamir and Fischlin.

Assuming Lean 4 and lake are already installed, the project can be built by just running:

```
lake exe cache get && lake build
```

Mathematical foundations such as probability theory, computational complexity, and algebraic structures are based on or written to the Mathlib project (see [MATHLIB4](REFERENCES.md#mathlib4)), making all of that library usable in constructions and proofs.

Generally the project aims to enable proof complexity comparable to that found in Mathlib.
It's most well suited to proving concrete security bounds for reductions, and for establishing the security of individual cryptographic primitives.
It allows for fully foundational proofs of things like forking/rewinding adversaries and Fiat-Shamir style transforms, but has less support for composing a large number of primitives into complex protocols.
Asymptotic reasoning is also supported, but tooling and automation for this is currently limited.
Computational complexity is not considered.

The `VCVio` directory provides all of the foundations and framework definitions / APIs.
`Examples` contains example proofs including OneTimePad (perfect secrecy), ElGamal (IND-CPA via DDH), and Schnorr ($\Sigma$-protocol completeness, soundness, HVZK).
`ToMathlib` contains constructions that eventually should be moved to another project.

External papers and project references cited in this repo are centralized in
[`REFERENCES.md`](REFERENCES.md).

## Acknowledgments

Parts of the current program-logic refactor use an ordered monad-algebra perspective adapted from
the Loom project (see [LOOM-REPO](REFERENCES.md#loom-repo) and [LOOM26](REFERENCES.md#loom26)).

## Contributions

Contributions to the library are welcome via PR.
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
* **Interactive tactics**: `rvcgen_step`, `rvcgen`, `qvcgen_step`, `game_trans`, and explicit probability-equality controls such as `qvcgen_step rw` / `qvcgen_step rw congr'` for stepping through game-based proofs.

## Other Useful Definitions

Predicates and tools for computations:

* `allWhen`/`someWhen` - recursively check predicates on a computation's syntax tree given allowed query outputs
* `IsQueryBound` - bound the number of queries a computation makes (with per-index variant `IsPerIndexQueryBound`)
* `QueryImpl.withLogging`/`withCaching`/`withPregen` - modifiers that wrap a query implementation with logging, caching, or pre-generated answers

## Trivia

`VCV-io` is inspired by FCF (see [FCF-REPO](REFERENCES.md#fcf-repo) and [FCF14](REFERENCES.md#fcf14)), a foundational framework for verified cryptography in Coq. Similar to FCF, we formalize the notion of oracle computations as central to modeling cryptographic games, primitives, and protocols. In contrast to FCF, our handling of oracles is much more refined — we allow for an *indexed* family of oracles via polynomial functors, and build significant infrastructure for combining and simulation of oracles.

The name `VCV` is reverse of `FCF` under the involution `F <=> V` (same number of characters going from the beginning, versus the end, of the English alphabet). One backronym for the name is "Verified Cryptography via Indexed Oracles".
