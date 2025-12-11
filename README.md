# Formally Verified Cryptography Proofs in Lean 4

This library aims to provide a foundational framework in Lean for reasoning about cryptographic protocols in the computational model. The core part of the framework provides:

* A monadic syntax for representing computations with oracle access (`OracleComp`), with probabilistic computations (`ProbComp`) as a special case of having uniform selection oracles
* A denotational semantics (`evalDist`) for assigning probability distributions to probabilistic computations, and tools for reasoning about the probabilities of particular outputs or events (`probOutput`/`probEvent`/`probFailure`).
* An operational semantics (`simulateQ`) for implementing/simulating the behavior of a computation's oracles, including implementations of random oracles, query logging, reductions, etc.

It also provides definitions for cryptographic primitives such as symmetric/asymmetric encryption, (ring) signatures, $\Sigma$-protocols, hashing algorithms, etc. 

Assuming Lean 4 and lake are already installed, the project can be built by just running:

```
lake exe cache get && lake build
```

Mathematical foundations such as probability theory, computational complexity, and algebraic structures are based on or written to the [Mathlib](https://github.com/leanprover-community/mathlib4) project, making all of that library usable in constructions and proofs.

Generally the project aims to enable proof complexity comparable to that found in mathlib.
It's most well suited to proving concrete security bounds for reductions, and for establishing the security of individual cryptographic primitives.
It allows for fully foundational proofs of things like forking/rewinding adversaries and Fiat-Shamir style transforms, but has less support for composing a large number of primitives into complex protocols.
Asymptotic reasoning is also supported, but tooling and automation for this is currently limited.
Computational complexity is not considered.

The `VCVio` directory provides all of the foundations and framework definitions / APIs. 
`Examples` contains example constructions of standard cryptographic algorithms. 
`ToMathlib` contains constructions that eventually should be moved to another project.

Contributions to the library are welcome via PR.
See [here](https://github.com/dtumad/lean-crypto-formalization) for an outdated version of the library in Lean 3.

# Framework Overview

## Representing Computations

The main representation of computations with oracle access is a type `OracleComp spec α` where `spec : OracleSpec ι` specifies a set of oracles (indexed by type `ι`) and `α` is the final return type.
This is defined as a free monad over the polynomial functor `OracleQuery spec α` which has only the single constructor `query i t`.

This results in a representation with three canonical forms (see `OracleComp.construct` and `OracleComp.inductionOn`):

* `return x` (`pure x`)
* `failure`
* `do let x ← comp₁; comp₂ x` (`comp₁ >>= comp₂`)

`ProbComp α` is the special case where `spec` only allows for uniform random selection (`OracleComp unifSpec α`).
`OracleComp (T →ₒ U) α` has access to a single oracle with input type `T` and output type `U`.
`OracleComp (spec₁ ++ₒ spec₂) α` has access to both sets of oracles, indexed by a sum type.

## Implementing and Simulating Oracles

The main semantics of `OracleComp` come from a function `simulateQ so comp` that recursively substitutes `query i t` in the syntax tree of `comp` for `so.impl i t`.
This can also be seen as a way of providing event handlers for queries in the computation.
The embedding can be into any `AlternativeMonad`.

This provides a mechanism to implement oracle behaviors, but can also be used to modify behaviors without fully implementing them (see `QueryImpl.withLogging`, `QueryImpl.withCaching`, `QueryImpl.withPregen`).

`runIO` can be used to embed into the `IO` monad to run a `ProbComp` computation using Lean's random number generation.

## Probabilities of Outputs and Events

Semantics for probability calculations come from using `simulateQ` to interpret the computation in another monad.
e.g. `support`/`supportWhen` can be used to embed in the `Set` monad to get the possible outputs of a computation.

`evalDist`/`evalDistWhen` embed a computation into the `PMF` monad, using uniform distributions or a custom distribution specification respectively (Actually `OptionT PMF`, which is essentially a `SPMF` to handle the "missing probability mass" of failure).
`evalDist` is the "expected" denotation for `ProbComp` and we introduce notation:

* `[= x | comp]` - probability of output `x`
* `[p | comp]` - probability of event `p`
* `[⊥ | comp]` - probability of the computation failing

## Automatic Coercions

Lean's `MonadLift` type-class allows computations to automatically lift to other monads when regular type-checking fails (the same mechanism Lean uses to lift along monad transformers).
We implement two main cases:

* `OracleQuery spec α` lifts to `OracleComp spec α`
* `OracleComp sub_spec α` lifts to `OracleComp super_spec α` whenever there is an instance of `sub_spec ⊂ₒ super_spec` available

The second case includes things like `spec₁ ⊂ₒ (spec₁ ++ₒ spec₂)` and `spec₂ ⊂ₒ (spec₁ ++ₒ spec₂)`, as well as many transitive cases. Generally lifting should be automatic if the left set of specs is an (ordered) sub-sequence of the right specs.

## Other Useful Definitions

Predicates on computations:

* `someWhen`/`allWhen` - recursively check predicates on a computation's syntax tree given some allowed query outputs
* `neverFailsWhen`/`mayFailWhen` - check if a computation could fail given a set of allowed query outputs
* `isQueryBound` - bound the number of queries a computation makes

## Trivia

`VCV-io` is inspired by [FCF](https://github.com/adampetcher/fcf), a foundational framework for verified cryptography in Coq. Similar to FCF, we formalize the notion of oracle computations as central to modeling cryptographic games, primitives, and protocols. In contrast to FCF, our handling of oracles is much more refined - we allow for an *indexed* family of oracles (soon to be *dependent* oracles), and build significant infrastructure for combining & simulation of oracles.

The name `VCV` is reverse of `FCF` under the involution `F <=> V` (same number of characters going from the beginning, versus the end, of the English alphabet). One backronym for the name is "Verified Cryptography via Indexed Oracles", though this may not remain accurate in the future (with the switch to dependent oracles / polynomial functors).
