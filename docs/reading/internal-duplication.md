# Internal duplication: where VCVio says the same thing twice

A companion to [`upstream-alignment.md`](upstream-alignment.md), which asks what a *dependency*
already owns. This file asks the same question *inside* the repository: which concepts have two
spellings, which one is canonical, what bridges them today, and what blocks folding the other.
The method is the ledger's: a claim names the declarations it is about, and a "duplicate" verdict
comes with the definitional or propositional bridge that shows the two spellings agree.

Each entry records the state at the date given; re-check the named declarations before relying
on it.

## Folded

**`QueryImpl.PreservesInv` is `StateT.PreservesInv` per query (2026-09-03).**
`VCVio/OracleComp/SimSemantics/StateT/PreservesInv.lean` defined the invariant-preservation
predicate twice: once for a single `StateT σ ProbComp α` computation and once, with the same body
quantified over the query index, for a `QueryImpl spec (StateT σ ProbComp)`. The second is now
`∀ t, StateT.PreservesInv (impl t) Inv`, so `QueryImpl.preservesInv_iff` is `Iff.rfl` and the
`StateT` lemmas (`preservesInv_bind`, `preservesInv_of_statePreserving`, …) apply to each query
implementation directly. The consumers (`ProgrammingOracle`, `CachingOracle`, the
`PRFTagReader` example) retain their statements; the example proofs use the structural rules.

## Layered, not duplicated

**The two Merkle engines.** `VCVio/CryptoFoundations/MerkleTree/Inductive/**` is the binding
and extractability theory over an inductive tree; `MerkleTree/Addressed/**` is the
address-indexed engine the SLH-DSA layer runs on (`HashSig/SLHDSA/MerkleExtractor.lean` speaks
`AddressedMerkleTree.nodeSpec`). `Addressed/Basic.lean` imports `Inductive.Binding`: the addressed
engine is built on the inductive theory rather than beside it, and the earlier `MerkleTree/Vector`
presentation is gone (#616). What remains to check at each XMSS change is that the addressed root
computation and the inductive one agree on the trees XMSS builds; that is a lemma to state once,
not a third engine.

**`OracleSpec` operations versus PolyFun's `PFunctor` operations.** `+`, `×`, `Σ`, and `Π` on
`OracleSpec` are re-declared for the `ι → Type` indexing but are `rfl`-bridged to
`PFunctor.sum`/`sigma`/`pi` (`toPFunctor_add`, `toPFunctor_sigma`, `toPFunctor_mul`,
`toPFunctor_pi` in `VCVio/OracleComp/OracleSpec.lean`); the theory is proved once, on the
`PFunctor` side. The nested-sum transparency note in `docs/agents/gotchas.md` §7 is the one place
where the two presentations need care.

## Open

**Cost-instrumentation layers.** `CostModel`, `CountingOracle`, `WriterCost`, and `QueryCost`
are four presentations of "run the computation and accumulate a cost". `AddWriterT`
(`VCVio/OracleComp/QueryTracking/WriterCost.lean`) is canonical: `CostModel.expectedCost`
already delegates to `AddWriterT.expectedCost`. `QueryImpl.withCost`, defined in
`CountingOracle.lean`, supports arbitrary monoid-valued costs. Its `withCounting` specialization
writes into the *multiplicative* `QueryCount` writer (`Structures.lean` gives
`QueryCount ι := ι → ℕ` a `Monoid` whose `mul` is `+`). Folding it onto `AddWriterT` is blocked
by the `QueryCount` design item in the ledger: the definition is `@[reducible]`, so that
`Monoid` instance leaks onto every `ι → ℕ` (`#synth Monoid (ℕ → ℕ)` finds it), and the fold has
to change the carrier (the repo already uses `κ →₀ ℕ` in `ResourceProfile.lean`) before it can
change the writer.

**Oracle handlers and interaction samplers.** `QueryImpl spec m` already specializes PolyFun's
`PFunctor.Handler m spec.toPFunctor` through `QueryImpl.eq_handler`; `ProbHandler` in
`VCVio/OracleComp/Coinductive/DynSystem.lean` specializes that handler to the discrete probability
backend. `TypeTree.Sampler m tree` decorates every interaction-tree node with a computation of
its answer type. These have different indexing structures: an oracle signature versus a tree
of possible interaction nodes. `VCVio/Interaction/UC/Runtime.lean` consumes the latter through
`TypeTree.samplePath`. A further unification needs an explicit bridge between the index
structures and execution laws, rather than another alias of the existing handler.
