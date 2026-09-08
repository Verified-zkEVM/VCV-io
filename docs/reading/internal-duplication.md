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
`PRFTagReader` example) are unchanged because the unfolding is definitional.

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
already delegates to `AddWriterT.expectedCost`. The odd one out is `CountingOracle.withCost`,
which writes into the *multiplicative* `QueryCount` writer (`Structures.lean` gives
`QueryCount ι := ι → ℕ` a `Monoid` whose `mul` is `+`). Folding it onto `AddWriterT` is blocked
by the `QueryCount` design item in the ledger: the definition is `@[reducible]`, so that
`Monoid` instance leaks onto every `ι → ℕ` (`#synth Monoid (ℕ → ℕ)` finds it), and the fold has
to change the carrier (the repo already uses `κ →₀ ℕ` in `ResourceProfile.lean`) before it can
change the writer.

**`QueryImpl`/`ProbHandler` versus PolyFun's `Sampler`/`Decoration`.** A `QueryImpl spec m` is a
per-query interpretation into `m`; PolyFun's `Spec.Sampler m spec` is `Decoration (fun X => m X)
spec`, the same data in the interaction layer's vocabulary (`VCVio/Interaction/UC/Runtime.lean`
already threads samplers through processes). `ProbHandler` (`VCVio/OracleComp/Coinductive/
DynSystem.lean`) is a third spelling for the coinductive runtime. These stay two vocabularies for
one concept until the Kleisli–Mealy wiring that PolyFun's own ledger tracks lands; at that point
`QueryImpl` should become the `OracleSpec`-indexed alias of the PolyFun notion, the way the
`OracleSpec` operations already are.
