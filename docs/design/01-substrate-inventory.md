# 01 — Substrate Inventory: What Exists, What Is Merged, What Is Disconnected

Audit date 2026-07-22. VCVio `main` = `a5f474fd` ("derive replay forking from PolyFun contexts",
#488). PolyFun `main` = `f887c096` ("Consolidate proof and validation infrastructure", #99).
Everything in this doc is a checkable claim about those trees or named merged PRs.

## 1. VCVio today, layer by layer

### 1.1 Oracle core — already polynomial, with an explicit boundary

`OracleComp spec := PFunctor.FreeM spec.toPFunctor` (`VCVio/OracleComp/OracleComp.lean`), with
`ofFreeM`/`toFreeM` as the *declared* abstraction boundary ("downstream semantics should use this
function instead of unfolding `OracleComp`"). Consequence for all directions: generic PolyFun
constructions transport to `OracleComp` by definitional unfolding through one named seam. #488 is
the template integration PR: replay forking now derives from PolyFun cursor/context machinery.

### 1.2 Handlers and simulation

`QueryImpl`, `simulateQ`, monad-transformer semantics (`SimSemantics/{StateT,WriterT,ReaderT,
OptionT}`), `QueryTracking` (counting/logging/caching, random oracles). These are the "matter"
side in disguise: a `QueryImpl.Stateful I E σ` is a Kleisli–Mealy machine — PolyFun's
`Responder` with `m := StateT σ (OracleComp I)` — but no file states that identification.

### 1.3 State-separating layer

`OracleComp/SimSemantics/StateT/StateSeparating.lean` defines `QueryImpl.Stateful` and — important
existing hook — **state frames built from `PFunctor.Lens.State` very-well-behaved lenses with an
explicit `separated` (non-interference + commuting updates) field**, used by `linkWith`/
`parSumWith`. `VCVio/StateSeparating/` adds `Advantage`, `Hybrid`, `IdenticalUntilBad`,
`DistEquiv`, `IndistAt`, `CellRef`. So the ownership discipline of `05` is not hypothetical: its
one-boundary case is already coded here, just not named as such.

### 1.4 Program logic

Loom-style ordered monad algebras. Unary: `HoareTriple`, `HoarePropTriple`, `Loom/{Qualitative,
Quantitative,Probabilistic,Coherence}` installing `Std.Do'` WP carriers. Relational:
`MAlgRelOrdered`, `CouplingPost` (coupling-existence carrier, definitionally the qualitative
`RelWP`), quantitative `ℝ≥0∞` carrier, `FromUnary`, `ProgrammingOracle`, `SeededFork`. Tactics:
`vcgen`/`rvcgen` + EasyCrypt-vocabulary port. The `outParam` scoping discipline (only one carrier
visible at a time; qualitative carrier is `scoped instance`) is a real constraint on `04`'s bridge
design — bridges must not add a third ambient carrier.

### 1.5 UC layer

Three strata, and the disconnection is precisely between the second and third:

1. **PolyFun abstract**: `OpenTheory` (`PolyFun/Interaction/UC/OpenTheory.lean`) — boundary-indexed
   `Obj` with `map/par/wire/plug` and the lawfulness ladder `IsLawful → IsMonoidal → IsTraced →
   IsCompactClosed → HasPlugWireFactor`. `Emulates`/`UCSecure` and the composition theorems
   (`Emulates.par_compose` at line ~457, `wire_compose` ~494, `plug_compose` ~526 of
   `Emulates.lean`) are proved **at `HasPlugWireFactor` strength**. One escape hatch exists:
   `plug_right_of_observes_plug_comm` / `plug_compose_of_observes_plug_comm` replace the strict
   `plug_comm` with a per-model hypothesis "`plug` commutes up to `Obs`" — **but only for the
   plug-composition leg**; `par_compose`/`wire_compose` have no up-to variants, and the file's own
   docstring warns that "a scheduler-only structural relation is not sufficient by itself" as the
   observation. The free/syntactic models (`Expr.theory`, `Interp.theory`) instantiate the whole
   ladder.
2. **PolyFun concrete**: `OpenProcessModel.lean` — the process-backed `openTheory` over
   `OpenProcess m Party Δ` instantiates **only `IsLawful`**; associativity/commutativity/snake hold
   only up to `OpenProcessActivationEquiv` (e.g. `openTheory_par_assoc_activation_equiv`).
3. **VCVio computational**: `Interaction/UC/{Computational,Standard,Runtime,AsyncRuntime,
   AsyncSecurity,StdDoBridge}.lean` — bundled `Semantics` (surface monad + `SPMFSemantics` +
   `run`), `ObservedCompEmulates` (fixed-ε, deliberately not an `Observation` since not
   transitive), asymptotic bridge, textbook Canetti vocabulary (`Protocol`/`Functionality`/
   `Adversary`/`Environment`/`Simulator`/`EXEC`), `observedCompEmulates_toUCSecure_id`, dummy
   adversary as capability `HasDummyAdversaryFactor`, and an async runtime with
   `ProcessScheduler`/`EnvScheduler` pairs and env alphabets (`EnvAction`, `MomentaryCorruption`).

**The load-bearing gap:** the composition theorems live at tier `HasPlugWireFactor`; the only
model with probabilistic content lives at tier `IsLawful`. The `_of_observes_plug_comm` escape
hatch could in principle reach the process model, but it (a) covers only plug composition, not
`par`/`wire`, and (b) shifts the burden to supplying, per model, an observation that both
commutes with `plug` and retains the security-relevant events — which is the activation-
equivalence tax again in different clothing. Today UC composition is therefore a theorem about
the *syntax* of open systems, not about any system you can run. Closing this gap is Direction 1
(`02`).

### 1.6 Examples and schemes (consumers to improve)

`Examples/`: BR93, CommitmentScheme (with LoggingBounds), OneTimePad, PRFTagReader (hybrid-heavy),
PRGfromPRF, Pedersen, Regev, Schnorr, SealedSender, FrankingProtocol, SimpleTwoServerPIR,
CompositionDiagram. `CryptoFoundations/`: FiatShamir (+Sigma, WithAbort), Fischlin (supermartingale
knowledge soundness), FujisakiOkamoto, MerkleTree (+Batch), TwoPhaseGame under `Asymptotics`.
`HashSig/` (SLH-DSA), `LatticeCrypto/` (ML-KEM, ML-DSA). Notable rewrite candidates and why, used
as rent-test targets throughout the suite:

| Consumer | Pain today | Direction that buys it |
|---|---|---|
| `TwoPhaseGame` (**off-main**: k-l-examples, §1.7) | unfolds `◃`-composition by hand | ledger A6 (destructor triple) — already a PolyFun deliverable; routed through G-0b |
| PRFTagReader hybrids | per-hybrid glue, eager/lazy setup lemmas | `03` (run-canonicity + package algebra) |
| CommitmentScheme LoggingBounds | logging lemmas re-proved per wrapper | `04` (decorations) |
| SimpleTwoServerPIR | privacy via manual coupling | `04` (relational display) |
| Fischlin / FiatShamir forking | cursor use is fresh (#488); seeded fork still bespoke | `03` (cursor/fork algebra as module ops) |
| UC OTP/commitment statements | stuck at `IsLawful` model | `02` |

### 1.7 Off-main assets

The ledger (`vcv-connection.md`) cites `WireK`, `RunLimit`, `Coinductive/Machine`
(`Implements`/`IsSimulation`), and `TwoPhaseGame` on branch `dtumad/k-l-examples`; on `main`,
`OracleComp/Coinductive/` holds only `Bridge.lean` and none of these names resolve (verified
2026-07-20). Plans in this suite reference the k-l-examples material as *evidence and lemma
bank*, not as merged surface — same discipline ArkLib's suite applies to its prototype tree.

## 2. PolyFun today

### 2.1 Merged on `main` (usable now)

- **Free side**: `FreeM` (re-exported from cslib) + displayed free, paths, execution, **cursors**
  (partial paths), cursor append/occurrence/**fork** — the generic rewinding algebra behind #488;
  free universal property (#55); substitution monoids (#53) and free-as-monoid classification.
- **Cofree side**: cofree comonoid construction (#61), **universal property** (#65), **category
  operations from comonoids** (#63), **cofree mates** — dynamical behavior identified with mates
  (#67), **finite projections / Prop 8.49** (#68), finite vertices of M-types (#56).
- **Dynamical**: `DynSystem`, behavior, simulation/bisimulation/refinement, `Responder` (systems
  over `q ⊸ X` with the Kleisli–Mealy `equivStateHandler`), games via `eval` wiring
  (`DynSystem.game`/`closedGame`), `RunN`, and `DynComputation` with variance, exact sequential
  composition, bounded execution, and qualitative termination (#78–#82). Legacy `IOMachine` was
  removed by #83; new consumers target `DynComputation`.
- **Lens/monoidal**: full lens calculus, cartesian/vertical factorization, duoidal, internal hom +
  eval/curry, adjunctions, comonoids, `Comonoid.Hom` retrofunctors (`Cat♯`).
- **Interaction**: `TypeTree` (now literally sequential-spec-as-type-tree, #64), dependent chain
  concatenation (#66), decorations,
  two-party/multiparty, concurrent processes/machines/traces/fairness, UC open-process +
  `OpenTheory` + `Emulates` + corruption/env-action data.
- **ITree**: M-type ITrees, strong bisim as definitional equality, weak bisim, cross-signature
  simulation, lawful iteration (#47), generalized handlers (#44).

### 2.2 Recently merged trains integrated by this suite

- **Pattern-runs-on-matter** (#71 formalized Ξ; #72 operationalized it): `FreeP.runOn`/`xi`
  with `runOn_eq_xi`, module laws
  (`runOn_unit`, `runOn_assoc`), naturality, `runThrough` (generic `m p ⊗ c q → m r` schema),
  `runAgainst` (internal-hom evaluation), `runAgainstMonoid`, `DynSystem.runPattern` agreeing with
  finite game semantics, and **behavior/simulation invariance**
  (`runBehaviorThrough_eq_of_{obsEq,isSimulation,isStrongSimulation}`). Direction 2's engine.
- **Aberlé display series** (#74–#75, #84–#88, and #91–#98, replacing superseded #89; source:
  Abe26, arXiv 2604.01303): `Display` (Type-valued displays over polynomials), display morphisms (g6a),
  witness-preserving responder `PresentationHom`s (g6b), **parallel sum `P ∥ Q`** with
  `≃ₚ (P + Q) + (P ⊗ Q)` (g6c), free/displayed
  parallel execution incl. lockstep `FreeM.parallel` (g6d), responder parallel semantics (g6e),
  coherence (g6f/g6g), wiring/reconstruction bridges (g6h); plus g1–g5 (coalgebra displays,
  wiring, displayed behavior reindexing, indexed M-types, and its categorical identification).
  The state-free API is `toDisplayedBehavior`, `reindexDisplayedBehavior`,
  `mapDisplayedBehavior`, `displayedTotalStep`, and `PresentationHom`; the modules are
  `Responder/Presentation.lean`, `Responder/Parallel/Presentation.lean`,
  `DisplayedAssociativity.lean`, and `DisplayedCoherence.lean`. Also `PFunctor/Wiring.lean`:
  Aberlé Thm 3.1 (`eval` as recursive wiring) and Thm
  5.3 (local displayed handlers compose along wiring). Directions 3 and 4's engine.
  **Known boundary fact**: unrestricted Kleisli interchange for `FreeM.parallel` is *refuted* by a
  committed counterexample; `Wiring.evalParallel` deliberately targets duplicated inputs to
  "expose the absence of contraction".
- **Issue-32 chain** (#76–#83): resumption coinduction/lens transport, tau-free
  characterization, `DynComputation` variance/observational equivalence/exact seqcomp/bounded
  execution/qualitative termination, resumption truncation, remove legacy `IOMachine`. Cleans the
  machine layer Directions 1–2 sit on.
- **#66**: dependent `TypeTree` chain concatenation — the n-ary sequential-composition carrier.

### 2.3 PolyFun roadmap position (from `docs/reading/roadmap.md`)

Phases A and B: landed through their second milestones. Phase C: substantially landed (cofree
universal property, mates, finite projections). **Phase D is open**: D1 bicomodules, D2 selected
Thm 8.102 legs, D3 prafunctors + dynamics-as-bicomodule-composition, D4 `IPFunctor` ↔ bicomodules
over discrete comonoids, D5 research memos (topos internal logic; ⊗-monoids in Cat♯). This suite's
Directions 1, 2, 5 are, in ledger terms, *the VCVio consumers that give Phase D its rent tests*.

## 3. The disconnection points, stated precisely

1. **Tier gap** (§1.5): UC composition theorems at `HasPlugWireFactor`; concrete model at
   `IsLawful`. → `02`.
2. **Unnamed identification**: `QueryImpl.Stateful` = `Responder` in Kleisli form; package
   composition = responder/module composition. Nothing states it, so SSP re-proves what
   `runBehaviorThrough`-invariance gives generically. → `03`.
3. **Instrumentation vs decoration**: `QueryTracking` combinators and their lemma families are
   hand-kept; PolyFun decorations/displays exist but have no VCVio consumer. → `04`.
4. **Two schedulers, no discipline**: `ProcessScheduler`/`EnvScheduler` are raw samplers; the
   interchange counterexample shows theorems *must* be discipline-indexed, but no vocabulary for
   disciplines exists on either side. → `05`.
5. **Party topology is data, not structure**: `MachineId`, `CorruptionModel`, env alphabets exist
   as data types; growth of the topology (spawning) has no reindexing semantics. → `06`.
6. **Off-main coinductive machine layer**: `Implements`/`IsSimulation`/`RunLimit` referenced by the
   ledger live on k-l-examples. Directions 1–2 must either merge or re-derive them. → `08` gate.

## 4. Dependency constraints after the merge train

- The relevant PolyFun trains are merged. VCVio consumer PRs still pin PolyFun revisions via the
  lake manifest, so each VCVio slice in `08` names the minimal merged revision it needs rather
  than depending on a feature branch.
- Toolchain: both repos on Lean v4.32.0 / synced Mathlib+cslib; VCVio completed its 4.31→4.32
  migration on main. Keep the train in lockstep (same discipline as ArkLib's AR-0).
- PolyFun's crypto-free rule (AGENTS gotcha 2) means every direction splits into an upstream
  (structural, PolyFun PR) and downstream (probabilistic, VCVio PR) half. The suite's tickets are
  written pre-split.
