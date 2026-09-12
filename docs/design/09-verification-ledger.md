# 09 — Verification Ledger: Named Anchors and Their Status

Every load-bearing declaration/file named by docs 00–08, with its verified location and merge
status. **Verified 2026-07-22** against VCVio `main` `a5f474fd` and PolyFun `main` `f887c096`.
Implementation agents: grep these names *at these locations* before coding; if
a name has moved, update this ledger in the same PR that adapts to the move. Status legend:
**M** = merged on main; **OFF** = only on
`dtumad/k-l-examples` (VCVio); **SK** = design sketch, does not exist yet.

## VCVio (`Verified-zkEVM/VCVio`)

| Anchor | Location | Status |
|---|---|---|
| `OracleComp` := `PFunctor.FreeM spec.toPFunctor`; `ofFreeM`/`toFreeM` seam | `VCVio/OracleComp/OracleComp.lean` | M |
| `simulateQ` | `VCVio/OracleComp/SimSemantics/` | M |
| `QueryImpl.Stateful I E σ`; `Stateful.run` (= `(simulateQ …).run' s₀`, drops state) | `VCVio/OracleComp/SimSemantics/StateT/StateSeparating.lean` | M |
| `QueryImpl.Stateful.Frame σ σ₁ σ₂` (`:64`); field `separated : PFunctor.Lens.State.IsSeparated` (`:74`) | same file | M |
| `linkWith` (`:222`), `parSumWith` (`:462`) | same file | M |
| `advantage`/`advantage₀`/`boolDistAdvantage`; hybrid/IUB layers | `VCVio/StateSeparating/{Advantage,Hybrid,IdenticalUntilBad,DistEquiv,IndistAt,CellRef}.lean` | M |
| `countingOracle` | `VCVio/OracleComp/QueryTracking/CountingOracle.lean` | M |
| `loggingOracle`, `IsQueryBound` | `QueryTracking/{LoggingOracle,QueryBound}.lean` | M |
| `cachingOracle`, random-oracle layer | `QueryTracking/{CachingOracle,RandomOracle/}` | M |
| Loom carriers: unary WP (`HoareTriple`, `Loom/*`), relational `CouplingPost`, quantitative `ℝ≥0∞`, scoped-qualitative discipline | `VCVio/ProgramLogic/{Unary,Relational}/…` | M |
| `SeededFork` | `VCVio/ProgramLogic/SeededFork.lean` | M |
| `Semantics`, `SPMFSemantics`, `ObservedCompEmulates`, `AsympObservedCompEmulates` | `VCVio/Interaction/UC/Computational.lean` | M |
| `ProtocolBoundary`, `Protocol`, `Functionality`, `Adversary`, `Environment`, `Simulator`, `dummyAdversary`, `EXEC`, `Execution(.ofSemantics)`, `UCSecure`, `observedCompEmulates_toUCSecure_id`, `HasDummyAdversaryFactor` | `VCVio/Interaction/UC/Standard.lean` | M |
| `processSemantics`, `processSemanticsOracle` | `VCVio/Interaction/UC/Runtime.lean` | M |
| `RuntimeEvent`, `AsyncRuntimeState`, `ProcessScheduler`/`EnvScheduler`, `runStepsAsync`, `processSemanticsAsync(±ProbComp)`, `trivialEnvScheduler`, `processSemantics_eq_processSemanticsAsync_trivial`, `MomentaryCorruption.Alphabet` | `VCVio/Interaction/UC/{AsyncRuntime,AsyncSecurity}.lean` | M |
| Universe-0 constraint on runtime moves/state/env alphabet | `AsyncRuntime.lean` module docstring | M (constraint) |
| Deferred-sampling + relational-coupling engine | VCVio PR #465 (merged `e413cf7b`) | M |
| Replay forking from PolyFun contexts | VCVio PR #488 (merged `a5f474fd`) | M |
| `WireK.wireKStep`, `RunLimit` (`runKT`/`runChain`/`runLimit`), `Coinductive/Machine` (`Implements`, `IsSimulation`), `TwoPhaseGame` | k-l-examples branch | **OFF** (G-0b) |
| `runExp`, `runExp_eq_runThrough`, `Semantics.ofBehavior`, `RelDisplayed`, `OwnershipFrame`, `SchedulingDiscipline`, `Topology` | docs 02–06 | **SK** |

## PolyFun (`Verified-zkEVM/PolyFun`) — merged on main

| Anchor | Location |
|---|---|
| `FreeM` (+ cslib re-export), `FreeM.append`, `FreeM.liftM` | `PolyFun/PFunctor/Free/{Basic,Universal,Path}.lean`, `Handler.lean` |
| Displayed free + decorations + displayed cursors | `PolyFun/PFunctor/Free/Displayed.lean`, `Free/Displayed/{Decoration,Cursor,Append,StateChain}.lean` |
| Cursors, occurrence lookup, fork | `PolyFun/PFunctor/Free/Cursor/{…,Occurrence,Fork}.lean` |
| Substitution monoids; free-as-monoid | `PolyFun/PFunctor/SubstMonoid.lean`, `Free/Polynomial.lean` |
| Internal hom + eval/curry (A1) | `PolyFun/PFunctor/InternalHom.lean`, `CartesianClosed.lean` |
| Vertical/cartesian factorization (A3) | `PolyFun/PFunctor/Lens/{Cartesian,Factorization}.lean` |
| Comonoids, retrofunctors `Comonoid.Hom`, comonoid categories | `PolyFun/PFunctor/Comonoid.lean`, `Comonoid/Category.lean` |
| Cofree comonoid; universal property; finite projections `CofreeP.extend_comp_projectionN` | `PolyFun/PFunctor/Cofree/{Polynomial,Universal,FiniteProjection}.lean` |
| `DynSystem` (= lens `selfMonomial S ⇆ p`), behavior, simulation | `PolyFun/PFunctor/Dynamical/{Basic,Trajectory,Behavior,Simulation,Bisimulation}.lean` |
| Cofree mate; `DynSystem.cofreeMate_comp_projectionN` | `Dynamical/CofreeMate.lean`, `Dynamical/CofreeMate/FiniteProjection.lean` |
| `Responder`, `equivStateHandler`; `DynSystem.game`/`closedGame` | `Dynamical/Responder.lean`, `Dynamical/Game.lean` |
| `DynComputation` variance and exact `seqComp`, bounded execution, and termination (#78–#82); legacy `IOMachine` removed (#83) | `Dynamical/DynComputation.lean`, `Dynamical/DynComputation/{Bounded,Termination}.lean` |
| `TypeTree` (+ `done`/`node` `match_pattern` invariant), decorations, samplers, `Sampler.interleave` | `PolyFun/Interaction/Basic/…` |
| Concurrent processes/machines/frontiers/traces | `PolyFun/Interaction/Concurrent/…` |
| `PortBoundary(.Hom/.swap/.tensor)`, `OpenTheory` + ladder (`IsLawful`→`IsMonoidal`→`IsTraced`→`IsCompactClosed`→`HasPlugWireFactor`), `HasUnit`/`HasIdWire` | `PolyFun/Interaction/UC/{Interface,OpenTheory}.lean` |
| `OpenProcess`, `OpenProcessActivationEquiv` | `Interaction/UC/{OpenProcess,…}.lean` |
| Process model `openTheory` (tier: `IsLawful` only; `openTheory_par_assoc_activation_equiv` etc.) | `Interaction/UC/OpenProcessModel.lean` |
| `Observation(.eq)`, `Emulates`, `UCSecure`; `par_compose`(~457)/`wire_compose`(~494)/`plug_compose`(~526) under `[HasPlugWireFactor]`; `plug_right_of_observes_plug_comm`/`plug_compose_of_observes_plug_comm` (plug leg only, per-model `hcomm`) | `Interaction/UC/Emulates.lean` |
| Free models `Expr.theory`, `Interp.theory` (full ladder) | `Interaction/UC/OpenSyntax/{Expr,Interp}.lean`, `OpenTheory.lean` |
| `MachineId`, `EnvAction`, `CorruptionModel`, `MomentaryCorruption`, `Leakage` | `Interaction/UC/…` |
| `IPFunctor I`, indexed `FreeM`/`FreeM₂` | `PolyFun/IPFunctor/{Basic,Free/…}.lean` |
| ITrees: M-type carrier, strong bisim = `Eq`, weak bisim, cross-signature sim, lawful iter | `PolyFun/ITree/…` |

## PolyFun — recently merged train anchors

| Anchor | Location | Status / provenance |
|---|---|---|
| `FreeP.runOn`, `FreeP.xi`, `runOn_eq_xi` | `PFunctor/PatternRunsOnMatter/{Universal,Module}.lean` | M (#71) |
| `runOn_unit`, `runOn_assoc`, naturality; `CofreeP.laxUnit/laxTensor` | `PatternRunsOnMatter/Module.lean` + `Cofree/LaxMonoidal.lean` | M (#71) |
| `FreeP.runThrough`, `FreeP.runAgainst`, `runAgainstMonoid`, `DynSystem.runPattern`, `runPattern_game`, `runBehaviorThrough_eq_of_{obsEq,isSimulation,isStrongSimulation}` | `PatternRunsOnMatter/{Operational,Dynamical,Applications}.lean` | M (#72) |
| `Display` (+ Chart/Coalgebra/Indexed/Free/Handler/Lens/Category) | `PFunctor/Display/…` | M (#74–#75, #84–#88, #91) |
| `toDisplayedBehavior`, `reindexDisplayedBehavior`, `mapDisplayedBehavior`; `PresentationHom`, `displayedTotalStep` | `Dynamical/Responder/{Behavior,Lens,Presentation}.lean` | M (#87, #92; names cut over by #99) |
| `ParallelChoice`, `PFunctor.parallelSum` (`P ∥ Q`), `≃ₚ (P+Q)+(P⊗Q)` | `PFunctor/Parallel.lean` | M (#93) |
| `Display.parallelSumComponents`/`parallelSum` (separable) | `PFunctor/Display/Parallel.lean` | M (#93) |
| `FreeM.parallel` (lockstep), `parallelAfterLeftReturn`; **interchange counterexample** (regression suite) | `PFunctor/Free/Parallel.lean` + tests | M (#94) |
| `Responder.parallel/sum`, `sumDisplayedBehavior`, `parallelDisplayedBehavior`, parallel presentation homomorphisms and displayed coherence | `Dynamical/Responder/Parallel/{Behavior,Presentation,DisplayedAssociativity,DisplayedCoherence}.lean` | M (#95–#97; names cut over by #99) |
| `Wiring`, `Wiring.evalParallel` (+ race-freedom disclaimer), Abe26 Thm 3.1/5.3 | `PFunctor/Wiring.lean`, `Wiring/Parallel.lean` | M (#98, plus g2) |
| indexed M-types; displayed M-types | `IPFunctor/M.lean`, `PFunctor/Display/M.lean` | M (g4/G-series) |
| Displayed restriction along cursors | `PFunctor/Free/Displayed/Cursor.lean` | M (#58) |
| `DynComputation` exact seqcomp / variance / bounds / termination; resumption coinduction/truncation; `IOMachine` removal | `Dynamical/DynComputation{,/…}.lean`, `PFunctor/Resumption{,/Truncate}.lean`, `ITree/Resumption.lean` | M (#76–#83) |
| Dependent `TypeTree.Chain` concatenation | `Interaction/Basic/TypeTree.lean` | M (#66) |

## Docs 10–12 anchors (added 2026-07-20; verified against the named checkouts)

VCVio-side facts consumed by the new directions (all **M** unless noted):

| Anchor | Location | Consumed by |
|---|---|---|
| `OracleSpec ι := ι → Type v`; `toPFunctor`/`ofPFunctor` round-trip | `VCVio/OracleComp/OracleSpec.lean:25` | `12` §2 (boundary neutrality) |
| `SecExp` advantage layer is carrier-generic (`ProbComp.boolBiasAdvantage`, `SPMF.boolDistAdvantage` need only `SPMF Bool`) | `VCVio/CryptoFoundations/SecExp.lean` | `12` §2.1 |
| `FujisakiOkamoto` (ROM development, QROM pilot target) | `VCVio/CryptoFoundations/FujisakiOkamoto{,.lean}` | `12` R-12.2 |
| `GPVHashAndSign` (docstring cites BDF+11; ROM-only proof — the audit's first file) | `VCVio/CryptoFoundations/GPVHashAndSign.lean:61` | `12` §1, R-12.3 |
| `@[vcspec]`/`@[wpStep]` discr-tree registries (precedent for `@[game_equiv]`) | `VCVio/ProgramLogic/` + `docs/agents/program-logic.md` | `11` §3.1 |
| `SeededOracle` (deferred sampling; = Clutch presampling tapes, semantically) | `VCVio/OracleComp/QueryTracking/SeededOracle.lean` | `10` §2 |

External checkouts (workspace-relative; **revision facts, will drift**):

| Fact | Location | Consumed by |
|---|---|---|
| iris-lean upstream (feature inventory corrected 2026-07-20, verified at source): MoSeL, `UPred`, camera library (`Auth`/`Agree`/`Excl`/`Csum`/`Frac`/`DFrac`/`UFrac`/`View`/`HeapView`/`GhostMap`/`MonoNat`/`ReservationMap`), **`Algebra/COFESolver.lean` (America–Rutten, Carneiro–Graf 2025) + `Algebra/IProp.lean` (`BundledGFunctors` = `gFunctors`) — higher-order ghost state available**, namespaced invariants (`inv_alloc`), cancelable (`CInvariants`) + non-atomic invariants, `FUpd` fancy updates, later credits, `ProphMap`, abstract WP (#475) + `Adequacy` over `EctxLanguage`, HeapLang instance; setoid→type port in flight (#502) | `~/Documents/Lean/iris-lean` @ `5a790ae` | `10` §2.1–§2.2, S1 |
| Clutch mechanism (paper, read at source): refinement = unary WP (guarded fixpoint over per-step coupling modality `execCoupl`) + ghost `spec(e')` + `specCtx` invariant from two auth-camera instances, run-ahead spec execution via fancy updates; presampling tapes `ι ↪ (N,ns)` as ghost future randomness, adequacy-level erasure; §7 counterexamples: unrestricted presampling unsound | Clutch POPL 2024 (paper-note) | `10` §2.3, S2d |
| Approxis (POPL 2025, arXiv 2407.14107, acquired + indexed 2026-07-20): relational error credits over the spec-resource architecture; internalized ε→0 limiting argument; mechanized case studies incl. **PRP/PRF switching lemma and IND$-CPA** | paper-note | `10` §2.3, `11` §3.1 ledger constraint |
| iris-bluebell (Verified-zkEVM fork): `PSp`/`PermissionRat`/`PSpPm`/`IndexedPSpPm`, `HyperAssertion`, `assertSampledFrom`, `jointCondition`, `wp` over opaque `t : IndexedPSpPmRat I α V → IndexedPSpPmRat I α V` — **no program syntax; rules `sorry`-grade; own audit also flags a paper-vs-Lean WP-definition discrepancy** (`notes/rules_progress.md`) | `~/Documents/Lean/iris-bluebell` @ `0926a38`, `src/Bluebell/` | `10` §2, S2 |
| IPDL artifact (Rocq): case-study line counts at repo HEAD — `Chan/` 279, `OTP/` 257, `CoinFlip/` 472, `Branch/` 589, `GMW/` 614, `DHKE/` 744, `OT/` 2220; core `theories/*.v` ≈3.8k; paper's own comparison: multi-use secure network 195 lines vs 12,203 counted for EasyUC's single-use analogue (KE excluded) | `github.com/ipdl/ipdl` (shallow clone, 2026-07-20) | `11` §2, R-11.2 |
| Owl artifact: Haskell typechecker + Z3 (`prelude.smt2`), Rust extraction; case-study `.owl` sources incl. `kerberos`, `lak`/`mw` (RFID), `kem`/`pke`; WireGuard spec `tests/wip/wireguard.owl` ≈672 lines; `hpke/owl-hpke` + `wg/` benchmark harnesses (OwlC) | `github.com/secure-foundations/owl` (shallow clone, 2026-07-20) | `11` §2 |
| New sketches (SK): `StrategyModel`/`Classical`/`Quantum`/`MatterFor`, `QuantumSound` certificates, `@[game_equiv]` registry, `game_hop`/`guess`/`up_to_bad`/epoch combinators, frame-independence transfer, behavior COFE, Bluebell `wp` constructor | docs 10–12 | **SK** |

## Correction history

- 2026-07-22 (post-merge naming cutover): re-audited against PolyFun `f887c096` after #66,
  #71–#72, #76–#83, #88, #91–#98, and #99 merged. Moved those anchors from the open-PR ledger
  to merged state; recorded #89 as superseded; replaced the application-loaded `Verified*` API
  with the structural `Displayed*`/`PresentationHom` names introduced by #99. “Verified” remains
  only for factual audit claims or application-level correctness claims, not generic displays.

- 2026-07-20 (doc 10 Iris zoom-in, late evening): added `10` §2 (step-indexing's two jobs;
  camera catalogue as crypto bookkeeping; couplings-as-ghost-state; invariants/persistence),
  S2d ghost-coupling layer, R-10.5/R-10.6, and renumbered `10` §§2–6 → §§3–7 (roadmap risk-table
  ref updated). **Fact correction: the earlier revision undersold iris-lean** — verified at
  source that `COFESolver`/`iProp`/`gFunctors`, namespaced + cancelable + non-atomic invariants,
  `FUpd`, later credits, `GhostMap`, `ProphMap`, and abstract-WP adequacy are all present, i.e.
  higher-order ghost state is available in Lean today; ledger row updated. Clutch read at source
  (spec-resource/`specCtx`/`execCoupl`/run-ahead/tape-erasure mechanism; §7 unsoundness
  counterexamples adopted as negative tests). **Approxis (POPL 2025) acquired and indexed** —
  relational error credits with mechanized PRP/PRF switching + IND$-CPA — cited as the existence
  proof that quantitative game-hopping is ghost-state manipulation; `11`'s ledger now carries an
  isomorphism constraint to it.
- 2026-07-20 (directions 6–8 source-review round, evening): all nine §B acquisitions read
  against docs 10–12; corrections applied — **PSL third author is Liao, not Ying** (07, paper
  index, PDF filename); **iUC is ePrint 2019/1073, not 2019/1324** (07, both occurrences; user
  caught during download); IPDL author order matched to publication (Morrisett–Shi–Sojakova–
  Fan–Gancher, randomized); IPDL restrictions restated paper-accurately in 11 §2 (write-once
  channels/reactions, statically bounded loops, static corruption, fully adversarial
  scheduling — replacing the looser "fixed topology / no state" gloss); Owl soundness phrasing
  fixed in 11 §2 ("once-and-for-all on-paper proof", not "logical relation") and Owl's
  name-based hierarchical corruption/`corr_case`/module-types/asymptotic-only facts added;
  PSL case-study list corrected in 10 §4.2/S2c — §3.2 pre-renumbering (PIR, OT, multi-party addition, simple ORAM; OTP is
  the warm-up); Bluebell fork's paper-vs-Lean WP discrepancy surfaced into 10; 12 upgraded with
  BDF+11's four non-transferring techniques + separation result + history-free-reduction
  certificates (GPV ground truth for R-12.3), PQ-CryptoVerif's black-box-attacker semantics as
  the §2 precedent, AHU (q,d)/semi-classical precision, and the AHU Appendix-B FO flaw notice
  (Maram) steering the R-12.2 baselines to Zhandry-FO + qrhl-FO. Artifact facts (IPDL/Owl
  clones) added to the anchor table above.
- 2026-07-20 (directions 6–8 extension): added docs 10–12 and their anchor section above;
  verified `OracleSpec`/`SecExp`/`FujisakiOkamoto`/`GPVHashAndSign` locations and the
  iris-lean/iris-bluebell checkout states cited by doc 10.
- 2026-07-20 (this review): added the `_of_observes_plug_comm` escape-hatch nuance (docs 01/02);
  moved `TwoPhaseGame` to OFF status (docs 01); fixed `runExp` sketch to match `Stateful.run`'s
  actual signature (doc 03); named `Frame`/`IsSeparated` exactly (doc 05); annotated `IOMachine`
  removal (#83) wherever `seqComp` is cited (docs 01/09).
