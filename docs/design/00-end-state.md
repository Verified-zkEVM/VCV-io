# 00 — End State: Compositional Verified Cryptography Over One Substrate

## 0. Status and scope

This document is a north star and coverage contract, not a claim that any of it is proved today.
The near-term scope is: game-based cryptography as currently practiced in VCVio (paper 1, ePrint
2026/899), upgraded in place; state-separating proofs and UC security unified over the PolyFun
interaction substrate; and the machinery for paper 2 (coalgebraic adversaries) and paper 3
(categorical UC) — the §10 promise of paper 1 — built so that each intermediate stage already
improves the library. Rational/composable-with-incentives settings are out of scope; the
architecture must leave seams for them without pretending to cover them. Two former out-of-scope
items were promoted on 2026-07-20: quantum access now has a staged design (`12` — the interface
core is in scope this cycle, the comb semantics is research), and protocol-scale proofs with
compromise events have a track (`11`); corruption models beyond the existing
`CorruptionModel`/`MomentaryCorruption` data remain scoped by `05`/`06`.

## 1. The ambition

VCVio should become the library in which the *entire* stack of modern cryptographic reasoning is
one connected story rather than four adjacent toolkits:

- **Game-based proofs** (current strength): oracle computations as free-monad syntax trees,
  handler-based manipulation, replay/forking without rewindability axioms, Loom program logics.
- **State-separating proofs**: packages, hybrids, identical-until-bad — today a competent but
  self-contained layer; end state: the one-boundary specialization of the open-system layer, with
  the reduction lemma derived from generic module laws (`03`).
- **Simulation-based / UC security**: today an abstract `OpenTheory` axiomatization whose only
  concrete model reaches `IsLawful`; end state: a behavior-backed model satisfying the compact
  closed laws strictly, making the UC composition theorems *apply* to the concrete model (`02`),
  with scheduling and corruption as named disciplines (`05`) and dynamic party topologies (`06`).
- **Program logics**: today Loom (extrinsic) plus ad-hoc instrumentation lemmas; end state: Loom
  on top, displayed/intrinsic invariants underneath, one bridge theorem per carrier (`04`).

The unifying claims, each of which is a *falsifiable formalization target*, not a metaphor:

1. **Adversary-vs-oracle execution is the pattern-runs-on-matter module action.**
   `Ξ : Free(P) ⊗ Cofree(Q) → Free(P ⊗ Q)`; the adversary is the pattern, the implementation is
   the matter, the module laws are the composition laws of experiments.
2. **Equality of implementations is equality of mates.** The cofree-comonoid universal property
   (now in PolyFun: `Cofree/Universal`, `CofreeMate`, `FiniteProjection`) makes behavioral
   equality an honest `Eq`, deleting per-theorem activation-equivalence bookkeeping.
3. **Packages, functionalities, environments, and hybrids are bicomodules over protocol
   comonoids**; `par`/`wire`/`plug` are instances of bicomodule composition; SSP's separation by
   typing is the ownership discipline that makes wiring race-free.
4. **The UC composition theorem is functoriality of the behavior assignment** from wired systems
   to wired behaviors (naturality squares "behavior of composite = composite of behaviors").
5. **Program logics are displayed structure**: unary invariants are displays over `Free(P)`;
   relational judgments are displays over the parallel composite with genuinely joint evidence.

## 2. Architecture: the standing split, sharpened

The paper-1 architecture (oracle core → handlers → program logic → SSP) remains. What changes is
that each layer acquires an explicit PolyFun *carrier* and the VCVio layer becomes the
probabilistic instance:

```text
                    PolyFun (structural, crypto-free)          VCVio (probabilistic instance)
programs            FreeM p                                    OracleComp spec  (already =, #488 era)
implementations     Responder / DynSystem / Cofree mate        QueryImpl.Stateful, SPMF-Kleisli responders
experiments         Ξ / runAgainst / runThrough                simulateQ + evalDist of the run
packages            one-boundary bicomodules                   QueryImpl.Stateful + state frames
open systems        comonoids + bicomodules / OpenTheory       Semantics, ObservedCompEmulates, EXEC
equality            mate equality (Eq, by finality)            evalDist/tvDist equality, asymptotics
program logic       displayed programs / responder presentations Loom WP/RelWP carriers, tactics
scheduling          ∥, interleaving policies, disciplines      ProcessScheduler/EnvScheduler instances
party topology      indexed pfunctors, mode-dependent comonoids MachineId/Sid/Pid directories, corruption
```

Every row's left cell is a PolyFun deliverable (some landed, some still new tickets);
every row's right cell is a VCVio consumer with named files in `01`. The dependency direction never
reverses.

## 3. What this buys, concretely (the coverage hypothesis)

The end state is earned when the following are true, each checkable in Lean:

- **UC composition applies to a concrete model.** `Emulates.par_compose` / `wire_compose` /
  `plug_compose` — which today require `HasPlugWireFactor`, unreachable by the process model —
  hold for the behavior-backed model, and at least one end-to-end UC statement (commitment or OTP
  functionality) is proved through them with zero `OpenProcessActivationEquiv` lemmas in its
  proof-term closure (`02` rent test).
- **The SSP reduction lemma is derived, not hand-proved.** The package-swapping argument in
  `StateSeparating/` factors through `runAgainst`-invariance under simulation, with the SPMF layer
  contributing only a `tvDist` bound (`03` rent test).
- **One instrumentation wrapper is a decoration.** At least one of counting/logging/caching in
  `QueryTracking` is re-derived as a displayed decoration with its transport lemma coming from the
  generic displayed-handler theorem, with no lost `simp` surface (`04` rent test).
- **One relational proof is a joint display.** One existing coupling proof (e.g. from
  `Relational/Examples.lean` or the OTP example) is re-expressed as a displayed program over the
  lockstep parallel composite, and the Loom `RelTriple` is recovered from it by a bridge theorem
  (`04` rent test).
- **Scheduling disciplines are named.** The async runtime's theorems are restated with the
  discipline as an explicit hypothesis, and the parallel-interchange counterexample is cited as
  the boundary of what holds without one (`05` gate).
- **A two-party functionality with dynamic session creation is stated.** Even in toy form, one
  functionality whose party/session directory grows during execution, modeled by reindexing, with
  its emulation statement surviving a spawn (`06` gate — this is the paper-3 pilot).
- **Existing examples get shorter or stronger.** At least two of: `TwoPhaseGame` via the
  destructor triple; a PRFTagReader hybrid via run-canonicity; Fischlin/forking via the cursor
  algebra; SimpleTwoServerPIR privacy via a relational display. Measured in lines and in axioms.

Failure of a criterion is evidence against the corresponding abstraction, handled per `08`'s kill
criteria — not a reason to weaken the criterion.

## 4. Non-goals for this cycle

- **Rebuilding paper-1 layers that already pay rent.** The oracle core, `evalDist` theory, Loom
  tactic surface, and the existing scheme library are consumers to *improve*, not surfaces to
  churn. No cutover renames in this cycle (contrast with ArkLib's `01b`); integration is additive
  until a direction's rent test passes.
- **A synthetic/internal-language UC.** The topos `[𝒯_p, Set]` internal-logic track stays a
  research memo (PolyFun D5) until it has a named consumer theorem; we do not build a
  specification language before its first specification.
- **Computational-cost foundations.** TM-grounded polynomial time stays where paper 1 left it
  (documented `sorry` boundary in `ToMathlib`); nothing in this suite depends on resolving it.
- **Solving fixed-ε transitivity.** `ObservedCompEmulates` at fixed ε is not an equivalence and
  is not forced into `Observation`; asymptotic and concrete-bound statements coexist as today.
- **Full Canetti ITM fidelity.** We target the *semantic content* of dynamic spawning and
  adversarial scheduling (IITM-style directories, explicit disciplines), not a bit-compatible
  encoding of the 2000/067 execution model.
