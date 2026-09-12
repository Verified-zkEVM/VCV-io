# 08a — Phase 0/1 PR Plan: Exact Slices

Operational companion to `08`. One PR per slice; each names repo, base, files, key declarations,
and its acceptance gate. Branch naming: `design-int/<slice-id>` in both repos. Every PolyFun slice
obeys PolyFun AGENTS rules (crypto-free, import DAG, no `sorry`, `./scripts/update-lib.sh`,
`./scripts/validate.sh --lint --test`); every VCVio slice keeps `ofFreeM`/`toFreeM` as the sole
unfolding seam and leaves the `Interaction/UC` public API additive. Anchors: see `09`; statuses
verified 2026-07-22.

## Phase 0

### P0-1 (process) — merge-train pinning (complete)
As of 2026-07-22, #66, #71/#72, #76–#83, #88, and #91–#98 are merged on PolyFun `main`; #89 was
superseded. Record the exact merged PolyFun revision at each slice's start rather than naming an
open branch.

### P0-2 (VCVio) — k-l-examples triage (gate G-0b)
Branch from VCVio main. For each off-main asset (`WireK`, `RunLimit`, `Implements`/`IsSimulation`,
`TwoPhaseGame`): a one-page disposition in `docs/design/dispositions.md` — merge / re-derive /
retire — with the A1 ledger payoff (`WireK` = eval-wiring) and `02`'s mate-based re-derivation
(`Implements`) as the default recommendations. **Gate:** every Phase 1+ slice that would touch an
OFF asset cites its disposition.

### P0-3 (paper-note) — acquisitions
`07` §B items 1–7 downloaded + indexed. No code.

## Phase 1 — Track A (behavior model, `02`)

### A1 (PolyFun) — `OpenProcess.behavior` and homomorphism statements
Needs: none beyond main (issue32 merges reduce churn; not blocking).
Files: new `PolyFun/Interaction/UC/Behavior.lean` (name the step polynomial of `OpenProcess`
explicitly — the Concurrent layer's machine polynomial; if no single named `stepPoly` exists,
*this slice introduces it* next to `OpenProcess`).
Declarations: `OpenProcess.stepPoly` (if new), `BehaviorObj m Party Δ` (M-type carrier),
`OpenProcess.behavior` via corec/mate, `behavior_congr_activationEquiv`
(`OpenProcessActivationEquiv W₁ W₂ → behavior W₁ = behavior W₂` — **the** quotient theorem; if
this needs behavior to be stated on a scheduler-quotiented step functor, say so here and adjust
`02` §3.1 before proceeding).
Gate: quotient theorem proved; DAG edge `Interaction/UC/OpenProcess → Behavior` only.

### A2 (PolyFun) — `behaviorTheory : OpenTheory` at `IsMonoidal` (gate G-2a)
Needs: A1.
Files: `Interaction/UC/BehaviorModel.lean`.
Declarations: behavior-level `map/par/wire/plug` by corecursion; `instance : IsLawful`,
`IsMonoidal`; homomorphism theorems `behavior_par/wire/plug` vs the process model's ops.
Gate: `IsMonoidal` fields close by finality/uniqueness (no setoid, no `Quotient`, no `sorry`);
rent test R-2.2 partially met.

### A2.5 (both) — plug-composition pilot (cheap milestone, added by the 2026-07-20 review)
Needs: A2.
PolyFun: instantiate `plug_compose_of_observes_plug_comm` at the behavior model with
`Obs := Observation.eq` and `hcomm` from behavior-level `plug`-commutation (should be a finality
lemma; if it is not provable at `IsMonoidal` strength, record that as evidence about G-2c's
difficulty and stop this slice).
VCVio: a toy two-system plug-composition statement through it (OTP-shaped), `Semantics` bridging
via `behavior_eq → evalDist_eq` (see B3').
Gate: first end-to-end UC-composition statement with runnable content, before G-2c.

### A3 (PolyFun) — `IsTraced` (gate G-2b)
Needs: A2; **D1-track interchange lemmas** (`05` step 1 — schedule Track D's D1 slice before or
alongside; shared-fate risk recorded in `08`).
Gate: wire-associativity + superposition strict; kill criterion from `02` §5 checked here
(transport-lemma count vs process-model activation-lemma count — record both numbers in the PR).

### A4 (PolyFun) — copy-cat `idWire` and `HasPlugWireFactor` (gate G-2c)
Needs: A3; uses the merged g6h wiring bridges from #98 (reconstruction lemmas).
Declarations: relay behavior (`idWire`), zig-zag laws, `HasPlugWireFactor` instance.
Gate: R-2.2 fully met. If blocked > budget: fall back per `02` §3.1(2), re-scope, update `08`.

### A5 (VCVio) — `Semantics.ofBehavior` + pilot (rent tests R-2.1, R-2.3)
Needs: A4 (or A2.5 for the plug-only variant); B3' lemma.
Files: `VCVio/Interaction/UC/BehaviorSemantics.lean`; pilot in `Examples/` or `UC/`.
Gate: pilot statement's proof-term closure has zero `OpenProcessActivationEquiv` constants
(check mechanically: `#print axioms`-style closure grep in CI script).

## Phase 1 — Track B (experiment engine, `03`)

### B1 (PolyFun) — Kleisli lemma pack for `runThrough`
Needs: merged #71/#72 (available on PolyFun `main`).
Files: extend `PatternRunsOnMatter/Operational.lean` (or new `Operational/Kleisli.lean`).
Declarations: `runThrough` instance lemmas at `m := StateT σ n` for lawful `n`-handlers:
step/bind/pure equations shaped for `simulateQ`-style rewriting (match VCVio's `simp` idiom).
Gate: lemma pack compiles against a mock `StateT`-handler in `PolyFunTest`.

### B2 (VCVio) — `runExp` seam
Needs: B1.
Files: `VCVio/OracleComp/SimSemantics/StateT/RunExp.lean`.
Declarations: `runExp h s₀ A := h.run s₀ A` (with a state-retaining sibling over `.run`);
`runExp_eq_runThrough` (the identification; **kill-check here** per `03` §5 — if `OptionT`
plumbing resists, ship `runExp` + invariance lemmas only and edit `03` §3.1 + this file).
Gate: zero consumer churn (pure addition).

### B3 (VCVio) — derive link-assoc + simulation invariance (rent R-3.1)
Needs: B2. Declarations: `runExp_linkWith_assoc` from `runOn_assoc`;
`runExp_congr_simulation` from `runBehaviorThrough_eq_of_isSimulation` + evalDist bridge.
Includes **B3′**: the shared lemma `behavior_eq → evalDist_eq` (single home:
`VCVio/Interaction/UC/BehaviorSemantics.lean` if Track A landed A5 first, else here — whichever
is second imports).
Gate: at least one bespoke twin deleted from `StateSeparating/` in the same PR; net diff ≤ 0
lines there.

### B4 (VCVio) — hybrid combinator + PRFTagReader port (rent R-3.2)
Needs: B3. Gate: one hybrid chain's per-hybrid glue lemmas deleted; statement unweakened.

### B5 (VCVio) — fork-as-pattern-surgery doctrinal pass (rent R-3.3)
Needs: B3. Files: docstring/lemma pass over `CryptoFoundations/Fischlin`, `FiatShamir`,
`ProgramLogic/SeededFork.lean`. Gate: one Bellare–Neven fork step restated via `runExp` + cursor
fork; diff reported in PR body.

## Phase 2 early-startable slices (may run during Phase 1)

### C1 (VCVio) — counting as decoration (rent R-4.1)
Needs: nothing beyond main (uses merged `Free/Displayed/Decoration`).
Files: `QueryTracking/CountingOracle.lean` + new `QueryTracking/Decorations.lean`.
Gate: all existing counting consumers elaborate unchanged; transport lemma imported, not local.

### D1 (PolyFun) — `SchedulingDiscipline` + restricted interchange packs
Needs: merged #93/#94 (parallel sum + lockstep + counterexample; available on PolyFun `main`).
Files: new `PolyFun/Interaction/Concurrent/Discipline.lean` (or `PFunctor/Free/Parallel/…`).
Declarations: the three disciplines of `05` §1.2; lockstep interchange for
synchronization-preserving handlers; sequential-activation invariances.
Gate: the committed counterexample is cited in the docstring as the boundary; feeds A3.

## Standing PR discipline

- Every slice's PR body links the direction doc section it implements and quotes its rent test.
- A slice that fires a kill criterion merges its *post-mortem edit to the docs* instead of code.
- Ledger (`09`) updated in the same PR whenever an anchor moves or a SK item becomes real.
