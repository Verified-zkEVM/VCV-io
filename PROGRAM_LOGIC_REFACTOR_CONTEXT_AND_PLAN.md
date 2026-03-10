# Program Logic Refactor: Context and Implementation Plan

Generated: March 1, 2026  
Repo: `VCV-io`  
Branch at analysis time: `quang/more-cleanups`  
Baseline status: clean working tree, `lake build` succeeded.

## Historical Status

This document records the pre-implementation baseline from March 1. It is still useful for
architectural rationale around the Loom-style algebraic core and the Bluebell deferral, but
its description of `VCVio/ProgramLogic` is no longer current.

In particular, the current tree now has a landed unary quantitative WP layer, coupling-based
relational rules, quantitative eRHL / apRHL infrastructure, notation, a tactic surface, and
a narrow unary `Std.Do` bridge. Treat this file as historical context, not as the active
plan-of-record.

## 1) Objective

Implement a probabilistic Hoare/WP-style program logic for `VCVio` that:

1. is extensible over monad transformer stacks (Loom-style),
2. integrates cleanly with existing `OracleComp` and `EvalDist`,
3. leaves room for future relational/coupling/separation-logic extensions.

## 2) Current VCVio Program Logic Status

These were inspected and are currently not a production-ready foundation:

- [`VCVio/ProgramLogic/Unary/HoareTriple.lean`](VCVio/ProgramLogic/Unary/HoareTriple.lean)
  - Experimental, `StateM`-only Hoare rules.
- [`VCVio/ProgramLogic/Unary/Examples.lean`](VCVio/ProgramLogic/Unary/Examples.lean)
  - Ordered-monad examples, exploratory.
- [`VCVio/ProgramLogic/Relational/Basic.lean`](VCVio/ProgramLogic/Relational/Basic.lean)
  - Placeholder namespace.

`ProgramLogic` is currently imported by root:

- [`VCVio.lean`](VCVio.lean)

## 3) Relevant VCVio Infrastructure Already Available

### 3.1 Probability semantics and APIs

- [`VCVio/EvalDist/Defs/Basic.lean`](VCVio/EvalDist/Defs/Basic.lean)
  - `HasEvalSPMF`, `HasEvalPMF`, `evalDist`, `Pr[...]`, `probOutput`, `probEvent`, `probFailure`.
- [`VCVio/EvalDist/Monad/Basic.lean`](VCVio/EvalDist/Monad/Basic.lean)
  - bind-probability rules (`probOutput_bind_eq_tsum`, `probEvent_bind_eq_tsum`, etc.).
- [`VCVio/EvalDist/Defs/SPMF.lean`](VCVio/EvalDist/Defs/SPMF.lean)
  - `SPMF := OptionT PMF` core lemmas.

### 3.2 Oracle-specific semantics

- [`VCVio/OracleComp/EvalDist.lean`](VCVio/OracleComp/EvalDist.lean)
  - `HasEvalPMF (OracleComp spec)` via uniform-query semantics.
  - Key bridge for quantitative WP on oracle computations.
- [`VCVio/OracleComp/SimSemantics/SimulateQ.lean`](VCVio/OracleComp/SimSemantics/SimulateQ.lean)
  - `simulateQ` monad-hom-like behavior (`pure`/`bind`) suitable for algebraic lifting.

### 3.3 Existing design preference to preserve

- [`VCVio/EvalDist/Instances/ReaderT.lean`](VCVio/EvalDist/Instances/ReaderT.lean)
  - Explicitly avoids global `ReaderT` eval instances without fixed environment.

## 4) Loom Resources Explored (Architecture Reference)

### 4.1 Core algebraic WP architecture

- [`../loom/Loom/MonadAlgebras/Defs.lean`](../loom/Loom/MonadAlgebras/Defs.lean)
  - `MAlg`, `MAlgOrdered`, `MAlgDet`, `MAlgPartial`, `MAlgTotal`, `MAlgLift`.
- [`../loom/Loom/MonadAlgebras/WP/Basic.lean`](../loom/Loom/MonadAlgebras/WP/Basic.lean)
  - `wp`, `triple`, `wp_bind`, `wp_cons`, `triple_bind`, loop rules.
- [`../loom/Loom/MonadAlgebras/Instances/StateT.lean`](../loom/Loom/MonadAlgebras/Instances/StateT.lean)
- [`../loom/Loom/MonadAlgebras/Instances/ReaderT.lean`](../loom/Loom/MonadAlgebras/Instances/ReaderT.lean)
- [`../loom/Loom/MonadAlgebras/Instances/ExceptT.lean`](../loom/Loom/MonadAlgebras/Instances/ExceptT.lean)
- [`../loom/Loom/MonadAlgebras/PMF.lean`](../loom/Loom/MonadAlgebras/PMF.lean)
  - Prototype `MAlgOrdered PMF ENNReal`.

### 4.2 Auxiliary pieces inspected

- [`../loom/Loom/MonadUtil.lean`](../loom/Loom/MonadUtil.lean)
  - `Cont`/continuation infrastructure.
- [`../loom/Loom/SpecMonad.lean`](../loom/Loom/SpecMonad.lean)
  - `MonadOrder` class.
- [`../loom/Loom/BI/Basic.lean`](../loom/Loom/BI/Basic.lean)
  - BI backend sketch for future separation-logic extension.
- [`../loom/README.md`](../loom/README.md)

### 4.3 Loom constraints discovered

- Toolchain mismatch: [`../loom/lean-toolchain`](../loom/lean-toolchain) is Lean `v4.24.0`.
- VCVio toolchain: [`lean-toolchain`](lean-toolchain) is Lean `v4.28.0`.
- Loom dependency on `lean-auto`: [`../loom/lakefile.lean`](../loom/lakefile.lean).
- Unsafe axiom in Loom SMT module: [`../loom/Loom/SMT.lean`](../loom/Loom/SMT.lean) (`trust_smt`).

Conclusion: port core files; do not depend on Loom directly now.

## 5) Bluebell / iris-lean Resources Explored

### 5.1 Integration design notes

- [`../../Notes/LOOM_INTEGRATION_BLUEPRINT.md`](../../Notes/LOOM_INTEGRATION_BLUEPRINT.md)
  - Detailed cross-project architecture and phased roadmap.

### 5.2 Bluebell / iris current state checked

- [`../iris-lean/lean-toolchain`](../iris-lean/lean-toolchain) is Lean `v4.26.0`.
- [`../iris-lean/lakefile.toml`](../iris-lean/lakefile.toml) pinned to Mathlib `v4.26.0`.
- Bluebell still has key `sorry` gaps:
  - [`../iris-lean/src/Bluebell/Logic/JointCondition.lean`](../iris-lean/src/Bluebell/Logic/JointCondition.lean)
  - [`../iris-lean/src/Bluebell/Logic/WeakestPre.lean`](../iris-lean/src/Bluebell/Logic/WeakestPre.lean)
  - [`../iris-lean/src/Bluebell/Logic/Ownership.lean`](../iris-lean/src/Bluebell/Logic/Ownership.lean)
  - [`../iris-lean/src/Bluebell/ProbabilityTheory/IndepProduct.lean`](../iris-lean/src/Bluebell/ProbabilityTheory/IndepProduct.lean)

Conclusion: defer direct Bluebell integration until toolchain and proof gaps are resolved.

## 6) Build and Baseline Verification Performed

Command executed:

```bash
lake build
```

Outcome:

- Build completed successfully (`8118` jobs).
- `VCVio.ProgramLogic.Unary.HoareTriple` and the rest of the library built cleanly at baseline.

## 7) Recommended Implementation Plan (VCVio-first)

## Phase A: Port minimal Loom core into `ToMathlib` (no SMT/tactics/case studies)

1. Add `ToMathlib/Control/MonadAlgebras/Defs.lean`.
2. Add `ToMathlib/Control/MonadAlgebras/WP/Basic.lean`.
3. Add `ToMathlib/Control/MonadAlgebras/Instances/{Basic,StateT,ReaderT,ExceptT}.lean`.
4. Add `ToMathlib/Control/MonadAlgebras/PMF.lean` (adapted to Lean 4.28/Mathlib v4.28).
5. Register imports in [`ToMathlib.lean`](ToMathlib.lean).

Guardrails:

- Do not import Loom directly.
- Do not port `SMT`, `Tactic`, `Meta`, `CaseStudies`.

## Phase B: VCVio quantitative WP for `OracleComp` (unary, probabilistic)

1. Create `VCVio/ProgramLogic/Unary/WP.lean` (new).
2. Define `wp`/`triple` aliases for `OracleComp` using ported core.
3. Build `MAlgOrdered` instance for target quantitative lattice (`ℝ≥0∞`) via existing `evalDist`.
4. Prove core rules specialized to oracle programs:
   - `wp_oracle_pure`
   - `wp_oracle_bind`
   - `triple_oracle_cons`
   - `triple_oracle_bind`
5. Bridge to existing APIs:
   - `probEvent` as WP of indicator postcondition
   - `probOutput` as WP of singleton indicator

## Phase C: Transformer extensibility in VCVio style

1. Keep Reader-style explicit environment (match [`VCVio/EvalDist/Instances/ReaderT.lean`](VCVio/EvalDist/Instances/ReaderT.lean)).
2. Prioritize `OptionT` compatibility (since `SPMF = OptionT PMF` is central).
3. Keep `ExceptT` support optional/secondary.

## Phase D: Migration and deprecation of old `ProgramLogic`

1. Keep old files temporarily while new WP API lands.
2. Port one canonical proof to validate ergonomics:
   - Candidate: [`Examples/OneTimePad.lean`](Examples/OneTimePad.lean).
3. Once stable:
   - remove/replace old ad-hoc `StateM`-only `HoareTriple` module,
   - update [`VCVio.lean`](VCVio.lean) imports accordingly.

## Phase E: Relational layer (after unary stabilizes)

1. Introduce coupling-based relational triples (self-product / paired semantics).
2. Reuse existing coupling support:
   - [`ToMathlib/ProbabilityTheory/Coupling.lean`](ToMathlib/ProbabilityTheory/Coupling.lean).
3. Add relational API under `VCVio/ProgramLogic/Relational/`.

## Phase F (deferred): Bluebell/iris separation-logic integration

Prerequisites:

1. Toolchain alignment to Lean/Mathlib version used by VCVio.
2. Close key Bluebell `sorry` gaps in JointCondition/WP/Ownership/IndepProduct.
3. Then provide BI backend and frame-rule bridge.

## 8) Immediate Next Step Checklist

1. Create `ToMathlib/Control/MonadAlgebras/Defs.lean` and `WP/Basic.lean` (ported/adapted).
2. Add minimal `MAlgOrdered PMF ENNReal` in `ToMathlib`.
3. Create `VCVio/ProgramLogic/Unary/WP.lean` with `OracleComp` quantitative WP lemmas.
4. Run `lake build` after each phase.
5. Keep old `ProgramLogic` files untouched until new API is validated by at least one example proof.

