# Program Logic Refactor Context + Implementation Plan (V2)

Generated: March 1, 2026  
Repo: `VCV-io`  
Working directory: `/Users/quang.dao/Documents/Lean/VCV-io`

## Historical Status

This document captures a March 1 design revision, especially the serious exploration of
Lean's `Std.Do` / `mvcgen` stack. That investigation is still valuable background, but the
repo has moved on since then.

Today the semantic core has already landed in `ToMathlib` and `VCVio/ProgramLogic`, and the
active automation direction is the custom tactic layer described in
`PROGRAM_LOGIC_VCGEN_DESIGN.md`, with `Std.Do` retained only as a narrow unary bridge. Treat
this file as historical background and rationale, not as the current implementation plan.

## 1) Current Snapshot

- Branch: `master`
- HEAD: `84822d6`
- Working tree status during analysis: clean except untracked planning doc(s)
- Build baseline: `lake build` succeeded (`8118` jobs)

Commands run:

```bash
git branch --show-current
git rev-parse --short HEAD
git status --short
lake build
```

## 2) Objective (Restated)

Design and implement a probabilistic Hoare/WP program logic for `VCVio` that:

1. works well with `OracleComp`/`evalDist`,
2. is extensible over transformer stacks (Loom-style architecture),
3. supports good proof ergonomics in `do` notation (via Lean's `Std.Do` + VCGen tooling),
4. leaves a clean path to relational/separation logic later.

## 3) VCVio Context Inspected

Program-logic footprint:

- [`VCVio/ProgramLogic/Relational/Basic.lean`](VCVio/ProgramLogic/Relational/Basic.lean)
- [`VCVio/ProgramLogic/Unary/Examples.lean`](VCVio/ProgramLogic/Unary/Examples.lean)
- [`VCVio/ProgramLogic/Unary/HoareTriple.lean`](VCVio/ProgramLogic/Unary/HoareTriple.lean)

Root imports still include these:

- [`VCVio.lean`](VCVio.lean)

Probability/oracle foundations to build on:

- [`VCVio/EvalDist/Defs/Basic.lean`](VCVio/EvalDist/Defs/Basic.lean)
- [`VCVio/EvalDist/Monad/Basic.lean`](VCVio/EvalDist/Monad/Basic.lean)
- [`VCVio/OracleComp/EvalDist.lean`](VCVio/OracleComp/EvalDist.lean)
- [`VCVio/OracleComp/SimSemantics/SimulateQ.lean`](VCVio/OracleComp/SimSemantics/SimulateQ.lean)

## 4) Loom Resources Explored

Architecture and WP core:

- [`../loom/Loom/MonadAlgebras/Defs.lean`](../loom/Loom/MonadAlgebras/Defs.lean)
- [`../loom/Loom/MonadAlgebras/WP/Basic.lean`](../loom/Loom/MonadAlgebras/WP/Basic.lean)
- [`../loom/Loom/MonadAlgebras/Instances/Basic.lean`](../loom/Loom/MonadAlgebras/Instances/Basic.lean)
- [`../loom/Loom/MonadAlgebras/Instances/StateT.lean`](../loom/Loom/MonadAlgebras/Instances/StateT.lean)
- [`../loom/Loom/MonadAlgebras/Instances/ReaderT.lean`](../loom/Loom/MonadAlgebras/Instances/ReaderT.lean)
- [`../loom/Loom/MonadAlgebras/Instances/ExceptT.lean`](../loom/Loom/MonadAlgebras/Instances/ExceptT.lean)
- [`../loom/Loom/MonadAlgebras/PMF.lean`](../loom/Loom/MonadAlgebras/PMF.lean)
- [`../loom/Loom/SpecMonad.lean`](../loom/Loom/SpecMonad.lean)
- [`../loom/Loom/MonadUtil.lean`](../loom/Loom/MonadUtil.lean)
- [`../loom/README.md`](../loom/README.md)

Constraints observed:

- [`../loom/lean-toolchain`](../loom/lean-toolchain): Lean `v4.24.0`
- [`../loom/lakefile.lean`](../loom/lakefile.lean): Mathlib `v4.24.0`, dependency on `lean-auto`
- Loom has files outside the safe port scope (`SMT`, async/meta/tactic extras)

## 5) Bluebell / iris-lean Resources Explored

Primary integration note:

- [`../../Notes/LOOM_INTEGRATION_BLUEPRINT.md`](../../Notes/LOOM_INTEGRATION_BLUEPRINT.md)

Current repository/toolchain status:

- [`../iris-lean/lean-toolchain`](../iris-lean/lean-toolchain): Lean `v4.26.0`
- [`../iris-lean/lakefile.toml`](../iris-lean/lakefile.toml): Mathlib `v4.26.0`

Key open proof gaps confirmed:

- [`../iris-lean/src/Bluebell/Logic/JointCondition.lean`](../iris-lean/src/Bluebell/Logic/JointCondition.lean)
- [`../iris-lean/src/Bluebell/Logic/WeakestPre.lean`](../iris-lean/src/Bluebell/Logic/WeakestPre.lean)
- [`../iris-lean/src/Bluebell/Logic/Ownership.lean`](../iris-lean/src/Bluebell/Logic/Ownership.lean)
- [`../iris-lean/src/Bluebell/ProbabilityTheory/IndepProduct.lean`](../iris-lean/src/Bluebell/ProbabilityTheory/IndepProduct.lean)

## 6) Lean/Std Program Logic + Metaprogramming Layer (Key New Findings)

Lean 4.28 ships a substantial built-in WP/Hoare + VC generation stack in `Std.Do` and `Lean.Elab.Tactic.Do`.

### 6.1 Core logical layer

- Local source root:
  `/Users/quang.dao/.elan/toolchains/leanprover--lean4---v4.28.0/src/lean`

Key files:

- `Std/Do/PostCond.lean` (`PostShape`, `Assertion`, `PostCond`)
- `Std/Do/PredTrans.lean` (`PredTrans`, conjunctive/monotone transformers)
- `Std/Do/WP/Basic.lean` (`class WP`, `wp⟦x⟧` notation)
- `Std/Do/WP/Monad.lean` (`class WPMonad`, `wp_pure`, `wp_bind`)
- `Std/Do/Triple/Basic.lean` (`def Triple := P ⊢ₛ wp⟦x⟧ Q`)
- `Std/Do/Triple/SpecLemmas.lean` (`[spec]` theorem library for many monadic ops)

Interpretation:

- This is a generic transformer-aware WP/triple framework already aligned with `do`-notation reasoning.
- It is orthogonal to VCVio semantics and can be reused for ergonomics even if we keep Loom-style algebraic semantics.

### 6.2 Metaprogramming/automation layer

Syntax + docs:

- `Std/Tactic/Do/Syntax.lean`
  - tactics: `mstart`, `mstop`, `mleave`, `mspec`, `mvcgen`, `mvcgen?`, `mspecialize`, `mcases`, etc.
  - `@[spec]` attribute contract for theorem pickup by `mspec`/`mvcgen`
  - `mvcgen_trivial` extension hook

Elaboration internals:

- `Lean/Elab/Tactic/Do/VCGen.lean` (VC engine, split/join-point handling, config flags)
- `Lean/Elab/Tactic/Do/Spec.lean` (spec theorem lookup and application)
- `Lean/Elab/Tactic/Do/Attr.lean` (`spec` attribute implementation + internal simp integration)
- `Lean/Elab/Tactic/Do/ProofMode/*.lean` (goal-shape tactics)

Notable behavior:

1. `mvcgen` is explicitly marked experimental in source warnings.
2. `spec` attribute supports both triple specs and simp rules consumed by VCGen.
3. VCGen can aggressively split `if`/`match`; config has controls (`jp`, `elimLets`, `stepLimit`) to avoid blowups.

### 6.3 Mathlib usage check

- Searched Mathlib for direct `mvcgen`/`mspec` adoption; effectively no significant usage surfaced.
- Conclusion: this stack is powerful but still relatively niche/bleeding-edge in ecosystem usage.

## 7) Does the Direction Make Sense?

Yes. Your target is coherent:

1. Semantics: Loom-style algebraic WP/triple design fits extensibility requirements.
2. Domain bridge: VCVio already has `evalDist`/`probEvent`/`probOutput`, so quantitative WP is natural.
3. Ergonomics: Lean's `Std.Do` metaprogramming is directly relevant for better proof UX on `do` code.

Most important sequencing constraint:

- Bluebell integration should be deferred for now due version mismatch + many `sorry` in key logic files.

## 8) Implementation Plan (Recommended)

### Phase A — Establish stable unary probabilistic WP in VCVio (now)

1. Port Loom *core only* into `ToMathlib`:
   - `MonadAlgebras/Defs`
   - `MonadAlgebras/WP/Basic`
   - core transformer instances (`StateT`, `ReaderT`, `ExceptT`, minimal base)
2. Add `PMF`/`ENNReal` algebra adaptation for Lean 4.28.
3. Build `OracleComp`-specialized quantitative WP/triple API in new `VCVio/ProgramLogic/Unary/WP.lean`.
4. Prove bridge lemmas:
   - `probEvent` as indicator-post WP,
   - `probOutput` as singleton-indicator WP.
5. Keep existing `HoareTriple.lean` until new API proves out.

### Phase B — Ergonomics layer using Lean `Std.Do` tactics (now/next)

1. Add a thin VCVio wrapper module (e.g. `VCVio/ProgramLogic/Unary/DoTactics.lean`) that imports:
   - `Std.Do`
   - `Std.Tactic.Do`
2. Register VCVio-specific `[spec]` lemmas for frequently used combinators in oracle/probability code.
3. Provide starter tactic macros for local workflow (non-invasive):
   - preferred `mvcgen` config defaults for VCVio proofs,
   - optional custom `mvcgen_trivial_extensible` rules for common arithmetic/simp goals.
4. Validate on one canonical example proof (`Examples/OneTimePad.lean` or similar).

### Phase C — Migrate and simplify ProgramLogic surface (after A+B stable)

1. Replace ad-hoc `StateM`-specific API usage with new generalized unary API.
2. Keep compatibility shims temporarily if needed.
3. Update root imports in `VCVio.lean`.

### Phase D — Relational logic (later)

1. Add relational layer under `VCVio/ProgramLogic/Relational/`.
2. Start with coupling-based relational rules (reusing existing coupling infrastructure).
3. Avoid tying to separation logic until unary stack and ergonomics settle.

### Phase E — Bluebell integration (defer)

Prerequisites:

1. Toolchain alignment (`iris-lean` to Lean/Mathlib 4.28).
2. Close major `sorry` in Bluebell `JointCondition` / `WeakestPre` / `Ownership` / `IndepProduct`.
3. Then integrate BI/frame resources as an optional backend, not a blocker for VCVio unary WP.

## 9) API Design Guidelines for the Refactor

1. Keep import layering intact (`EvalDist` must not depend on `OracleComp` internals in reverse).
2. Preserve VCVio `ReaderT` design discipline (avoid globally ambiguous reader instances).
3. Separate:
   - semantic core (`wp`, `triple`, laws),
   - automation layer (`[spec]`, tactics),
   - high-level crypto-facing helper lemmas.
4. Avoid hard dependency on Loom repo; port what is needed.

## 10) Suggested Immediate Work Queue

1. Create `ToMathlib/Control/MonadAlgebras/Defs.lean` + `WP/Basic.lean` (ported/adapted).
2. Create `VCVio/ProgramLogic/Unary/WP.lean` with `OracleComp` quantitative WP.
3. Add minimal `VCVio/ProgramLogic/Unary/DoTactics.lean` with `Std.Tactic.Do` import and first `[spec]` lemmas.
4. Prove one end-to-end example using `mspec`/`mvcgen` where helpful.
5. Run `lake build` after each structural step.

## 11) Repro Queries Used

```bash
rg --files VCVio/ProgramLogic ../loom
rg -n "Hoare|WP|Dijkstra|triple|assert|assume|relational|separation" VCVio/ProgramLogic ../loom
rg --files /Users/quang.dao/.elan/toolchains/leanprover--lean4---v4.28.0/src/lean/Std | rg '/Do(\\.|/)'
rg --files /Users/quang.dao/.elan/toolchains/leanprover--lean4---v4.28.0/src/lean/Lean | rg 'Elab/Tactic/Do'
rg -n "mvcgen|mspec|mstart|mleave|\\[spec\\]" /Users/quang.dao/.elan/toolchains/leanprover--lean4---v4.28.0/src/lean/Std /Users/quang.dao/.elan/toolchains/leanprover--lean4---v4.28.0/src/lean/Lean/Elab/Tactic/Do
rg -n "sorry" ../iris-lean/src/Bluebell/Logic/JointCondition.lean ../iris-lean/src/Bluebell/Logic/WeakestPre.lean ../iris-lean/src/Bluebell/Logic/Ownership.lean ../iris-lean/src/Bluebell/ProbabilityTheory/IndepProduct.lean
lake build
```

