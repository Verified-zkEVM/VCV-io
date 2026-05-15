# Interaction Integration

VCV-io depends on PolyFun for the generic interaction framework.
Do not duplicate PolyFun's interaction guide here.
Use this page for VCV-specific runtime, computational, and example integration only.

## Source of Truth

Generic protocol theory lives in PolyFun:

- Sequential specs, transcripts, decorations, strategies, append, replicate, and state chains: `PolyFun.Interaction.Basic.*`
- Two-party, multiparty, and concurrent interaction layers: `PolyFun.Interaction.TwoParty.*`, `PolyFun.Interaction.Multiparty.*`, `PolyFun.Interaction.Concurrent.*`
- Generic UC interfaces, open processes, open theory, notation, environment actions, and leakage scaffolding: `PolyFun.Interaction.UC.*`

For conceptual background, read PolyFun's `docs/wiki/interaction.md` and the module docstrings in the PolyFun dependency.
VCV-io should only document how those generic APIs are instantiated with probabilistic semantics, oracle computations, and crypto examples.

## VCV-Specific Layers

VCV-io retains the computational and runtime interpretation of PolyFun's generic UC layer:

| File | Purpose |
|------|---------|
| `VCVio/Interaction/UC/Computational.lean` | Computational observation layer for UC-style emulation using `SPMF` and total variation distance. |
| `VCVio/Interaction/UC/Runtime.lean` | Synchronous runtime semantics for closed open processes, including `processSemantics`, `processSemanticsProbComp`, and `processSemanticsOracle`. |
| `VCVio/Interaction/UC/AsyncRuntime.lean` | Asynchronous runtime semantics with process ticks and environment events. |
| `VCVio/Interaction/UC/AsyncSecurity.lean` | Fair-PPT security wrappers for asynchronous env-open executions. |
| `VCVio/Interaction/UC/Standard.lean` | Standard VCV-io UC imports and conveniences. |
| `VCVio/Interaction/UC/StdDoBridge.lean` | Bridges from VCV-io program-logic/Std.Do idioms into the UC runtime layer. |

These files may import PolyFun interaction modules.
Generic interaction modules should not be reintroduced under `VCVio/Interaction` or `ToMathlib`.

## Runtime Semantics

`OpenProcess m Party Δ` comes from PolyFun and carries its per-step `Spec.Sampler m` intrinsically.
VCV-io's runtime layer interprets a closed process by running those samplers and then observing the resulting state in a probabilistic semantics.

Use the synchronous entry points in `VCVio/Interaction/UC/Runtime.lean`:

```lean
import VCVio.Interaction.UC.Runtime
```

- `processSemantics` runs in an arbitrary surface monad `m` with a bundled `SPMFSemantics m`.
- `processSemanticsProbComp` specializes to coin-flip-only `ProbComp` protocols.
- `processSemanticsOracle` specializes to `OracleComp superSpec`, interpreting shared oracle access through `simulateQ'`.

Use the asynchronous entry points in `VCVio/Interaction/UC/AsyncRuntime.lean` when the environment can interleave direct events with process steps:

```lean
import VCVio.Interaction.UC.AsyncRuntime
```

- `RuntimeEvent Event` distinguishes `processTick` from `envTick e`.
- `EnvAction m Event State` is provided by PolyFun and reacts in the same surface monad as the runtime.
- `processSemanticsAsync` and `processSemanticsAsyncProbComp` are the main async semantic constructors.

## Computational Security

Use `VCVio/Interaction/UC/Computational.lean` for the distributional observation layer:

```lean
import VCVio.Interaction.UC.Computational
```

Important definitions:

- `Semantics T` bundles a result type, a surface monad, its `SPMFSemantics`, and a closed-system runner.
- `Semantics.evalDist` evaluates a closed system to an `SPMF sem.Result`.
- `Semantics.distAdvantage` computes total variation distance between two closed systems.
- `ObservedCompEmulates sem ε real ideal` states fixed-advantage computational emulation.
- `AsympObservedCompEmulates` packages the negligible asymptotic variant.
- `ObservedCompUCSecure` is the simulator-based security wrapper.
- `Execution T` is the distributional experiment consumed by paper-level `Standard.UCSecure`.

The generic equivalence-style UC judgments live in PolyFun.
The VCV-io layer gives them a crypto-facing distributional interpretation.
Use the `Observed*` definitions when you intentionally work relative to a chosen observer.
Use `Standard.UCSecure exec ε π F` when stating textbook UC security for a fixed execution experiment; `Execution.ofSemantics` is an explicit bridge from an observer to such an execution.

## Examples

The main smoke test for the integration is `Examples/OneTimePad/UC.lean`.
It builds real and ideal one-time-pad systems as PolyFun open-theory objects and proves the observation-level statement `ObservedCompEmulates 0`.

Use it as the first example when wiring a concrete protocol into the UC runtime and computational observation layer.
For lower-level probabilistic and oracle examples, see `docs/agents/probability.md` and `docs/agents/oracle-comp.md`.

## Import Guide

Choose the smallest import matching the task:

```lean
-- Generic interaction APIs from PolyFun
import PolyFun.Interaction.Basic.Spec
import PolyFun.Interaction.Basic.Strategy
import PolyFun.Interaction.Concurrent.Process
import PolyFun.Interaction.UC.OpenProcess
import PolyFun.Interaction.UC.OpenProcessModel

-- VCV-specific runtime and security interpretation
import VCVio.Interaction.UC.Runtime
import VCVio.Interaction.UC.AsyncRuntime
import VCVio.Interaction.UC.Computational
import VCVio.Interaction.UC.Standard
```

When editing VCV-io, prefer importing the specific PolyFun module you need rather than re-exporting large generic surfaces through VCV-io.
