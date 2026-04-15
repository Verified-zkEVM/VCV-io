# Interaction Framework

General-purpose protocol interaction theory: sequential specs, two-party roles,
multiparty local views, and concurrent process semantics.

## Design philosophy

The framework is organized around a few stable principles:

- **Continuation-first semantics.**
  `Spec` is a W-type (dependent tree): each round's continuation type depends
  on the move chosen.
  All composition, decoration, and strategy types respect this structure.
- **Control vs observation are orthogonal.**
  Who *chooses* a move (`Control`) and who *sees* a move (`Profile`, `LocalView`)
  are independent axes.
  A party can control a node but see only a quotient of its own move, or observe
  a node fully without controlling it.
- **Boundary vs composition.**
  *Boundaries* adapt the interface of a fixed protocol (same transcript shape,
  same round structure).
  *Composition* (`append`, `replicate`, `stateChain`) extends the protocol with
  new rounds.
  Never conflate the two.
- **Concurrency is layered.**
  The kernel is `par` + `Front` (frontier) + `residual` (one-step reduction).
  Interleaving is the basic semantics; independence and true concurrency are
  refinements on top.
  Dynamic `Process` wraps sequential `Spec` episodes into a coinductive stream.
- **UC as a frontend, not the foundation.**
  The open-systems layer (`Interface`, `PortBoundary`, `OpenTheory`) provides
  compositional operations (`map`, `par`, `wire`, `plug`).
  UC-style emulation, scope policies, and runtime semantics are built *on top*
  of these primitives, not baked into the core.

## Quick orientation

| Layer | Directory | What it models |
|-------|-----------|----------------|
| Sequential core | `Basic/` | Specs, transcripts, decorations, strategies, composition |
| Two-party | `TwoParty/` | Sender/receiver roles, counterparts, Fiat-Shamir replay |
| Multiparty | `Multiparty/` | Per-party local views (active/observe/hidden/quotient) |
| Concurrent | `Concurrent/` | Parallel composition, frontiers, processes, refinement, open systems |

Dependencies flow downward: `Concurrent/` may import `Multiparty/` and `Basic/`;
`TwoParty/` and `Multiparty/` import only `Basic/`.

## Core types

### `Spec` and `Transcript` (`Basic/Spec.lean`)

`Spec` is an inductive tree: `done` (no more moves) or `node Moves rest`
(one round of type `Moves`, with dependent continuation `rest : Moves → Spec`).
`Transcript spec` is one full play through a `Spec`.

### `Decoration` (`Basic/Decoration.lean`)

`Decoration Γ spec` attaches node-local metadata from a `Node.Context Γ` to every
node of a `Spec`.
`Decoration.Over` adds a dependent second layer.
Used for role labels, monad annotations, party assignments, etc.

### `Strategy` (`Basic/Strategy.lean`)

`Strategy m spec Output` is a one-player strategy with monadic effects in `m`.
`Strategy.run` executes it against a counterpart to produce a `Transcript`.
`Strategy.mapOutput` is functorial over the output family.

## Sequential composition

Three ways to compose specs sequentially, each suited to a different pattern:

| Combinator | When to use |
|------------|-------------|
| `Spec.append s₁ s₂` | Two-phase protocol where phase 2 depends on phase 1's transcript |
| `Spec.replicate spec n` | Fixed `n`-fold repetition of an identical spec |
| `Spec.stateChain Stage step n` | `n` stages with explicit state threading |
| `Spec.Chain n` | Continuation-style telescope (no external state type needed) |

`Transcript.liftAppend` lifts a type family on the first transcript to the
combined transcript, avoiding `cast`/`Eq.rec` pollution.
`Strategy.comp` composes strategies along `append`.

## Two-party protocols (`TwoParty/`)

Label each node with `Role` (`.sender` or `.receiver`) via `RoleDecoration`.
Then:

- **`Strategy.withRoles m spec roles Output`**: the focal party's strategy,
  seeing sender nodes as "produce a move" and receiver nodes as "observe a move".
- **`Counterpart m spec roles Output`**: the environment (verifier if focal is prover).
- **`Strategy.runWithRoles`**: executes focal + counterpart to get a transcript.

For public-coin protocols, `PublicCoinCounterpart` and `replay` support
Fiat-Shamir-style transcript replay.

### Composition

`Strategy.compWithRoles` and `Counterpart.append` compose along `Spec.append`.
The flat variants (`compWithRolesFlat`, `Counterpart.appendFlat`) take a single
output family on the combined transcript.
Factorization theorems (e.g. `runWithRoles_compWithRoles_append`) show that
executing a composed protocol equals sequential execution of its parts.
These require `LawfulCommMonad` (independent effects may be swapped).

## Multiparty local views (`Multiparty/`)

`LocalView X` characterizes what a participant sees at a node with move type `X`:

| Constructor | Meaning |
|-------------|---------|
| `.active` | Participant chooses the move |
| `.observe` | Participant sees the full move |
| `.hidden` | Participant sees nothing |
| `.quotient f` | Participant sees `f x` (partial information) |

Three packaged resolver patterns:

- **`Broadcast.Strategy`**: one acting party per node, all others observe.
- **`Directed.Strategy`**: sender/receiver pair per node.
- **`Profile.Strategy`**: full per-party `ViewProfile` decoration.

## Concurrent processes (`Concurrent/`)

### Structural layer

`Concurrent.Spec` extends `Spec` with `par left right`.
`Front S` is the type of currently enabled frontier events.
`residual event` gives the spec after one event fires.
The `diamond` theorem proves independent events commute.
`Trace.Equiv` identifies different linearizations of independent events.

### Dynamic processes

`Process Party` is a coinductive-style stream: each step is a sequential
`Interaction.Spec` episode, producing a residual process.
`Process.Run` and `Process.Prefix` model infinite and finite executions.
`Machine` provides a state-indexed transition-system frontend that compiles
to `Process` via `Machine.toProcess`.

### Coalgebraic structure

Both `ProcessOver` and `Machine` are instances of the `Coalg` typeclass
defined in `ToMathlib/Control/Coalgebra.lean`.
An `Coalg F S` is a type `S` together with `out : S → F S`,
the categorical dual of `MonadAlgebra`.

- `StepOver Γ` is a `Functor` (post-compose on `next`), and `LawfulFunctor`.
- `ProcessOver Γ` is an `Coalg (StepOver Γ)` via its `step` field.
- `Machine.StepFun` is a `Functor` and `LawfulFunctor`.
- `Machine` is an `Coalg Machine.StepFun` via its `Enabled`/`step` fields.

This reflects the Poly/ACT perspective: a process is a coalgebra for a
polynomial endofunctor, with the step functor playing the role of the
"interface polynomial."

### Interleaving combinator

`ProcessOver.interleave` factors out the binary-choice interleaving pattern
shared by `par`, `wire`, and `plug` in `OpenProcessModel`.
Given two processes `p₁ : ProcessOver Γ₁`, `p₂ : ProcessOver Γ₂`,
context morphisms into a target context `Δ`, and a scheduler decoration,
it produces a `ProcessOver Δ` with product state space
`p₁.Proc × p₂.Proc`.

### Control and observation

`Control Party S` assigns ownership of payload moves and scheduling decisions.
`Profile Party S` assigns `LocalView`s to each party at frontier nodes.
`Current.view` combines both to give a party's current-step interface.

### Fairness, safety, liveness

`Fairness.lean` defines weak and strong fairness over stable ticket systems.
`Liveness.lean` provides temporal predicates (`AlwaysState`, `EventuallyState`,
`InfinitelyOftenState`) and safety/admissibility under fairness.

### Refinement and equivalence

`ForwardSimulation` lifts implementation runs to specification runs, preserving
safety and event/ticket/controller traces.
`Bisimulation` and `BackwardSimulation` establish behavioral equivalence.
Named equivalences in `Equivalence.lean` specialize to controller, trace, and
observational comparisons.

### Open systems

`Interface` (= `PFunctor`) and `PortBoundary` define typed I/O boundaries.
The choice of `PFunctor` for interfaces keeps the kernel minimal while
supporting `Packet`, `Query`, `Hom`, `comp` (Poly's composition product),
`compUnit` (composition unit), and boundary equivalences.

`OpenTheory` provides the compositional algebra: `map`, `par`, `wire`, `plug`.
Lawfulness is stratified into a class hierarchy:

- `IsLawfulMap` / `IsLawfulPar` / `IsLawfulWire` / `IsLawfulPlug`:
  functoriality of `map` and naturality of combinators.
- `IsLawful`: bundles all naturality laws.
- `Monoidal`: symmetric monoidal coherence for `par` (associativity,
  commutativity, left/right unit laws via a distinguished `unit` object).
- `CompactClosed`: compact closed structure with `idWire` as coevaluation,
  derivation of `plug` from `wire`, and a zig-zag identity (`wire_idWire`).

`OpenProcessIso` (in `OpenProcess.lean`) provides a bisimulation-based
equivalence for `OpenProcess`, used to state monoidal and compact closed laws
for the concrete `openTheory` model up to isomorphism (see `OpenProcessModel.lean`).

`OpenSyntax` provides three layers for free open-system expressions:

- `Raw` is an inductive syntax tree whose constructors mirror the `OpenTheory`
  operations. It is pattern-matchable and suitable for inspection,
  transformation, and visualization.
- `Expr` is the quotient of `Raw` by the `OpenTheory` equations, yielding a
  lawful `OpenTheory` instance by construction.
- `Interp` is a tagless-final (Church-encoded) structure (final model) that
  stores a universal interpretation function and carries a lawful `OpenTheory`
  instance.

`Expr.toInterp` embeds quotiented expressions into the lawful `Interp` model.

## Import guide

Choose the minimal set for your task:

```lean
-- Sequential protocol
import VCVio.Interaction.Basic.Spec
import VCVio.Interaction.Basic.Strategy
import VCVio.Interaction.Basic.Append      -- if composing

-- Two-party
import VCVio.Interaction.TwoParty.Strategy -- includes Role, Decoration
import VCVio.Interaction.TwoParty.Compose  -- if composing

-- Multiparty
import VCVio.Interaction.Multiparty.Core
import VCVio.Interaction.Multiparty.Broadcast  -- or Directed / Profile

-- Concurrent
import VCVio.Interaction.Concurrent.Spec
import VCVio.Interaction.Concurrent.Process
```

## File index

### `Basic/`

| File | Purpose |
|------|---------|
| `Spec.lean` | `Spec`, `Transcript`, `ofList` |
| `Node.lean` | `Node.Context`, `Node.Schema`, `Prefix` |
| `Decoration.lean` | `Decoration`, `Decoration.Over`, `telescope`, `pack`/`unpack` |
| `Syntax.lean` | `SyntaxOver`, `SyntaxOver.Family` |
| `Shape.lean` | `ShapeOver` (functorial `SyntaxOver` with continuation map) |
| `Interaction.lean` | `InteractionOver`, `Interaction`, `run` |
| `Strategy.lean` | `Strategy`, `Strategy.run`, `mapOutput` |
| `Append.lean` | `Spec.append`, transcript ops, `Strategy.comp`/`compFlat` |
| `Replicate.lean` | `Spec.replicate`, `Strategy.iterate` |
| `StateChain.lean` | `Spec.stateChain`, `Strategy.stateChainComp` |
| `Chain.lean` | `Spec.Chain`, `Chain.toSpec`, `Chain.ofStateMachine` |
| `Ownership.lean` | `LocalView`/`LocalRunner` builders for `SyntaxOver` |
| `MonadDecoration.lean` | `MonadDecoration`, `Strategy.withMonads`, `runWithMonads` |
| `BundledMonad.lean` | `BundledMonad` (monad packaged for inductive data) |

### `TwoParty/`

| File | Purpose |
|------|---------|
| `Role.lean` | `Role`, `swap`, `Action`, `Dual`, `interact` |
| `Decoration.lean` | `RoleDecoration`, `RoleContext`, `RoleSchema`, monad contexts |
| `Strategy.lean` | `withRoles`, `Counterpart`, `PublicCoinCounterpart`, `replay` |
| `Compose.lean` | `compWithRoles`, `Counterpart.append`, factorization theorems |
| `Refine.lean` | `Role.Refine`, equivalence with `Decoration.Over` |
| `Swap.lean` | Role swap involutivity and append compatibility |
| `Examples.lean` | Definitional `rfl` checks on small specs |

### `Multiparty/`

| File | Purpose |
|------|---------|
| `Core.lean` | `LocalView`, `ObsType`, `Action`, `Multiparty.Strategy` |
| `Broadcast.lean` | `PartyDecoration`, `Broadcast.Strategy` |
| `Directed.lean` | `EdgeDecoration`, `Directed.Strategy` |
| `Profile.lean` | `ViewProfile`, `Profile.Decoration`, `Profile.Strategy` |
| `Examples.lean` | Broadcast, directed, profile, adversarial leakage examples |

### `Concurrent/`

| File | Purpose |
|------|---------|
| `Spec.lean` | `Concurrent.Spec` (`done`/`node`/`par`), `isLive` |
| `Frontier.lean` | `Front`, `residual`, liveness lemmas |
| `Trace.lean` | `Trace` (finite linearization), `length` |
| `Independence.lean` | `Independent`, `diamond` |
| `Interleaving.lean` | `Trace.Equiv`, `cast` |
| `Control.lean` | `Control`, `scheduler?`, `current?`, `controllers` |
| `Profile.lean` | `Profile`, `observe`, `residual`, `frontierView` |
| `Current.lean` | `view`, `observe`, `residualView` |
| `Process.lean` | `StepOver`, `ProcessOver`, `Process`, systems, `Functor (StepOver Γ)`, `Coalg` instance, `interleave` |
| `Tree.lean` | Structural concurrent syntax → `Process` |
| `Machine.lean` | `Machine`, `Machine.toProcess`, `Machine.StepFun`, `Coalg` instance |
| `Execution.lean` | `Trace`, `ObservedTrace` for processes |
| `Run.lean` | `Prefix`, `Run` (infinite), controller/event extraction |
| `Policy.lean` | `StepPolicy`, `respects`, combinators |
| `Observation.lean` | `PackedObs`, transcript relations, observation preservation |
| `Refinement.lean` | `ForwardSimulation`, safety/trace preservation |
| `Bisimulation.lean` | `Bisimulation`, `BackwardSimulation`, `refl`, `symm` |
| `Equivalence.lean` | Controller, trace, observational equivalences |
| `Fairness.lean` | `WeakFair`, `StrongFair`, temporal predicates |
| `Liveness.lean` | `Safe`, `Satisfies`, `Admissible`, state predicates |
| `Examples.lean` | Worked examples: profiles, control, execution, policies |

### `UC/`

| File | Purpose |
|------|---------|
| `Interface.lean` | `Interface`, `PortBoundary`, `Hom`, `Equiv`, `comp`/`compUnit`, tensor/swap |
| `OpenTheory.lean` | `OpenTheory` algebra, `IsLawful`, `Monoidal`, `CompactClosed` |
| `OpenSyntax/Raw.lean` | `Raw` syntax tree, `Raw.interpret`, `Raw.Equiv` (incl. monoidal/CC equations) |
| `OpenSyntax/Interp.lean` | `Interp` (tagless-final), `Monoidal`/`CompactClosed` instances |
| `OpenSyntax/Expr.lean` | `Expr` (quotient of `Raw`), `Monoidal`/`CompactClosed` instances, `Expr.toInterp` |
| `OpenProcess.lean` | `BoundaryAction`, `OpenProcess`, `OpenProcessIso` (bisimulation equivalence) |
| `OpenProcessModel.lean` | `openTheory` (concrete model), `IsLawful`, monoidal/CC laws up to `OpenProcessIso` |
| `Emulates.lean` | `Emulates`, `UCSecure` (contextual emulation and UC security) |
| `Computational.lean` | `Semantics`, `CompEmulates`, `AsympCompEmulates` (computational observation layer) |
| `Runtime.lean` | `Spec.Sampler m`, `sampleTranscript`, `ProcessOver.runSteps`, `processSemantics` (monad-parametric), `processSemanticsProbComp`, `processSemanticsOracle` (oracle-aware runtime) |

## In-tree examples

- **`TwoParty/Examples.lean`**: `rfl` checks that `withRoles`/`Counterpart` types
  unfold correctly on a two-step spec.
- **`Multiparty/Examples.lean`**: Pattern-matching resolvers for broadcast,
  directed, and profile-based models; adversarial leakage and adaptive corruption.
- **`Concurrent/Examples.lean`**: Small concurrent specs with profiles, control,
  process execution, policies, and interleaving.
