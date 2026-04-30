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
  Who *chooses* a move (per-node: `NodeAuthority`; per-spec-tree: `Concurrent.Control`)
  and who *sees* a move (per-node: `NodeView`; per-party-per-node:
  `Multiparty.ViewMode`; per-spec-tree: `Concurrent.Profile`) are independent axes.
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
| Multiparty | `Multiparty/` | Per-party local view modes (pick/observe/hidden/react) and observation kernels |
| Concurrent | `Concurrent/` | Parallel composition, frontiers, processes, refinement, open systems |

Dependencies flow downward: `Concurrent/` may import `Multiparty/` and `Basic/`;
`TwoParty/` and `Multiparty/` import only `Basic/`.

## Core concepts: Spec, Node, Party, Profile

Before reading any one file, it helps to fix four words. They are the load-bearing
vocabulary of the entire `Interaction/` layer.

### Node — a structural location in the protocol tree

A `Spec` is an interaction tree (`VCVio/Interaction/Basic/Spec.lean`). A **node** is one
branching point of that tree: a pair `(Moves : Type, rest : Moves → Spec)`. It is *not*
an actor; it is a location where some next move gets chosen. At the level of `Spec`
alone, a node knows its move space and its continuation family, and nothing else: not
who chooses, not who watches, not what monad runs, not what data is attached. Those
concerns are deferred to companion layers (`Decoration`, `NodeProfile`, `StepOver`,
`SyntaxOver`, `InteractionOver`).

The namespace `Spec.Node.*` (`Context`, `Schema`, `ContextHom` in
`VCVio/Interaction/Basic/Node.lean`) is *generic node-context infrastructure*: for any
type family `Γ : Type → Type`, a `Γ`-decoration attaches one `Γ X` value at every node
with move space `X`.

### Party — an actor that plays across many nodes

A `Party` is a free type parameter introduced by the *content* layers (`Multiparty/`,
`Concurrent/`, `UC/`). A party is an actor that may control or observe moves at
*various* nodes throughout the same protocol tree. A party is whole-tree (it has a
strategy across the entire `Spec`); a node is local (it lives at one location in the
tree). Typically there are *many more* nodes than parties: a long protocol may have
unboundedly many nodes (or a continuation-based infinite stream of them via
`ProcessOver`), but always the same finite party set.

### ViewMode — what a single party sees at a single node

`Multiparty.ViewMode X` (`Multiparty/Core.lean`) records how *one* party locally
experiences a node whose move space is `X`. The four constructors
`pick` / `observe` / `hidden` / `react ⟨Obs, toObs⟩` are the canonical
observation modes. A `ViewMode` is the smallest atomic node × party ×
observation triple in the framework.

The information content of a `ViewMode` is captured by `Multiparty.Observation X`
(`Multiparty/Observation.lean`), a `Σ Obs : Type, X → Obs` realized as
`PFunctor.Idx (Observation.basePFunctor X)`. `Observation X` carries
Mathlib's order typeclasses (`⊤`, `⊥`, `≤`, `⊔`) so refinement and join in
the information lattice use standard notation.

### NodeProfile — per-node attribution of who-authors-what and who-sees-what

`NodeProfile Party X` (`Concurrent/Process.lean`) is the bridge between a single node
and the whole party set. It bundles two orthogonal factor structures:

- `NodeAuthority Party X`: `controllers : X → List Party` — for each possible move,
  which parties are credited as having authored it (move-dependent and possibly
  multi-controller).
- `NodeView Party X`: `views : Party → Multiparty.ViewMode X` — for each
  party, what local view they have at this node.

The structure `extends` both factors, so dot-notation field access
(`node.controllers x`, `node.views me`) and the structure-literal constructor
`{ controllers := ..., views := ... }` work transparently. Code that depends only on
authorship can take a `NodeAuthority Party X` parameter; code that depends only on
observation can take a `NodeView Party X` parameter.

The naming `NodeView` (rather than `NodeObservation`) deliberately avoids
collision with `Multiparty.Observation X`, the kernel-level *information
content* of a single party's view.

`OpenNodeProfile Party Δ X` (`UC/OpenProcess.lean`) is the open-system extension that
adds one `BoundaryAction Δ X` field for external traffic.

### Mental picture

The protocol tree is the stage; **nodes** are scenes on the stage; **parties** are
actors who appear in many scenes; a **`NodeProfile`** is one scene's cast list and
sightlines. `ViewMode` is a single actor's vantage on a single scene.

| Concept | Scope | Role |
|---|---|---|
| `Spec` | whole protocol tree | branching shape of all possible plays |
| Node | one location in the tree | one scene: move space + continuation |
| Party | spans the whole tree | actor; may control or observe at various nodes |
| `Multiparty.ViewMode X` | one node × one party | that party's vantage on that one scene |
| `Multiparty.Observation X` | one node × one party | information content (kernel) of that vantage |
| `NodeProfile Party X` | one node × all parties | full cast list + sightlines for that scene |

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

`ViewMode X` characterizes what a participant sees at a node with move type `X`:

| Constructor | Meaning |
|-------------|---------|
| `.pick` | Participant locally selects the move (effectful Σ-of-X) |
| `.observe` | Participant sees the full move (function-from-X) |
| `.hidden` | Participant sees nothing |
| `.react ⟨Obs, toObs⟩` | Participant sees `toObs x : Obs` (partial information) |

Three packaged resolver patterns:

- **`Broadcast.Strategy`**: one acting party per node, all others observe.
- **`Directed.Strategy`**: sender/receiver pair per node.
- **`Profile.Strategy`**: full per-party `ViewProfile` decoration.

### Information kernel vs operational shape

`ViewMode` carries information along **two orthogonal axes**:

- **Information** — what observation does the participant make? Fully captured
  by a single projection `toObs : X → Obs` packaged with its codomain `Obs`.
  This polynomial-element form is `Multiparty.Observation X`, defined as
  `PFunctor.Idx (Observation.basePFunctor X)` where
  `Observation.basePFunctor X := ⟨Type, (X → ·)⟩`. Concretely it unfolds to
  `Σ Obs : Type, X → Obs`. Every `ViewMode X` collapses to an `Observation X`
  via `ViewMode.toObservation`.
- **Operational** — what continuation-passing shape does the participant use
  for `Action`? `.pick` (effectful Σ-of-X), `.observe` (function-from-X),
  `.hidden` (function-into-Cont, prepared in advance), `.react` (function on
  the observation, prepared in advance).

The four-constructor `ViewMode` is the *ergonomically convenient* form; it
specializes `Action` to a definitionally simpler shape per pattern, which
keeps protocol examples short. `Observation` is the *semantically universal*
form; protocols whose participants make arbitrary observations not captured
by `.pick` / `.observe` / `.hidden` should build observations directly. The
two are related by `ViewMode.toObservation` (collapse) and
`Observation.toViewMode` (lift into the universal `.react` constructor); on
the operational side, `ViewMode.Action (.react ⟨..⟩) = Observation.Action ⟨..⟩`
definitionally.

The information lattice on `Observation X` is exposed via Mathlib's order
typeclasses, so `⊤`, `⊥`, `≤`, `⊔` work directly:

- `⊤ : Observation X` is `Observation.top X = ⟨X, id⟩` — full information.
  This is exactly the kernel of `ViewMode.observe`.
- `⊥ : Observation X` is `Observation.bot X = ⟨PUnit, fun _ => .unit⟩` —
  no information. This is exactly the kernel of `ViewMode.hidden`.
- `k₁ ≤ k₂` denotes `Observation.Refines k₁ k₂` — `k₁` is no more revealing
  than `k₂`.
- `k₁ ⊔ k₂` denotes `Observation.combine k₁ k₂` — the join (Σ-product) of
  two observations.

`Refines` is only a *preorder* (mutual refinement permits codomain
bijections), so `Observation X` carries `Preorder`, `OrderTop`, `OrderBot`
and `Max` instances but not `PartialOrder` / `SemilatticeSup`. Profile-level
order theory comes through Mathlib's `Pi` instances on
`ObservationProfile Party X = Party → Observation X` for free.

Note that the operational distinction `.pick` vs `.observe` is **not** the
canonical authorship attribution. Authorship-of-move is recorded by
`Concurrent.NodeAuthority.controllers : X → List Party` (move-dependent,
possibly multi-controller). `ViewMode.pick` indicates only that the
participant chooses *locally* in its endpoint; the protocol-level controllers
of a given move are recorded separately.

### Literature

Three independent traditions converge on the kernel form `Σ Obs, X → Obs`:

- *Epistemic logic* (Halpern-Vardi "Reasoning About Knowledge"): agent
  observation as a projection from global state to local indistinguishability
  classes.
- *Noninterference / info-flow* (Goguen-Meseguer; Sabelfeld-Myers
  "Language-Based Information-Flow Security"): per-security-level projection
  of observable outputs.
- *Session types and endpoint projection* (Honda-Yoshida-Carbone "Multiparty
  Asynchronous Session Types"; Cruz-Filipe-Montesi "A Core Model for
  Choreographic Programming"): projection of a global type / global play to a
  single role's local view.

Closest type-theoretic ancestor: Hancock-Setzer "Interactive Programs in
Dependent Type Theory" — Command/Response interfaces with embedded
observation modes mirror the four-constructor operational shape.

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
`Profile Party S` assigns `ViewMode`s to each party at frontier nodes.
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
Lawfulness is stratified into a granular Mathlib-style class hierarchy. Carriers:

- `HasUnit` — distinguished monoidal unit object for `par`.
- `HasIdWire` — distinguished identity-wire builder for `wire`.

Naturality:

- `IsLawfulMap` / `IsLawfulPar` / `IsLawfulWire` / `IsLawfulPlug`:
  functoriality of `map` and naturality of each combinator.
- `IsLawful`: bundles all naturality laws.

Coherence (each subsequent class adds laws on top of the previous):

- `IsMonoidal`: symmetric monoidal coherence for `par` (associativity,
  commutativity, left/right unit laws via the `HasUnit` object).
- `IsTraced`: Joyal-Street-Verity traced symmetric monoidal structure
  (`wire`-trace yanking, sliding, vanishing).
- `IsCompactClosed`: compact closed structure (a `(Poly, ⊗)`-friendly
  weakening; the strict snake equations are *not* asserted, since
  `(Poly, ⊗)` is monoidal closed but not strictly compact closed; see
  Spivak arXiv:2202.00534 §4.3).
- `HasPlugWireFactor`: closure-factorization identities relating
  `plug` to `wire` (`plug_eq_wire`, `plug_par_left`, `plug_wire_left`).

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

### Monad-parametric open processes and intrinsic samplers

`OpenProcess m Party Δ` (`UC/OpenProcess.lean`) is the runtime-facing analogue of
`Concurrent.ProcessOver`: an `m`-parametric structure that bundles, at every
step, a `Spec.Sampler m` for resolving that step's nondeterminism. Samplers are
carried as data, not threaded through as an external argument. Three concrete
consequences:

1. **Samplers are a decoration, not a side argument.**
   `Spec.Sampler m spec` is definitionally `Decoration (fun X => m X) spec`
   (`Basic/Sampler.lean`). Every move type `X` in the spec receives an `m X`
   computation; `sampleTranscript` folds a sampler into an `m (Transcript spec)`.
   Universe-polymorphic at `(w, w')` so that `m : Type w → Type w'` and
   `spec : Spec.{w}`.
2. **`OpenProcess` carries `stepSampler` as a field.**
   For each reachable step, `OpenProcess.stepSampler` supplies the
   `Spec.Sampler m` that resolves that step's move choices. The underlying pure
   structure is still a `Concurrent.ProcessOver`, recoverable via
   `OpenProcess.toProcess`. The structural layer (`StepOver`, `ProcessOver`) is
   left untouched.
3. **`openTheory m Party schedulerSampler` threads samplers compositionally.**
   The monad `m` and a scheduler sampler (`m (ULift Bool)` resolving
   binary-choice scheduler nodes introduced by `par` / `wire` / `plug`) become
   parameters of the concrete model. Each combinator builds the new step's
   sampler via `Spec.Sampler.interleave` from its inputs' samplers, so any law
   about `map`/`par`/`wire`/`plug` that holds in the pure structural theory
   lifts to the monad-parametric one once `schedulerSampler` is fixed.

Runtime semantics drop the external `sampler` argument accordingly:
`processSemantics`, `processSemanticsProbComp`, and `processSemanticsOracle`
(`UC/Runtime.lean`) pull the per-step sampler from `process.stepSampler`, as do
their asynchronous counterparts in `UC/AsyncRuntime.lean`. Typeclass ornaments
(`Spec.Fintype` in `Basic/SpecFintype.lean`, mirroring `OracleSpec.Fintype`) let
users recover canonical uniform samplers (`Sampler.uniformI`) without writing
one by hand.

The end-to-end flow is exhibited by `Examples/OneTimePad/UC.lean`: both the
real and ideal one-time pads are built as
`(openTheory (OptionT ProbComp) Party demoSchedulerSampler).Obj (Δ_otp sp)`
with intrinsic uniform key-sampling nodes and genuine `BoundaryAction.emit`
ciphertext packets, and `CompEmulates 0` is discharged from the structural
equivalence of their emissions.

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

-- UC / open systems
import VCVio.Interaction.UC.OpenTheory
import VCVio.Interaction.UC.OpenProcess
import VCVio.Interaction.UC.OpenProcessModel
import VCVio.Interaction.UC.Runtime
import VCVio.Interaction.UC.Computational
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
| `Sampler.lean` | `Spec.Sampler m spec := Decoration (fun X => m X) spec` (per-node monadic samplers as data), `sampleTranscript`, `Sampler.interleave`, `Sampler.uniformI` |
| `SpecFintype.lean` | `Spec.Fintype` per-spec ornament (recursive `Fintype` + `Nonempty` for every move type); enables canonical `Sampler.uniformI` |

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
| `Core.lean` | `ViewMode`, `ObsType`, `Action`, `ViewMode.toObservation` / `Observation.toViewMode` (kernel bridges), `Multiparty.Strategy` |
| `Observation.lean` | `Multiparty.Observation` (= `PFunctor.Idx (Observation.basePFunctor X)`), `top`/`bot`/`Refines`/`combine`/`postcomp`/`Action`, Mathlib order typeclasses (`Top`/`Bot`/`LE`/`Preorder`/`OrderTop`/`OrderBot`/`Max`) |
| `ObservationProfile.lean` | `Multiparty.ObservationProfile Party X := Party → Observation X` (with pointwise `Pi` order instances), `toViewProfile` |
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
| `Process.lean` | `NodeAuthority`, `NodeView`, `NodeProfile`, `StepOver`, `ProcessOver`, `Process`, systems, `Functor (StepOver Γ)`, `Coalg` instance, `interleave`, `ProcessOver.{Behavior, behavior, ObsEq}` |
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
| `OpenTheory.lean` | `OpenTheory` algebra, `IsLawful`, `HasUnit`, `HasIdWire`, `IsMonoidal`, `IsTraced`, `IsCompactClosed`, `HasPlugWireFactor` |
| `OpenSyntax/Raw.lean` | `Raw` syntax tree, `Raw.interpret`, `Raw.Equiv` (incl. monoidal/traced/CC equations) |
| `OpenSyntax/Interp.lean` | `Interp` (tagless-final), granular `HasUnit` / `HasIdWire` / `IsMonoidal` / `IsTraced` / `IsCompactClosed` / `HasPlugWireFactor` instances |
| `OpenSyntax/Expr.lean` | `Expr` (quotient of `Raw`), granular `OpenTheory` lawfulness instances, `Expr.toInterp` |
| `OpenProcess.lean` | `BoundaryAction`, `OpenNodeProfile`, `OpenNodeContext` (with polynomial-product bridge `productView`), `OpenProcess m Party Δ` (monad-parametric, with intrinsic `stepSampler`), `toProcess`, `OpenProcessIso` (bisimulation equivalence) |
| `OpenProcessModel.lean` | `openTheory m Party schedulerSampler` (monad-parametric concrete model threading `Spec.Sampler` through `map`/`par`/`wire`/`plug`), `IsLawful`, monoidal/CC laws up to `OpenProcessIso` |
| `Emulates.lean` | `Emulates`, `UCSecure` (contextual emulation and UC security) |
| `Computational.lean` | `Semantics`, `CompEmulates`, `AsympCompEmulates` (computational observation layer) |
| `Runtime.lean` | `Spec.Sampler m`, `sampleTranscript`, `ProcessOver.runSteps`, `processSemantics` (no external `sampler` arg; pulled from `process.stepSampler`), `processSemanticsProbComp`, `processSemanticsOracle` (oracle-aware runtime) |
| `AsyncRuntime.lean` | asynchronous runtime variants for open processes |
| `AsyncSecurity.lean` | asynchronous security surfaces |
| `Notation.lean` | UC notation helpers |
| `StdDoBridge.lean` | bridge lemmas for `Std.Do`-style process code |
| `EnvAction.lean` / `EnvOpenProcess.lean` | environment actions and open-process wrappers |
| `CorruptionModel.lean` / `MomentaryCorruption.lean` | corruption modeling surfaces |
| `Leakage.lean` | leakage-oriented UC observation helpers |
| `MachineId.lean` / `Standard.lean` | machine identifiers and standard packaged interfaces |

## In-tree examples

- **`TwoParty/Examples.lean`**: `rfl` checks that `withRoles`/`Counterpart` types
  unfold correctly on a two-step spec.
- **`Multiparty/Examples.lean`**: Pattern-matching resolvers for broadcast,
  directed, and profile-based models; adversarial leakage and adaptive corruption.
- **`Concurrent/Examples.lean`**: Small concurrent specs with profiles, control,
  process execution, policies, and interleaving.
