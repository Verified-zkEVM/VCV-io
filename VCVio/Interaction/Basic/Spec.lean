/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-!
# Interaction specifications and transcripts

A `Spec` is a tree that describes the *shape* of a sequential interaction:
what types of moves can be exchanged at each round, and how later rounds
may depend on earlier moves. A `Transcript` records one complete play
through a `Spec` — a concrete move at every node from root to leaf.

On its own, a `Spec` says nothing about *who* makes each move or *how*
moves are computed. Those concerns are separated into companion modules:

* `Node` — realized node contexts and telescope-style node schemas
* `Decoration` — concrete per-node metadata on a fixed protocol tree
* `SyntaxOver` / `InteractionOver` — generic local syntax and local execution
  laws over realized node contexts
* `ShapeOver` — the functorial refinement of syntax, used when recursive
  continuations admit a generic map
* `Strategy` — one-player strategies with monadic effects
* `Append`, `Replicate`, `Chain` — sequential composition and iteration

This is the foundation of the entire `Interaction` layer, which replaces
the old flat `ProtocolSpec n` model with a dependent-type-native design.
The key advantage is that later rounds can depend on earlier moves, which
is mathematically forced in protocols like sumcheck and FRI.

## Module map

- `Basic/` — spec, node contexts, decoration, generic shapes, strategy,
  composition (this layer)
- `Concurrent/` — structural concurrent source syntax, frontiers and residuals,
  typed interfaces and directed open boundaries,
  operations-first open-composition theory and its first final-tagless free
  lawful model,
  structural frontier traces and true-concurrency refinements, dynamic
  `Process` / `Machine` / `Tree` frontends, generic process executions and
  policies, finite prefixes and infinite runs, observation extraction,
  refinement, bisimulation, packaged equivalence notions, fairness, liveness,
  per-party observation profiles,
  scheduler/control ownership, and current local frontier views
- `TwoParty/` — sender/receiver roles, `withRoles`, `Counterpart`
- `Reduction.lean` — prover, verifier, reduction
- `Oracle/` — oracle decoration, path-dependent oracle access
- `Security.lean` / `OracleSecurity.lean` — security definitions
- `Boundary/` — same-transcript interface adaptation
- `Multiparty/` — native multiparty local views and per-party profiles,
  including broadcast and directed communication models

## References

* Hancock–Setzer (2000), recursion over interaction interfaces
* Escardó–Oliva (2023, TCS 974), games as type trees
* McBride (2010); Dagand–McBride (2014), displayed algebras / ornaments
-/

universe u

namespace Interaction

/-- A `Spec` describes the shape of a sequential interaction as a tree.
Each internal node specifies a move space `Moves`, and the rest of the
protocol may depend on the chosen move `x : Moves`.

On its own, a `Spec` is intentionally minimal:
it records only the branching structure of the interaction.
It does **not** say
* who controls a node,
* what local data is attached to that node,
* what kind of participant object lives there, or
* how a collection of participants executes the node.

Those additional layers are supplied separately by:
* `Spec.Node.Context` / `Spec.Node.Schema`, for node-local semantic contexts
  and their telescope-style descriptions;
* `Spec.Decoration`, for concrete nodewise metadata;
* `Spec.SyntaxOver`, for the most general local participant syntax over
  realized node contexts;
* `Spec.ShapeOver`, for the functorial refinement of such syntax;
* `Spec.InteractionOver`, for local execution laws over such syntax. -/
inductive Spec : Type (u + 1) where
  | /-- Terminal node: the interaction is over. -/
    done : Spec
  | /-- A round of interaction: a value of type `Moves` is exchanged, then
    the protocol continues with `rest x` depending on the chosen move `x`. -/
    node (Moves : Type u) (rest : Moves → Spec) : Spec

namespace Spec

/-- A complete play through a `Spec`: at each node, a concrete move is
recorded, producing a root-to-leaf path through the interaction tree.
For `.done`, the transcript is trivial (`PUnit`); for `.node X rest`,
it is a chosen move `x : X` paired with a transcript for `rest x`. -/
def Transcript : Spec → Type u
  | .done => PUnit
  | .node X rest => (x : X) × Transcript (rest x)

/-- A straight-line `Spec` with no branching: each move type in the list
becomes one round, and later rounds do not depend on earlier moves. -/
def ofList : List (Type u) → Spec
  | [] => .done
  | T :: tl => .node T (fun _ => ofList tl)

end Spec
end Interaction
