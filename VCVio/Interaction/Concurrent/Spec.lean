/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Spec

/-!
# Concurrent interaction specifications

This file introduces the minimal concurrent source syntax for the
`Interaction` library.

The existing sequential `Interaction.Spec` is a continuation tree with one
currently enabled move family at each node. The concurrent extension keeps that
continuation-first shape and adds exactly one new constructor:

* `par left right` — both `left` and `right` are concurrently live.

The design is intentionally syntax-first and minimal.
This file does **not** yet define:

* the currently enabled frontier of a concurrent spec;
* scheduler or adversary execution;
* independence or true-concurrency refinements;
* dynamic spawning;
* or multiparty local observations of concurrent events.

Those layers live in later modules such as `Concurrent/Frontier` and
`Concurrent/Trace`.

The guiding idea is the same as in the sequential layer:
the "state" of a concurrent interaction is its current residual continuation,
not an external mutable store.
-/

universe u

namespace Interaction
namespace Concurrent

/--
A `Concurrent.Spec` describes the shape of a concurrent interaction as a
continuation tree with binary structural parallelism.

Constructors:

* `done` — no further behavior.
* `node Moves rest` — one currently enabled atomic move family, just as in the
  sequential `Interaction.Spec`.
* `par left right` — both `left` and `right` are concurrently live.

This is intentionally only a **source syntax** for concurrency.
It says that residual behavior can be built from sequential nodes and parallel
composition, but it does not yet commit to any particular execution semantics
or equivalence laws.
-/
inductive Spec : Type (u + 1) where
  | /-- Terminal concurrent interaction: no further events are enabled. -/
    done : Spec
  | /-- One atomic interaction node, exactly as in the sequential setting:
    a move `x : Moves` occurs, and the residual concurrent interaction is
    `rest x`. -/
    node (Moves : Type u) (rest : Moves → Spec) : Spec
  | /-- Parallel composition of two concurrently live residual interactions. -/
    par (left right : Spec) : Spec

namespace Spec

/--
`isLive S` decides whether the concurrent spec `S` still exposes any enabled
frontier event.

This is the structural liveness test for the concurrent source syntax:
* `done` is not live;
* an atomic `node` is live;
* a parallel spec is live iff either side is live.

Unlike syntactic equality with `.done`, this detects quiescent residuals such
as `.par .done .done`, which expose no frontier events even though they are not
literally the terminal constructor.
-/
def isLive : Concurrent.Spec → Bool
  | .done => false
  | .node _ _ => true
  | .par left right => left.isLive || right.isLive

/--
Embed a sequential `Interaction.Spec` into the concurrent syntax as the
one-thread fragment with no use of `par`.

This is the basic bridge from the existing sequential library to the new
concurrent source language.
-/
def ofSequential : Interaction.Spec → Concurrent.Spec
  | .done => .done
  | .node Moves rest => .node Moves (fun x => ofSequential (rest x))

@[simp, grind =]
theorem ofSequential_done : ofSequential Interaction.Spec.done = .done := rfl

@[simp, grind =]
theorem ofSequential_node (Moves : Type u) (rest : Moves → Interaction.Spec) :
    ofSequential (.node Moves rest) = .node Moves (fun x => ofSequential (rest x)) := rfl

@[simp, grind =]
theorem isLive_done : isLive .done = false := rfl

@[simp, grind =]
theorem isLive_node (Moves : Type u) (rest : Moves → Concurrent.Spec) :
    isLive (.node Moves rest) = true := rfl

@[simp, grind =]
theorem isLive_par (left right : Concurrent.Spec) :
    isLive (.par left right) = (left.isLive || right.isLive) := rfl

end Spec
end Concurrent
end Interaction
