/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.UC.EnvOpenProcess

/-!
# Corruption models as bundled environment alphabets

A **corruption model** is a named choice of "what corruption events
look like and how they update the bookkeeping state" — it picks the
event alphabet, the bookkeeping state schema, and the per-event
reaction. Different models capture different parts of the corruption
design space:

* **Static.** The adversary picks a fixed set of corrupted parties up
  front; the set is immutable thereafter.
* **Adaptive (persistent).** The adversary may corrupt parties at any
  time; once corrupted a party stays corrupted forever (the standard
  classical UC model).
* **Adaptive momentary** (Signal / CJSV22 §3.2). The adversary may
  corrupt parties at any time, *and* the environment may later
  `refresh` a party to revoke the compromise — this is what enables
  post-compromise security. The canonical model in
  `VCVio/Interaction/UC/MomentaryCorruption.lean` (the value
  `MomentaryCorruption.model`).
* **Threshold / mobile / leakage-resilient / …** All natural further
  models, each captured as its own `CorruptionModel` value when
  needed.

This file defines the framework's generic corruption-model bundle and
the bundled-process abbreviation `CorruptionModel.Process`. Concrete
models live alongside (one file each); the framework is intentionally
agnostic to which models exist.

## Why a structure bundle, not a typeclass

A model is a **named choice the user explicitly makes** at every
proof site (pick `MomentaryCorruption.model` here, pick
`StaticCorruption.model` there). It is not an implementation detail
we want resolved automatically by instance synthesis, so the right
shape is a first-class value. Being a value also means we can write
functions over models (lift one model to another, take products of
models) without the awkwardness of typeclass-level constructions.

## Three fields, no more

The bundle is intentionally minimal:

* `Event` — the alphabet of corruption events the model recognises;
* `State` — the bookkeeping state the model carries between events;
* `envAction` — the per-event reaction `EnvAction Event State`.

Things deliberately **not** in the bundle:

* **Leakage / observers.** Observation models (snapshot leak,
  interactive leakage queries, erasure-aware, structured/partial
  leak, passive) form their own design axis and are layered on top
  via separate typeclasses such as `SnapshotLeakable` (see
  `VCVio/Interaction/UC/Leakage.lean`).
* **Default policy.** Policies are constraints over event traces and
  are most useful in their own DSL (planned for a follow-up). A
  model may *recommend* a policy in its own namespace
  (e.g. `MomentaryCorruption.defaultPolicy`), but the bundle does
  not force one.
* **Decidable equality on `Event`.** Some downstream consumers want
  `DecidableEq Event` (policies that count distinct events); they
  declare `[DecidableEq M.Event]` at the proof site rather than
  forcing every model to provide it.

The bundle is the right API for "I want to write a process /
proof / lemma that is generic over the corruption model" — declare
`(M : CorruptionModel)` and use `M.Event`, `M.State`, `M.envAction`,
`M.Process Party Δ`.
-/

universe u v w

namespace Interaction
namespace UC

/--
A **corruption model** bundles an event alphabet, a bookkeeping state
schema, and a per-event reaction. Concrete models (`MomentaryCorruption`,
a future `StaticCorruption`, etc.) are values of this type.

The three fields are independent of any particular party identity:
`Event` and `State` may or may not be keyed by `MachineId`. A model
that is, exposes `MachineId`-keyed events through its own concrete
`Event` constructor (e.g.
`MomentaryCorruption.Alphabet.compromise (m : MachineId Sid Pid)`),
not through a parameter on `CorruptionModel`.
-/
structure CorruptionModel where
  /-- The event alphabet recognised by the model. -/
  Event : Type
  /-- The bookkeeping state carried between events. -/
  State : Type
  /-- The per-event reaction updating `State` on each `Event`. -/
  envAction : EnvAction Event State

namespace CorruptionModel

/--
The corruption-aware open process abbreviation for a fixed model.

Specialises `EnvOpenProcess` to the model's event alphabet and state,
fixing the env-channel slot to `M.envAction`'s `(Event, State)`. The
underlying open process is supplied by the user; the model determines
how environment events update the bookkeeping state.

The two `OpenProcess` universes `(v, w)` (process state and move
spaces) are exposed; `Party` is whatever the user pairs the model
with. For the canonical `MomentaryCorruption` instantiation, `Party`
will be `MachineId Sid Pid` and the model fixes
`Event := MomentaryCorruption.Alphabet Sid Pid`.
-/
abbrev Process (M : CorruptionModel) (Party : Type u) (Δ : PortBoundary) :=
  EnvOpenProcess.{u, 0, v, w} Party Δ M.Event M.State

end CorruptionModel

end UC
end Interaction
